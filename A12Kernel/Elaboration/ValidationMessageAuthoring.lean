import A12Kernel.Elaboration.ValidationRule

/-! # Checked authoring for bounded flat validation-message templates

A parameter's entity spec is the **shared path grammar** the condition parser uses, so this fragment
decodes the same separators and hands the result to the one existing field resolver rather than
carrying a second lookup: a leading `/` is absolute, each leading `..` crosses one enclosing group
with an optional explicit turning point after the last of them, and `/` separates the remaining group
names from the field. A field is therefore addressable by its bare name when that name is unique, by
a path relative to the rule group, or absolutely when it lies outside the rule context.

A name that collides with a terminal is written in the grammar's **single-quote** escape, and the
quotes are erased before any semantic lookup, so an unnecessary quote is transparent. This producer's
quoting requirement is deliberately **narrower** than the condition language's: a set of terminals is
historically accepted unquoted inside an entity name, and the caller supplies both lists from the
language version it supports.

What stays outside is the rest of the parameter grammar: every non-field parameter form, the semantic
index and category suffixes, and repeatable targets. Two of the Kernel's own `.value` gates are
unreachable in this fragment rather than modelled — a star reference needs a repeatable path, and a
declaration's "no value validation" flag has no representation here. The bounded-ASCII template gate
also refuses a name carrying one of the grammar's accented letters before the name rules see it.
-/

namespace A12Kernel

inductive ValidationMessageTemplateError where
  | emptyTemplate
  | lineSeparator
  | controlCharacter (character : Char)
  | unsupportedCharacter (character : Char)
  | oddDollarCount
  | invalidParameter (parameter : String)
  /-- A name colliding with a terminal was written without the grammar's quote escape. -/
  | unquotedTerminalName (name : String)
  | reference (parameter : String) (error : ResolveError)
  | fieldNotReferenced (parameter : String) (field : FieldId)
  deriving Repr, DecidableEq

private inductive ParsedValidationMessagePart where
  | text (value : String)
  /-- The authored spelling beside the path it decoded to. Both travel, because the spelling is what
  a diagnostic and an Explain consumer quote while the path is what resolves. -/
  | fieldName (parameter : String) (reference : AuthoredFieldPath)
  | fieldValue (parameter : String) (reference : AuthoredFieldPath)

private def isLineSeparator (character : Char) : Bool :=
  character == '\n' || character == '\r' ||
    character.toNat == 0x2028 || character.toNat == 0x2029

private def isControlCharacter (character : Char) : Bool :=
  character.toNat < 0x20 || character.toNat == 0x7f

private def isBoundedAscii (character : Char) : Bool :=
  character.toNat ≤ 0x7e

private def isBareNameCharacter (character : Char) : Bool :=
  ('a' ≤ character && character ≤ 'z') ||
    ('A' ≤ character && character ≤ 'Z') ||
    ('0' ≤ character && character ≤ '9') ||
    character == '_' || character == ':'

private def isBareName (name : String) : Bool :=
  !name.isEmpty && name.toList.all isBareNameCharacter

/-- The quoting rule for a rule-message parameter. A name colliding with one of the selected
language's terminals must be quoted, **except** for the terminals this producer has historically
accepted unquoted inside an entity name. The exemption belongs to this producer rather than to the
path grammar, which is why it does not live on `PathKeywordProfile`. -/
structure ValidationMessageKeywordProfile where
  path : PathKeywordProfile
  unquotedTerminals : List String := []
  deriving Repr, DecidableEq

/-- Treat an exempt terminal as if the author had quoted it, then reuse the one existing
quote-provenance lowering. The exemption says exactly "no quote is needed here", so recording it as
quoted expresses that decision in the shared type instead of duplicating the lowering walk. -/
private def exemptQuoting (profile : ValidationMessageKeywordProfile)
    (name : AuthoredPathName) : AuthoredPathName :=
  if profile.unquotedTerminals.contains name.text then
    { name with quoted := true }
  else
    name

/-- Decode one authored segment's quote syntax into the shared name-with-provenance type. -/
private def decodeSegment (segment : String) : Option AuthoredPathName :=
  match segment.toList with
  | '\'' :: rest =>
      match rest.reverse with
      | '\'' :: inner =>
          let text := String.mk inner.reverse
          if isBareName text then some { text, quoted := true } else none
      | _ => none
  | _ => if isBareName segment then some { text := segment } else none

/-- Decode a list of authored segments, failing as a whole if any segment is malformed. -/
private def decodeSegments : List String → Option (List AuthoredPathName)
  | [] => some []
  | segment :: rest => do
      let name ← decodeSegment segment
      pure (name :: (← decodeSegments rest))

/-- Split the up-run off a relative spec, returning the parent count, the optional turning point, and
the remaining segments. A name attached directly to a `..` is the turning point, so it ends the run;
one written after a `/` is an ordinary path element. -/
private def splitParentWalk :
    Nat → List String → Nat × Option String × List String
  | parents, ".." :: rest => splitParentWalk (parents + 1) rest
  | parents, segment :: rest =>
      if segment.startsWith ".." then
        (parents + 1, some (segment.drop 2).toString, rest)
      else
        (parents, none, segment :: rest)
  | parents, [] => (parents, none, [])

/-- Decode one parameter's entity spec into the shared structured path. Failure is the Kernel's own
single parse class rather than a family of shape classes, because that is what the parameter parser
reports for every malformed spec. -/
private def parseMessagePath (spec : String) :
    Except ValidationMessageTemplateError AuthoredFieldPath :=
  let segments := spec.splitOn "/"
  let malformed := Except.error (ValidationMessageTemplateError.invalidParameter spec)
  match segments with
  | [] => malformed
  | first :: rest =>
      if first.isEmpty then
        -- A leading separator is the absolute form, which needs at least one group and a field.
        match rest.reverse with
        | field :: group :: groups =>
            match decodeSegments (field :: group :: groups) with
            | some (field :: groups) =>
                .ok { base := .absolute, groups := groups.reverse, field }
            | _ => malformed
        | _ => malformed
      else
        let (parents, turningPoint, remaining) := splitParentWalk 0 segments
        match remaining.reverse, turningPoint with
        | field :: groups, none =>
            match decodeSegments (field :: groups) with
            | some (field :: groups) =>
                .ok { base := .relative parents, groups := groups.reverse, field }
            | _ => malformed
        | field :: groups, some turningPoint =>
            match decodeSegments (field :: groups), decodeSegment turningPoint with
            | some (field :: groups), some turningPoint =>
                .ok { base := .relative parents, turningPoint := some turningPoint
                      groups := groups.reverse, field }
            | _, _ => malformed
        | [], _ => malformed

/-- Strip the value suffix, then decode the remaining entity spec as a path. The suffix is taken at
the end of the whole spec, which is this fragment's committed reading of a grammar that also lets a
trailing reserved word belong to the name itself. -/
private def parseParameter (parameter : String) :
    Except ValidationMessageTemplateError ParsedValidationMessagePart :=
  match parameter.splitOn ".value" with
  | [spec, ""] => .fieldValue parameter <$> parseMessagePath spec
  | [spec] => .fieldName parameter <$> parseMessagePath spec
  | _ => .error (.invalidParameter parameter)

private def textPart (value : String) : List ParsedValidationMessagePart :=
  if value.isEmpty then [] else [.text value]

private def parseSegments :
    List String →
      Except ValidationMessageTemplateError (List ParsedValidationMessagePart)
  | [] => .ok []
  | [text] => .ok (textPart text)
  | text :: parameter :: rest => do
      let parameterPart ←
        if parameter.isEmpty then
          pure (.text "$")
        else
          parseParameter parameter
      pure (textPart text ++ [parameterPart] ++ (← parseSegments rest))

private def validateMessageTemplateSource (source : String) :
    Except ValidationMessageTemplateError (List String) := do
  if source.isEmpty then throw .emptyTemplate
  match source.toList.find? isLineSeparator with
  | some _ => throw .lineSeparator
  | none => pure ()
  match source.toList.find? isControlCharacter with
  | some character => throw (.controlCharacter character)
  | none => pure ()
  match source.toList.find? (fun character => !isBoundedAscii character) with
  | some character => throw (.unsupportedCharacter character)
  | none => pure ()
  if source.toList.count '$' % 2 != 0 then throw .oddDollarCount
  pure (source.splitOn "$")

private def parseValidationMessageTemplate (source : String) :
    Except ValidationMessageTemplateError (List ParsedValidationMessagePart) := do
  parseSegments (← validateMessageTemplateSource source)

/-- One checked field reference of a message parameter. `parameter` retains the authored spelling for
Explain, including any value suffix; `reference` is its decoded path, which is what resolved. -/
structure CheckedValidationMessageReference
    (model : FlatModel) (condition : CheckedFlatCondition model) where
  parameter : String
  reference : SurfaceFieldPath
  declaration : FlatFieldDecl
  resolved :
    model.resolveNonrepeatableFieldUnchecked condition.rowGroup reference =
      .ok declaration
  conditionReferenced :
    condition.core.referencesField declaration.id = true

inductive CheckedValidationMessagePart
    (model : FlatModel) (condition : CheckedFlatCondition model) where
  | text (value : String)
  | fieldName (reference : CheckedValidationMessageReference model condition)
  | fieldValue (reference : CheckedValidationMessageReference model condition)

structure CheckedValidationMessageTemplate
    (model : FlatModel) (condition : CheckedFlatCondition model) where
  source : String
  parts : List (CheckedValidationMessagePart model condition)

private def resolveMessageReference (model : FlatModel)
    (profile : ValidationMessageKeywordProfile)
    (condition : CheckedFlatCondition model)
    (parameter : String) (authored : AuthoredFieldPath) :
    Except ValidationMessageTemplateError
      (CheckedValidationMessageReference model condition) := do
  -- Every name-bearing position is checked, because a terminal may sit at any path level.
  let reference ← match ({ authored with
      turningPoint := authored.turningPoint.map (exemptQuoting profile)
      groups := authored.groups.map (exemptQuoting profile)
      field := exemptQuoting profile authored.field
    } : AuthoredFieldPath).lower profile.path with
    | .ok reference => pure reference
    | .error (.unquotedKeyword name) => throw (.unquotedTerminalName name)
  match hResolved :
      model.resolveNonrepeatableFieldUnchecked condition.rowGroup reference with
  | .error error => throw (.reference parameter error)
  | .ok declaration =>
      if hReferenced :
          condition.core.referencesField declaration.id = true then
        pure {
          parameter
          reference
          declaration
          resolved := hResolved
          conditionReferenced := hReferenced
        }
      else
        throw (.fieldNotReferenced parameter declaration.id)

private def checkMessageParts (model : FlatModel)
    (profile : ValidationMessageKeywordProfile)
    (condition : CheckedFlatCondition model) :
    List ParsedValidationMessagePart →
      Except ValidationMessageTemplateError
        (List (CheckedValidationMessagePart model condition))
  | [] => .ok []
  | .text value :: rest => do
      pure (.text value :: (← checkMessageParts model profile condition rest))
  | .fieldName parameter reference :: rest => do
      pure (.fieldName
        (← resolveMessageReference model profile condition parameter reference) ::
        (← checkMessageParts model profile condition rest))
  | .fieldValue parameter reference :: rest => do
      pure (.fieldValue
        (← resolveMessageReference model profile condition parameter reference) ::
        (← checkMessageParts model profile condition rest))

def elaborateValidationMessageTemplate (model : FlatModel)
    (profile : ValidationMessageKeywordProfile)
    (condition : CheckedFlatCondition model) (source : String) :
    Except ValidationMessageTemplateError
      (CheckedValidationMessageTemplate model condition) := do
  let parsed ← parseValidationMessageTemplate source
  pure { source, parts := ← checkMessageParts model profile condition parsed }

structure ValidationMessageInputs where
  fieldName : FieldId → MessageNameInput
  fieldValue : FieldId → MessageValueInput

def CheckedValidationMessagePart.toRenderPart
    (inputs : ValidationMessageInputs) :
    CheckedValidationMessagePart model condition → MessageRenderPart
  | .text value => .text value
  | .fieldName reference => .fieldName (inputs.fieldName reference.declaration.id)
  | .fieldValue reference => .fieldValue (inputs.fieldValue reference.declaration.id)

def CheckedValidationMessageTemplate.toRenderPlan
    (template : CheckedValidationMessageTemplate model condition)
    (inputs : ValidationMessageInputs) : MessageRenderPlan :=
  { parts := template.parts.map (·.toRenderPart inputs) }

/-- One checked part of the measured en_US String-pattern field-message grammar. The fixed tokens refer to the owning field, never to a rule-relative path. -/
inductive CheckedEnUsStringPatternMessagePart where
  | text (value : String)
  | fieldName
  | fieldValue
  deriving Repr, DecidableEq

/-- A checked en_US String-pattern error-text template. Requiredness and every other field-message producer remain distinct and unsupported. -/
structure CheckedEnUsStringPatternMessageTemplate where
  source : String
  parts : List CheckedEnUsStringPatternMessagePart
  deriving Repr, DecidableEq

private def stringPatternTextPart (value : String) :
    List CheckedEnUsStringPatternMessagePart :=
  if value.isEmpty then [] else [.text value]

private def parseEnUsStringPatternParameter (parameter : String) :
    Except ValidationMessageTemplateError CheckedEnUsStringPatternMessagePart :=
  match parameter with
  | "field" => .ok .fieldName
  | "field.value" => .ok .fieldValue
  | _ => .error (.invalidParameter parameter)

private def parseEnUsStringPatternSegments :
    List String →
      Except ValidationMessageTemplateError
        (List CheckedEnUsStringPatternMessagePart)
  | [] => .ok []
  | [text] => .ok (stringPatternTextPart text)
  | text :: parameter :: rest => do
      let parameterPart ← parseEnUsStringPatternParameter parameter
      pure (stringPatternTextPart text ++ [parameterPart] ++
        (← parseEnUsStringPatternSegments rest))

/-- Check the bounded English String-pattern producer. Its empty dollar-pair parameter is invalid rather than a literal-dollar escape. -/
def elaborateEnUsStringPatternMessageTemplate (source : String) :
    Except ValidationMessageTemplateError
      CheckedEnUsStringPatternMessageTemplate := do
  let segments ← validateMessageTemplateSource source
  pure { source, parts := ← parseEnUsStringPatternSegments segments }

/-- Exact replacement bytes selected by the caller for the owning field. Provider invocation and empty-value fallback precede this boundary and remain outside the supported fragment. -/
structure StringPatternMessageInputs where
  fieldName : String
  fieldValue : String
  deriving Repr, DecidableEq

def CheckedEnUsStringPatternMessagePart.toRenderPart
    (inputs : StringPatternMessageInputs) :
    CheckedEnUsStringPatternMessagePart → MessageRenderPart
  | .text value => .text value
  | .fieldName => .text inputs.fieldName
  | .fieldValue => .text inputs.fieldValue

def CheckedEnUsStringPatternMessageTemplate.toRenderPlan
    (template : CheckedEnUsStringPatternMessageTemplate)
    (inputs : StringPatternMessageInputs) : MessageRenderPlan :=
  { parts := template.parts.map (·.toRenderPart inputs) }

/-- The resolved text attached to an already-established String-pattern failure. Rendering cannot replace or reclassify the underlying formal error. -/
structure RenderedStringPatternError where
  error : StringFieldError
  text : ResolvedMessageText
  deriving Repr, DecidableEq

def CheckedEnUsStringPatternMessageTemplate.renderError
    (template : CheckedEnUsStringPatternMessageTemplate)
    (inputs : StringPatternMessageInputs) : RenderedStringPatternError where
  error := .pattern
  text := (template.toRenderPlan inputs).render

end A12Kernel
