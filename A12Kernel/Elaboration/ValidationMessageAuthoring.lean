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

A field reference may carry an Enumeration **category** suffix, `->Name`, whose three gates are the
Kernel's own: a missing name, a field that is not an Enumeration, and a name that is not one of that
declaration's categories. It carries neither of the value suffix's extra gates, and combining it with the value suffix is a parse failure — the two really are alternatives. A **doubled** arrow is refused
only after the first category's kind and membership gates pass. Its diagnostic therefore depends on
that first name: an undeclared category or a non-Enumeration field stops at its own gate, while a
declared category reaches the trailing-syntax refusal. What a category access **renders** is measured: the category
token the field's current stored value maps to, so the checked part carries the declaration's own
mapping and the caller supplies only the stored token. An absent stored token renders as the empty
string, which is measured; a token the category does not map cannot arise, because a declaration's
categories align one-to-one with its values.

A field reference may finally carry a **semantic-index key**, `For "k"` or `For SomeField`, after any
value or category suffix — that order is the grammar's, not a preference. Its gate is on the
**semantic index**, not on the field: the condition must use that same index the same way, and the
keyed field itself need not be a condition operand at all. Measured, a keyed parameter naming a field
the condition never mentions is admitted when the condition keys that group by that key, while the
unkeyed spelling of the same field is refused — so condition membership belongs to the unkeyed form
alone. The pairing is exact in the other direction too: a keyed condition operand does not license an
unkeyed parameter.

A semantic index needs a repeatable group, and this fragment's model is nonrepeatable, so a keyed
parameter is decoded and then refused as outside the fragment. The refusal is deliberately *not*
mapped to the Kernel's pairing class, because the Kernel's gate is a question this condition spine
cannot pose; the grammar in front of it — well-formedness, suffix order, key spelling, nesting — is
measured and modeled exactly.

A parameter written `$#...$` occupies the **group position**, which is a different position from the
name one and resolves the same words differently: bare `$RootGroup$` is an entity lookup and refused,
while `$#RootGroup$` is admitted. Its argument is an absolute group path or one of the two keyword
shorthands for the endpoints of the rule's ancestor chain, and the admitted set is the rule's own group
together with its ancestors — so containment runs the **opposite** way from the computation
declaring-group gate: the *named* group must contain the rule's group. A relative spelling is refused
even when it names a real group. An absolute path resolves in two stages the Kernel reports apart, an
undeclared root ahead of containment, and its segments take the same quote escape as a name — but
because the keyword match is on the raw argument, quoting a terminal turns it back into an ordinary
group name. Two historic terminals keep their own refusal class, which the Kernel reports distinctly
rather than as an unknown group, and quoting removes that reading too.

One **non-field** parameter form is admitted: the Base Year terminal with an optional signed offset.
Its only static gate is that the model declares a Base Year, and the offset is applied at authoring
because nothing about it depends on the document.

What stays outside is the rest of the parameter grammar: the remaining non-field forms, the semantic
index suffix, and repeatable targets. Two of the Kernel's own `.value` gates are
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
  /-- A category suffix was written with no category name after the arrow. -/
  | missingCategoryName (parameter : String)
  /-- A category suffix was applied to a field that is not an Enumeration declaration. -/
  | categoryFieldNotEnumeration (parameter : String) (field : FieldId)
  /-- The named category is not one this Enumeration declaration declares, or the declaration itself
  is ill-formed. Both arrive through the one existing Enumeration projection gate. -/
  | category (parameter : String) (error : EnumerationOperandError)
  /-- A group-position argument whose root is declared but which the rule's group does not lie under,
  or which is not an absolute path at all. A declared descendant, a sibling, an unknown group below a
  declared root, and every relative spelling share this one refusal, which is the Kernel's own
  grouping — an **unknown root** is separated onto `unknownRootGroup` instead. -/
  | invalidGroupParameter (parameter : String)
  /-- The first segment of an absolute group argument names no declared root group. Root existence is
  a gate of its own, ahead of containment and reported apart from it, so it fires whatever follows the
  root and regardless of whether the rest could ever have contained the rule.

  A root the model declares but leaves **empty** would be reported by the Kernel on the ordinary group
  class instead. `FlatModel` cannot express such a group, so no input reaching here separates the two;
  `FlatModel.hasGroupPath` owns that limit. -/
  | unknownRootGroup (parameter root : String)
  /-- A historic group terminal the Kernel still recognizes and refuses on the modern route. It stays
  distinct from `invalidGroupParameter` because the Kernel's own code is distinct. -/
  | retiredGroupTerminal (parameter terminal : String)
  /-- A Base Year parameter was authored against a model that declares none. -/
  | noBaseYear
  /-- A semantic-index key is itself keyed. -/
  | nestedSemanticIndex (parameter : String)
  /-- A **well-formed** keyed parameter, refused because this fragment's model is nonrepeatable and so
  declares no semantic index for the key to name. This is the fragment's own boundary, not the
  Kernel's pairing class: the Kernel gates a keyed parameter on whether the **condition uses that same
  semantic index**, which is a question a flat condition spine cannot pose. -/
  | semanticIndexUnsupported (parameter : String)
  deriving Repr, DecidableEq

/-- Which suffix a keyed field reference carries. The grammar puts the suffix **before** the key, so
a keyed parameter is one shape with three suffix cases rather than three keyed shapes. -/
inductive MessageParameterSuffix where
  | none
  | value
  | category (name : String)
  deriving Repr, DecidableEq

/-- A group-position argument as the author spelled it. The two keyword shorthands stay distinct from
a path, because what they denote is decided against the rule's group rather than at parsing. -/
inductive AuthoredMessageGroup where
  | ruleGroup
  | rootGroup
  | absolute (path : GroupPath)
  deriving Repr, DecidableEq

/-- A key as the author spelled it: a decoded quoted literal, or a path to the keying field. -/
inductive AuthoredMessageKey where
  | literal (token : String)
  | field (reference : AuthoredFieldPath)
  deriving Repr, DecidableEq

private inductive ParsedValidationMessagePart where
  | text (value : String)
  /-- The authored spelling beside the path it decoded to. Both travel, because the spelling is what
  a diagnostic and an Explain consumer quote while the path is what resolves. -/
  | fieldName (parameter : String) (reference : AuthoredFieldPath)
  | fieldValue (parameter : String) (reference : AuthoredFieldPath)
  | fieldCategory (parameter : String) (reference : AuthoredFieldPath)
      (category : String)
  /-- A doubled category arrow. The first category is checked before the remaining syntax is refused,
  so this stays distinct from an undifferentiated parse failure. -/
  | fieldCategoryWithTrailingSyntax (parameter : String)
      (reference : AuthoredFieldPath) (category : String)
  | baseYear (offset : Int)
  /-- A group-position argument, beside the authored spelling a diagnostic quotes. -/
  | group (parameter : String) (authored : AuthoredMessageGroup)
  /-- Any field form above, keyed. The suffix travels so one arm serves all three. -/
  | keyed (parameter : String) (reference : AuthoredFieldPath)
      (suffix : MessageParameterSuffix) (key : AuthoredMessageKey)

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
  /-- The selected language's spelling of the Base Year parameter terminal. It is data because the
  parameter grammar is bilingual and this project does not choose a language for the author. -/
  baseYearTerminal : String
  /-- The selected language's spelling of the semantic-index key terminal. -/
  forTerminal : String
  /-- The selected language's spelling of the group position's root shorthand. -/
  rootGroupTerminal : String
  /-- The selected language's spelling of the group position's own-group shorthand. -/
  ruleGroupTerminal : String
  /-- The historic group terminals the Kernel recognizes in the group position and refuses on the
  modern route. Measured under the English condition language the set is `Zeile` and `Usb`; whether it
  is selected by language at all is unmeasured, so the caller supplies it like the other terminals. -/
  retiredGroupTerminals : List String := []
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
          let text := String.ofList inner.reverse
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
private def parseMessagePath (parameter spec : String) :
    Except ValidationMessageTemplateError AuthoredFieldPath :=
  -- The refusal quotes the whole authored parameter rather than the spec it was split from, because
  -- a diagnostic naming a fragment the author never wrote sends them looking in the wrong place.
  let segments := spec.splitOn "/"
  let malformed :=
    Except.error (ValidationMessageTemplateError.invalidParameter parameter)
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

/-- Decode the optional signed offset of a Base Year parameter. An absent offset is zero, which is
the same parameter with no calculation rather than a distinguished shape. -/
private def parseBaseYearOffset (remainder : String) : Option Int :=
  if remainder.isEmpty then
    some 0
  else
    match remainder.toList with
    | sign :: digits =>
        if digits.isEmpty || !digits.all Char.isDigit then none
        else
          let magnitude := (String.ofList digits).toNat!
          match sign with
          | '+' => some (Int.ofNat magnitude)
          | '-' => some (-Int.ofNat magnitude)
          | _ => none
    | [] => none

/-- Decode one group-position argument, with the `#` already stripped. A live keyword is taken before
the path grammar, a retired terminal keeps its own refusal, and every other spelling must be an
absolute group path: a relative one is refused even when it names a real group, so the leading
separator is required rather than conventional. Each segment takes the name grammar's single-quote
escape and the quotes are erased before lookup, so quoting reaches the same group — but the keyword
match above is on the **raw** argument, which is why quoting a terminal turns it back into an ordinary
group name. A malformed spelling is a parse failure rather than a group refusal; the Kernel separates
three lexical codes for these shapes, which this fragment reports as its one parse class. -/
private def parseMessageGroup (profile : ValidationMessageKeywordProfile)
    (parameter argument : String) :
    Except ValidationMessageTemplateError AuthoredMessageGroup :=
  if argument == profile.ruleGroupTerminal then
    .ok .ruleGroup
  else if argument == profile.rootGroupTerminal then
    .ok .rootGroup
  else if profile.retiredGroupTerminals.contains argument then
    .error (.retiredGroupTerminal parameter argument)
  else
    match argument.splitOn "/" with
    | "" :: first :: rest =>
        match decodeSegments (first :: rest) with
        | some names => .ok (.absolute (names.map (·.text)))
        | none => .error (.invalidParameter parameter)
    | _ => .error (.invalidGroupParameter parameter)

/-- Decode a key's own spelling. A literal is the grammar's double-quoted token with `""` as its
escape; anything else is a path to the keying field, and an unquoted bare word therefore resolves as a
field rather than as a token. -/
private def parseMessageKey (parameter key : String) :
    Except ValidationMessageTemplateError AuthoredMessageKey :=
  if key.startsWith "\"" && key.endsWith "\"" && key.length ≥ 2 then
    .ok (.literal
      (((key.drop 1).dropEnd 1).toString.replace "\"\"" "\""))
  else
    .field <$> parseMessagePath parameter key

/-- Split the trailing key off a parameter, then decode the remaining spec's own suffix. The key
separator is the selected language's `For` terminal surrounded by spaces, which is the canonical
authored spelling; this fragment does not accept the grammar's whitespace-free forms. -/
private def splitMessageKey (profile : ValidationMessageKeywordProfile)
    (parameter : String) : String × Option String :=
  match parameter.splitOn s!" {profile.forTerminal} " with
  | [spec] => (spec, none)
  | spec :: rest => (spec, some (String.intercalate s!" {profile.forTerminal} " rest))
  | [] => (parameter, none)

/-- Strip the value suffix, then decode the remaining entity spec as a path. The suffix is taken at
the end of the whole spec, which is this fragment's committed reading of a grammar that also lets a
trailing reserved word belong to the name itself. -/
private def parseParameter (profile : ValidationMessageKeywordProfile)
    (parameter : String) :
    Except ValidationMessageTemplateError ParsedValidationMessagePart :=
  -- The position marker is read first, because it selects a different grammar rather than a different
  -- form inside the name grammar. Nothing in the name grammar can begin with it.
  if parameter.startsWith "#" then
    (ParsedValidationMessagePart.group parameter ·) <$>
      parseMessageGroup profile parameter (parameter.drop 1).toString
  else
  -- The Base Year terminal is checked first: it is a terminal, so an unquoted occurrence is never a
  -- field name, and its offset syntax is not part of any path.
  match splitMessageKey profile parameter with
  | (spec, some keyText) =>
      if (splitMessageKey profile keyText).2.isSome then
        .error (.nestedSemanticIndex parameter)
      else do
        let key ← parseMessageKey parameter keyText
        -- The suffix sits before the key, so the spec is re-split by the ordinary rules.
        match spec.splitOn "->" with
        | [inner, category] =>
            if category.isEmpty then throw (.missingCategoryName parameter)
            else
              pure (.keyed parameter (← parseMessagePath parameter inner)
                (.category category) key)
        | [_] =>
            match spec.splitOn ".value" with
            | [inner, ""] =>
                pure (.keyed parameter (← parseMessagePath parameter inner) .value
                  key)
            | [inner] =>
                pure (.keyed parameter (← parseMessagePath parameter inner) .none
                  key)
            | _ => throw (.invalidParameter parameter)
        | _ => throw (.invalidParameter parameter)
  | (_, none) =>
  if parameter.startsWith profile.baseYearTerminal then
    match parseBaseYearOffset
        ((parameter.drop profile.baseYearTerminal.length).toString) with
    | some offset => .ok (.baseYear offset)
    | none => .error (.invalidParameter parameter)
  else
  -- The two suffixes are alternatives in the grammar, and the arrow cannot occur inside a name, so
  -- splitting on it first is unambiguous. A doubled arrow retains its first category so the semantic
  -- gates can decide before the trailing syntax is refused.

  match parameter.splitOn "->" with
  | [spec, category] =>
      if category.isEmpty then .error (.missingCategoryName parameter)
      else (.fieldCategory parameter · category) <$> parseMessagePath parameter spec
  | spec :: category :: _ =>
      if category.isEmpty then .error (.missingCategoryName parameter)
      else (.fieldCategoryWithTrailingSyntax parameter · category) <$>
        parseMessagePath parameter spec
  | [_] =>
      match parameter.splitOn ".value" with
      | [spec, ""] => .fieldValue parameter <$> parseMessagePath parameter spec
      | [spec] => .fieldName parameter <$> parseMessagePath parameter spec
      | _ => .error (.invalidParameter parameter)
  | _ => .error (.invalidParameter parameter)

private def textPart (value : String) : List ParsedValidationMessagePart :=
  if value.isEmpty then [] else [.text value]

private def parseSegments (profile : ValidationMessageKeywordProfile) :
    List String →
      Except ValidationMessageTemplateError (List ParsedValidationMessagePart)
  | [] => .ok []
  | [text] => .ok (textPart text)
  | text :: parameter :: rest => do
      let parameterPart ←
        if parameter.isEmpty then
          pure (.text "$")
        else
          parseParameter profile parameter
      pure (textPart text ++ [parameterPart] ++ (← parseSegments profile rest))

/-- The lexical gate **both** message producers share: a nonempty printable-ASCII source with no line
separator or control character and balanced dollar delimiters, split into alternating text and
parameter segments. Only the parameter grammar differs between producers, so this stays one gate. -/
def validateMessageTemplateSource (source : String) :
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

private def parseValidationMessageTemplate
    (profile : ValidationMessageKeywordProfile) (source : String) :
    Except ValidationMessageTemplateError (List ParsedValidationMessagePart) := do
  parseSegments profile (← validateMessageTemplateSource source)

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

/-- One checked category access: the field reference beside the resolved projection, with witnesses
that the projection belongs to *that* field's own Enumeration declaration and selects *that* category.
Together with the projection's own check this is the complete gate. -/
structure CheckedValidationMessageCategory
    (model : FlatModel) (condition : CheckedFlatCondition model) where
  reference : CheckedValidationMessageReference model condition
  category : String
  projection : CheckedEnumerationProjection
  enumerationOwned :
    reference.declaration.enumeration = some projection.declaration.declaration
  categorySelected : projection.projectionRef = .category category

/-- One admitted group-position parameter: the group the author named, beside the witnesses that it is
a representable path and that it **contains** the rule's group. Containment runs opposite to the
computation declaring-group gate, where the declaring group is the one that must contain the target. -/
structure CheckedValidationMessageGroup
    (model : FlatModel) (condition : CheckedFlatCondition model) where
  parameter : String
  group : GroupPath
  valid : GroupPath.isValid group = true
  containsRuleGroup : GroupPath.isPrefixOf group condition.rowGroup = true

/-- Admit one resolved group under the two gates every argument shares: it is a representable path,
and it **contains** the rule's group. Below the root gate, containment needs no separate existence
test, because every ancestor of a declared group is itself declared — so a group passing containment
is declared, and one failing it is refused whether or not the model declares it, which is what a
**declared** descendant and an unknown group below a declared root sharing one refusal already says. -/
def admitMessageGroup {model : FlatModel}
    (condition : CheckedFlatCondition model) (parameter : String)
    (group : GroupPath) :
    Except ValidationMessageTemplateError
      (CheckedValidationMessageGroup model condition) :=
  if hValid : GroupPath.isValid group = true then
    if hContains : GroupPath.isPrefixOf group condition.rowGroup = true then
      .ok { parameter, group, valid := hValid, containsRuleGroup := hContains }
    else
      .error (.invalidGroupParameter parameter)
  else
    .error (.invalidGroupParameter parameter)

/-- Resolve one group-position argument against the rule's own group. An absolute path resolves in the
two stages the Kernel reports apart: its first segment must name a declared root group, and only then
does containment decide. The root gate belongs to the path form alone — a keyword resolves to a group
derived from the rule's own, which introduces no root the model might not declare. -/
def checkMessageGroup {model : FlatModel} (condition : CheckedFlatCondition model)
    (parameter : String) (authored : AuthoredMessageGroup) :
    Except ValidationMessageTemplateError
      (CheckedValidationMessageGroup model condition) :=
  match authored with
  -- The root shorthand is the top of the *rule's own* ancestor chain rather than a model-wide root.
  -- A model with two roots separates the two readings, and the rule's own chain is what the Kernel
  -- admits: under the second root the shorthand is accepted while the first root is refused.
  | .ruleGroup => admitMessageGroup condition parameter condition.rowGroup
  | .rootGroup => admitMessageGroup condition parameter (condition.rowGroup.take 1)
  | .absolute [] => .error (.invalidGroupParameter parameter)
  | .absolute (root :: rest) =>
      if model.hasGroupPath [root] then
        admitMessageGroup condition parameter (root :: rest)
      else
        .error (.unknownRootGroup parameter root)

inductive CheckedValidationMessagePart
    (model : FlatModel) (condition : CheckedFlatCondition model) where
  | text (value : String)
  | fieldName (reference : CheckedValidationMessageReference model condition)
  | fieldValue (reference : CheckedValidationMessageReference model condition)
  | fieldCategory (access : CheckedValidationMessageCategory model condition)
  /-- The Base Year with its authored offset already applied, beside the witnesses that the model
  declares that year and that the arithmetic is the authored one. -/
  | baseYear (offset year : Int)
      (declared : model.baseYear = some (year - offset))
  | group (access : CheckedValidationMessageGroup model condition)

structure CheckedValidationMessageTemplate
    (model : FlatModel) (condition : CheckedFlatCondition model) where
  source : String
  parts : List (CheckedValidationMessagePart model condition)

/-- One resolved name-bearing parameter position, carrying its resolution witness but **no**
membership requirement. -/
private structure ResolvedMessageEntity
    (model : FlatModel) (condition : CheckedFlatCondition model) where
  reference : SurfaceFieldPath
  declaration : FlatFieldDecl
  resolved :
    model.resolveNonrepeatableFieldUnchecked condition.rowGroup reference =
      .ok declaration

/-- Resolve one name-bearing parameter position to a declaration. This is the part a keyed parameter
shares with an unkeyed one: measured, an unresolvable name is refused for both, while only the unkeyed
form additionally requires the condition to name the field. -/
private def resolveMessageEntity (model : FlatModel)
    (profile : ValidationMessageKeywordProfile)
    (condition : CheckedFlatCondition model)
    (parameter : String) (authored : AuthoredFieldPath) :
    Except ValidationMessageTemplateError
      (ResolvedMessageEntity model condition) := do
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
  | .ok declaration => pure { reference, declaration, resolved := hResolved }

private def resolveMessageReference (model : FlatModel)
    (profile : ValidationMessageKeywordProfile)
    (condition : CheckedFlatCondition model)
    (parameter : String) (authored : AuthoredFieldPath) :
    Except ValidationMessageTemplateError
      (CheckedValidationMessageReference model condition) := do
  let entity ← resolveMessageEntity model profile condition parameter authored
  if hReferenced :
      condition.core.referencesField entity.declaration.id = true then
    pure {
      parameter
      reference := entity.reference
      declaration := entity.declaration
      resolved := entity.resolved
      conditionReferenced := hReferenced
    }
  else
    throw (.fieldNotReferenced parameter entity.declaration.id)

/-- Apply the category suffix's three gates in the Kernel's own order to an already-resolved field
reference. The missing-name gate belongs to parsing, so only the kind and the declared-category gates
remain here, and both reuse the one existing Enumeration projection boundary. -/
private def resolveMessageCategory
    (reference : CheckedValidationMessageReference model condition)
    (parameter category : String) :
    Except ValidationMessageTemplateError
      (CheckedValidationMessageCategory model condition) :=
  match hSource : reference.declaration.enumeration with
  | none =>
      throw (.categoryFieldNotEnumeration parameter reference.declaration.id)
  | some source =>
      match elaborateEnumeration source with
      | .error _ =>
          throw (.category parameter (.unknownCategory category))
      | .ok checked =>
          match checkEnumerationProjection checked (.category category) with
          | .error error => throw (.category parameter error)
          | .ok projection =>
              if hOwned : source = projection.declaration.declaration ∧
                  projection.projectionRef =
                    EnumerationProjectionRef.category category then
                .ok {
                  reference, category, projection
                  enumerationOwned := by rw [hSource, hOwned.1]
                  categorySelected := hOwned.2 }
              else
                throw (.category parameter (.unknownCategory category))

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
  | .baseYear offset :: rest => do
      match hDeclared : model.baseYear with
      | none => throw .noBaseYear
      | some base =>
          pure (.baseYear offset (base + offset) (by
            rw [hDeclared, Int.add_sub_cancel]) ::
            (← checkMessageParts model profile condition rest))
  | .group parameter authored :: rest => do
      pure (.group (← checkMessageGroup condition parameter authored) ::
        (← checkMessageParts model profile condition rest))
  | .keyed parameter reference _suffix key :: rest => do
      -- Measured, a keyed parameter is *not* subject to the condition-membership gate an unkeyed one
      -- carries: a keyed read of a field the condition never names is admitted, provided the
      -- condition uses the same semantic index. Both name-bearing positions are still resolved as
      -- entities, because an unresolvable name is refused there rather than at the index gate — so
      -- these resolutions are kept for their refusals, and their results are unusable here. The
      -- decoded suffix is likewise unusable, since no part this fragment can build carries a key.
      discard <| resolveMessageEntity model profile condition parameter reference
      match key with
        | .literal _ => pure ()
        | .field keyReference =>
            discard <|
              resolveMessageEntity model profile condition parameter keyReference
      throw (.semanticIndexUnsupported parameter)
  | .fieldCategory parameter reference category :: rest => do
      let resolved ←
        resolveMessageReference model profile condition parameter reference
      pure (.fieldCategory
        (← resolveMessageCategory resolved parameter category) ::
        (← checkMessageParts model profile condition rest))
  | .fieldCategoryWithTrailingSyntax parameter reference category :: _ => do
      let resolved ←
        resolveMessageReference model profile condition parameter reference
      discard <| resolveMessageCategory resolved parameter category
      throw (.invalidParameter parameter)

def elaborateValidationMessageTemplate (model : FlatModel)
    (profile : ValidationMessageKeywordProfile)
    (condition : CheckedFlatCondition model) (source : String) :
    Except ValidationMessageTemplateError
      (CheckedValidationMessageTemplate model condition) := do
  let parsed ← parseValidationMessageTemplate profile source
  pure { source, parts := ← checkMessageParts model profile condition parsed }

structure ValidationMessageInputs where
  fieldName : FieldId → MessageNameInput
  fieldValue : FieldId → MessageValueInput
  /-- The field's current stored token. The category mapping is applied by the checked part, not by
  the caller, because the mapping is the declaration's and is measured. -/
  fieldStoredToken : FieldId → Option String
  /-- The bytes an admitted group parameter renders as. They are the caller's because the Kernel's own
  rendering for this position is unmeasured. -/
  group : GroupPath → MessageGroupInput

def CheckedValidationMessagePart.toRenderPart
    (inputs : ValidationMessageInputs) :
    CheckedValidationMessagePart model condition → MessageRenderPart
  | .text value => .text value
  | .fieldName reference => .fieldName (inputs.fieldName reference.declaration.id)
  | .fieldValue reference => .fieldValue (inputs.fieldValue reference.declaration.id)
  | .fieldCategory access =>
      .fieldCategory {
        categoryToken :=
          (inputs.fieldStoredToken access.reference.declaration.id).bind
            (access.projection.declaration.categoryTokenFor? access.category) }
  | .baseYear _ year _ => .baseYear year
  | .group access => .group (inputs.group access.group)

def CheckedValidationMessageTemplate.toRenderPlan
    (template : CheckedValidationMessageTemplate model condition)
    (inputs : ValidationMessageInputs) : MessageRenderPlan :=
  { parts := template.parts.map (·.toRenderPart inputs) }

end A12Kernel
