import A12Kernel.Elaboration.ValidationRule

/-! # Checked authoring for bounded flat validation-message templates -/

namespace A12Kernel

inductive ValidationMessageTemplateError where
  | emptyTemplate
  | lineSeparator
  | controlCharacter (character : Char)
  | unsupportedCharacter (character : Char)
  | oddDollarCount
  | invalidParameter (parameter : String)
  | unsupportedQuotedName (name : String)
  | reference (parameter : String) (error : ResolveError)
  | fieldNotReferenced (parameter : String) (field : FieldId)
  deriving Repr, DecidableEq

private inductive ParsedValidationMessagePart where
  | text (value : String)
  | fieldName (name : String)
  | fieldValue (name : String)

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

private def parseParameter (parameter : String) :
    Except ValidationMessageTemplateError ParsedValidationMessagePart :=
  match parameter.splitOn ".value" with
  | [name, ""] =>
      if isBareName name then .ok (.fieldValue name)
      else .error (.invalidParameter parameter)
  | [_] =>
      if isBareName parameter then .ok (.fieldName parameter)
      else .error (.invalidParameter parameter)
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

private def parseValidationMessageTemplate (source : String) :
    Except ValidationMessageTemplateError (List ParsedValidationMessagePart) := do
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
  parseSegments (source.splitOn "$")

private def bareMessageField (name : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field := name }

structure CheckedValidationMessageReference
    (model : FlatModel) (condition : CheckedFlatCondition model) where
  parameter : String
  declaration : FlatFieldDecl
  resolved :
    model.resolveNonrepeatableFieldUnchecked condition.rowGroup
      (bareMessageField parameter) = .ok declaration
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
    (profile : PathKeywordProfile) (condition : CheckedFlatCondition model)
    (parameter : String) :
    Except ValidationMessageTemplateError
      (CheckedValidationMessageReference model condition) := do
  if profile.requiresQuote parameter then
    throw (.unsupportedQuotedName parameter)
  let reference := bareMessageField parameter
  match hResolved :
      model.resolveNonrepeatableFieldUnchecked condition.rowGroup reference with
  | .error error => throw (.reference parameter error)
  | .ok declaration =>
      if hReferenced :
          condition.core.referencesField declaration.id = true then
        pure {
          parameter
          declaration
          resolved := hResolved
          conditionReferenced := hReferenced
        }
      else
        throw (.fieldNotReferenced parameter declaration.id)

private def checkMessageParts (model : FlatModel)
    (profile : PathKeywordProfile) (condition : CheckedFlatCondition model) :
    List ParsedValidationMessagePart →
      Except ValidationMessageTemplateError
        (List (CheckedValidationMessagePart model condition))
  | [] => .ok []
  | .text value :: rest => do
      pure (.text value :: (← checkMessageParts model profile condition rest))
  | .fieldName name :: rest => do
      pure (.fieldName (← resolveMessageReference model profile condition name) ::
        (← checkMessageParts model profile condition rest))
  | .fieldValue name :: rest => do
      pure (.fieldValue (← resolveMessageReference model profile condition name) ::
        (← checkMessageParts model profile condition rest))

def elaborateValidationMessageTemplate (model : FlatModel)
    (profile : PathKeywordProfile) (condition : CheckedFlatCondition model)
    (source : String) :
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

end A12Kernel
