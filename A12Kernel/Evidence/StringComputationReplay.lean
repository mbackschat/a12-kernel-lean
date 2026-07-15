import A12Kernel.Basic
import A12Kernel.Evidence.StringComputationSchema
import A12Kernel.Semantics.StringComputation

/-! # A12Kernel.Evidence.StringComputationReplay — pure thirteen-case replay -/

namespace A12Kernel.Evidence.StringComputation

open A12Kernel

private def hasDuplicate [BEq α] : List α → Bool
  | [] => false
  | value :: rest => rest.contains value || hasDuplicate rest

private def lowercaseHexOfLength (length : Nat) (value : String) : Bool :=
  value.length == length && value.toList.all fun character =>
    character.isDigit || ('a' ≤ character && character ≤ 'f')

private def portableRelative (reference : String) : Bool :=
  !reference.isEmpty && !reference.startsWith "/" && !(reference.splitOn "/").contains ".."

private def conservativeStringLiteral (value : String) : Bool :=
  value.toList.all fun character =>
    let code := character.toNat
    0x20 ≤ code && code ≤ 0x7e && character != '"' && character != '\\'

def FieldSpec.path (field : FieldSpec) : List String := field.groups ++ [field.name]

def ModelSpec.findField (model : ModelSpec) (id : FieldId) : Except String FieldSpec :=
  match model.fields.filter (·.id == id) with
  | [field] => pure field
  | [] => throw s!"{model.id}: no projected field {id}"
  | _ => throw s!"{model.id}: duplicate projected field {id}"

def ExprSpec.fieldIds : ExprSpec → List FieldId
  | .field fieldId => [fieldId]
  | .literal _ => []
  | .concat left right => left.fieldIds ++ right.fieldIds

def ExprSpec.toCore : ExprSpec → StringExpr
  | .field fieldId => .field fieldId
  | .literal value => .literal value
  | .concat left right => .concat left.toCore right.toCore

def ExprSpec.render (expression : ExprSpec) (model : ModelSpec) : Except String String :=
  match expression with
  | .field fieldId => do
      let field ← model.findField fieldId
      pure s!"[{field.name}]"
  | .literal value =>
      if conservativeStringLiteral value then pure s!"\"{value}\""
      else throw s!"{model.id}: String literal is outside the conservative evidence renderer"
  | .concat left right => do
      let leftText ← left.render model
      let rightText ← right.render model
      pure s!"{leftText} + {rightText}"

private def CellStateSpec.toRaw : CellStateSpec → RawCell
  | .empty => .empty
  | .string value => .parsed (.str value)

private def CaseSpec.context (case : CaseSpec) : StringComputationContext where
  read fieldId :=
    let raw := (case.cells.find? (·.fieldId == fieldId)).map (·.state.toRaw) |>.getD .empty
    formalCheck { kind := .string } raw

private def TargetStateSpec.toPrior : TargetStateSpec → Except String PriorStringTarget
  | .empty => pure .empty
  | .string value =>
      if nonempty : value ≠ "" then pure (.filled { text := value, nonempty })
      else throw "a prior stored String cannot be empty"

private def deltaSignature (targetPointer : String) :
    Option StringDelta → Except String (List String)
  | none => pure []
  | some (.value stored) => pure [s!"{targetPointer}|VALUE|{stored.text}"]
  | some .cleared => pure [s!"{targetPointer}|CLEARED"]
  | some (.errored _ _) =>
      throw "unconstrained String-computation replay produced a target error"

private def FieldSpec.validate (model : ModelSpec) (field : FieldSpec) : Except String Unit := do
  if field.groups != model.declaringGroup || field.groups.any String.isEmpty || field.name.isEmpty then
    throw s!"{model.id}: invalid projected field path {repr field.path}"

private def ExprSpec.validate (expression : ExprSpec) (model : ModelSpec) : Except String Unit := do
  for fieldId in expression.fieldIds do
    if fieldId == model.targetFieldId then
      throw s!"{model.id}: computation directly references its target field"
    discard <| model.findField fieldId
  discard <| expression.render model

private def ModelSpec.validate (model : ModelSpec) : Except String Unit := do
  if model.id.isEmpty || !portableRelative model.modelRef ||
      !lowercaseHexOfLength 64 model.modelSha256 then
    throw s!"{model.id}: invalid projected model identity"
  if model.declaringGroup.isEmpty || model.declaringGroup.any String.isEmpty then
    throw s!"{model.id}: invalid declaring group"
  if model.fields.length != 4 || hasDuplicate (model.fields.map (·.id)) ||
      hasDuplicate (model.fields.map (·.path)) then
    throw s!"{model.id}: expected four unique projected String fields"
  model.fields.forM (·.validate model)
  let target ← model.findField model.targetFieldId
  if model.computationName.isEmpty || model.targetRelPath != "../" ++ target.name then
    throw s!"{model.id}: invalid computation target identity"
  let expectedPointer := "/" ++ String.intercalate "/" model.declaringGroup ++ "[1]/" ++ target.name
  if model.targetPointer != expectedPointer then
    throw s!"{model.id}: target pointer differs from the projected target"
  model.expression.validate model

private def CellStateSpec.validate (caseId : String) : CellStateSpec → Except String Unit
  | .empty => pure ()
  | .string value =>
      if value.isEmpty then throw s!"{caseId}: an empty input String must use the empty state"
      else pure ()

def Bundle.modelFor (bundle : Bundle) (case : CaseSpec) : Except String ModelSpec :=
  match bundle.models.filter (·.id == case.modelId) with
  | [model] => pure model
  | [] => throw s!"{case.id}: unknown model '{case.modelId}'"
  | _ => throw s!"{case.id}: duplicate model '{case.modelId}'"

private def CaseSpec.validate (bundle : Bundle) (case : CaseSpec) : Except String Unit := do
  if case.id.isEmpty || !portableRelative case.caseRef || !lowercaseHexOfLength 64 case.caseSha256 then
    throw s!"{case.id}: invalid projected case identity"
  if hasDuplicate (case.cells.map (·.fieldId)) then
    throw s!"{case.id}: duplicate projected source cell"
  let model ← bundle.modelFor case
  let expectedFields := model.expression.fieldIds.eraseDups.mergeSort
  if (case.cells.map (·.fieldId)).mergeSort != expectedFields then
    throw s!"{case.id}: projected cells must cover exactly the expression's fields"
  for cell in case.cells do
    discard <| model.findField cell.fieldId
    cell.state.validate case.id
  discard <| case.priorTarget.toPrior

def CaseSpec.replay (case : CaseSpec) (model : ModelSpec) : Except String (List String) := do
  let store ← match model.expression.toCore.evaluate case.context with
    | .ok result => pure result
    | .error (.fieldKindMismatch fieldId) =>
        throw s!"{case.id}: projected field {fieldId} failed its String kind invariant"
  let prior ← case.priorTarget.toPrior
  deltaSignature model.targetPointer (store.projectDelta prior)

def Bundle.validate (bundle : Bundle) : Except String Unit := do
  if bundle.schemaVersion != 1 then
    throw s!"unsupported String-computation evidence schema {bundle.schemaVersion}"
  if bundle.kernelVersion != A12Kernel.kernelVersion then
    throw s!"String-computation evidence targets kernel {bundle.kernelVersion}"
  if !portableRelative bundle.captureRef || !lowercaseHexOfLength 64 bundle.captureSha256 ||
      !lowercaseHexOfLength 40 bundle.sourceRevision then
    throw "invalid String-computation capture identity"
  if bundle.models.length != 3 || bundle.cases.length != 13 then
    throw "String-computation projection must retain exactly three models and thirteen cases"
  if hasDuplicate (bundle.models.map (·.id)) || hasDuplicate (bundle.models.map (·.modelRef)) ||
      hasDuplicate (bundle.cases.map (·.id)) || hasDuplicate (bundle.cases.map (·.caseRef)) then
    throw "duplicate String-computation model or case identity"
  bundle.models.forM ModelSpec.validate
  bundle.cases.forM (·.validate bundle)

end A12Kernel.Evidence.StringComputation
