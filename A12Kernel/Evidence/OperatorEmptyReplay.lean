import A12Kernel.Basic
import A12Kernel.Evidence.OperatorEmptySchema
import A12Kernel.Evidence.Replay

/-! # A12Kernel.Evidence.OperatorEmptyReplay — pure six-case replay projection -/

namespace A12Kernel.Evidence.OperatorEmpty

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
  !value.isEmpty && value.toList.all fun character =>
    let code := character.toNat
    0x20 ≤ code && code ≤ 0x7e && character != '"' && character != '\\'

def FieldSpec.path (field : FieldSpec) : List String := field.groups ++ [field.name]

private def FieldSpec.toDeclaration (field : FieldSpec) : FlatFieldDecl :=
  { id := field.id
    groupPath := field.groups
    name := field.name
    policy := { kind := match field.kind with
      | .number scale signed => .number { scale, signed }
      | .string => .string } }

def ModelSpec.findField (model : ModelSpec) (id : FieldId) : Except String FieldSpec :=
  match model.fields.filter (·.id == id) with
  | [field] => pure field
  | [] => throw s!"{model.id}: no projected field {id}"
  | _ => throw s!"{model.id}: duplicate projected field {id}"

private def FieldSpec.surfacePath (field : FieldSpec) : SurfaceFieldPath :=
  { base := .absolute, groups := field.groups, field := field.name }

def ConditionSpec.fieldId : ConditionSpec → FieldId
  | .numberNotEqual fieldId _
  | .stringEqual fieldId _
  | .stringLengthLess fieldId _
  | .stringLengthGreaterEqual fieldId _ => fieldId

def ConditionSpec.toSurface (condition : ConditionSpec) (model : ModelSpec) :
    Except String SurfaceCondition := do
  let field ← model.findField condition.fieldId
  match condition, field.kind with
  | .numberNotEqual _ expected, .number .. =>
      pure (.compare .notEqual field.surfacePath (.number expected))
  | .stringEqual _ expected, .string =>
      if !conservativeStringLiteral expected then
        throw s!"{model.id}: String literal is outside the conservative evidence renderer"
      pure (.compare .equal field.surfacePath (.string expected))
  | .stringLengthLess _ expected, .string =>
      pure (.lengthCompare .less field.surfacePath expected)
  | .stringLengthGreaterEqual _ expected, .string =>
      pure (.lengthCompare .greaterEqual field.surfacePath expected)
  | _, actual =>
      throw s!"{model.id}: condition field {field.id} has incompatible kind {repr actual}"

def ConditionSpec.render (condition : ConditionSpec) (model : ModelSpec) : Except String String := do
  let field ← model.findField condition.fieldId
  let path := "/" ++ String.intercalate "/" field.path
  match condition with
  | .numberNotEqual _ expected => pure s!"[{path}] != {expected}"
  | .stringEqual _ expected =>
      if !conservativeStringLiteral expected then
        throw s!"{model.id}: String literal is outside the conservative evidence renderer"
      pure s!"[{path}] == \"{expected}\""
  | .stringLengthLess _ expected => pure s!"Length({path}) < {expected}"
  | .stringLengthGreaterEqual _ expected => pure s!"Length({path}) >= {expected}"

private def CellStateSpec.toRaw : CellStateSpec → RawCell
  | .empty => .empty
  | .number value => .parsed (.num value)
  | .string value => .parsed (.str value)

private def ModelSpec.flatModel (model : ModelSpec) : FlatModel :=
  { fields := model.fields.map FieldSpec.toDeclaration }

private def CaseSpec.rawContext (case : CaseSpec) : RawFlatContext where
  read id := (case.cells.find? (·.fieldId == id)).map (·.state.toRaw) |>.getD .empty

private def signature (rule : RuleSpec) : Verdict → List String
  | .fired .value => [s!"{rule.code}|VALUE_ERROR|{rule.errorPointer}"]
  | .fired .omission => [s!"{rule.code}|OMISSION_ERROR|{rule.errorPointer}"]
  | .notFired | .unknown => []

def ModelSpec.replay (model : ModelSpec) (case : CaseSpec) : Except String (List String) := do
  let flatModel := model.flatModel
  let mut signatures := []
  for rule in model.rules do
    let condition ← rule.condition.toSurface model
    let verdict ← match elaborateAndEvalFull flatModel model.declaringGroup case.rawContext
        case.hasContent condition with
      | .ok verdict => pure verdict
      | .error error => throw s!"{case.id}/{rule.code}: elaboration failed: {repr error}"
    signatures := signature rule verdict ++ signatures
  pure signatures.mergeSort

private def FieldSpec.validate (modelId : String) (field : FieldSpec) : Except String Unit := do
  if field.groups.isEmpty || field.groups.any String.isEmpty || field.name.isEmpty then
    throw s!"{modelId}: invalid projected field path {repr field.path}"

private def RuleSpec.validate (model : ModelSpec) (rule : RuleSpec) : Except String Unit := do
  if rule.name.isEmpty || rule.code.isEmpty || rule.errorPointer.isEmpty then
    throw s!"{model.id}: incomplete projected rule identity"
  discard <| model.findField rule.errorFieldId
  discard <| rule.condition.toSurface model
  discard <| rule.condition.render model

private def ModelSpec.validate (model : ModelSpec) : Except String Unit := do
  if model.id.isEmpty || !portableRelative model.modelRef ||
      !lowercaseHexOfLength 64 model.modelSha256 then
    throw s!"{model.id}: invalid projected model identity"
  if model.declaringGroup.isEmpty || model.declaringGroup.any String.isEmpty then
    throw s!"{model.id}: invalid declaring group"
  if model.fields.isEmpty || hasDuplicate (model.fields.map (·.id)) ||
      hasDuplicate (model.fields.map (·.path)) then
    throw s!"{model.id}: empty or duplicate projected fields"
  if model.rules.isEmpty || hasDuplicate (model.rules.map (·.name)) ||
      hasDuplicate (model.rules.map (·.code)) then
    throw s!"{model.id}: empty or duplicate projected rules"
  model.fields.forM (·.validate model.id)
  model.rules.forM (·.validate model)
  match model.flatModel.validate with
  | .ok _ => pure ()
  | .error error => throw s!"{model.id}: invalid projected flat model: {repr error}"

private def cellKindMatches (field : FieldSpec) : CellStateSpec → Bool
  | .empty => true
  | .number _ => match field.kind with | .number .. => true | _ => false
  | .string _ => match field.kind with | .string => true | _ => false

private def CaseSpec.validate (bundle : Bundle) (case : CaseSpec) : Except String Unit := do
  if case.id.isEmpty || !portableRelative case.caseRef || !lowercaseHexOfLength 64 case.caseSha256 then
    throw s!"{case.id}: invalid projected case identity"
  if hasDuplicate (case.cells.map (·.fieldId)) then
    throw s!"{case.id}: duplicate projected cell"
  let model ← match bundle.models.filter (·.id == case.modelId) with
    | [model] => pure model
    | [] => throw s!"{case.id}: unknown model '{case.modelId}'"
    | _ => throw s!"{case.id}: duplicate model '{case.modelId}'"
  if (case.cells.map (·.fieldId)).mergeSort != (model.fields.map (·.id)).mergeSort then
    throw s!"{case.id}: projected cells must cover every projected field exactly once"
  for cell in case.cells do
    let field ← model.findField cell.fieldId
    if !cellKindMatches field cell.state then
      throw s!"{case.id}: cell {cell.fieldId} has the wrong projected kind"

def Bundle.validate (bundle : Bundle) : Except String Unit := do
  if bundle.schemaVersion != 1 then
    throw s!"unsupported operator-empty evidence schema {bundle.schemaVersion}"
  if bundle.kernelVersion != A12Kernel.kernelVersion then
    throw s!"operator-empty evidence targets kernel {bundle.kernelVersion}"
  if !portableRelative bundle.captureRef || !lowercaseHexOfLength 64 bundle.captureSha256 ||
      !lowercaseHexOfLength 40 bundle.sourceRevision then
    throw "invalid operator-empty capture identity"
  if bundle.models.length != 2 || bundle.cases.length != 6 then
    throw "operator-empty projection must retain exactly two models and six cases"
  if hasDuplicate (bundle.models.map (·.id)) || hasDuplicate (bundle.models.map (·.modelRef)) ||
      hasDuplicate (bundle.cases.map (·.id)) || hasDuplicate (bundle.cases.map (·.caseRef)) then
    throw "duplicate operator-empty model or case identity"
  bundle.models.forM ModelSpec.validate
  bundle.cases.forM (·.validate bundle)

def Bundle.modelFor (bundle : Bundle) (case : CaseSpec) : Except String ModelSpec :=
  match bundle.models.filter (·.id == case.modelId) with
  | [model] => pure model
  | [] => throw s!"{case.id}: unknown model '{case.modelId}'"
  | _ => throw s!"{case.id}: duplicate model '{case.modelId}'"

end A12Kernel.Evidence.OperatorEmpty
