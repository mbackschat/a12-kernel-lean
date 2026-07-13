import A12Kernel.Basic
import A12Kernel.Evidence.IterationSchema
import A12Kernel.Semantics.Iteration

/-! # A12Kernel.Evidence.IterationReplay — pure single-level iteration replay -/

namespace A12Kernel.Evidence.Iteration

open A12Kernel

private def hasDuplicate [BEq α] (values : List α) : Bool :=
  match values with
  | [] => false
  | value :: rest => rest.contains value || hasDuplicate rest

private def NumberFieldSpec.toField (field : NumberFieldSpec) : FlatNumberField :=
  { id := field.id, info := { scale := field.scale, signed := field.signed } }

private def NumberCellStateSpec.toRaw : NumberCellStateSpec → RawCell
  | .empty => .empty
  | .number value => .parsed (.num value)
  | .rejected => .rejected .malformed

private def findField (fields : List NumberFieldSpec) (id : FieldId) :
    Option NumberFieldSpec :=
  match fields with
  | [] => none
  | field :: rest => if field.id = id then some field else findField rest id

private def findCell (cells : List NumberCellSpec) (rowId : RowIndex) (fieldId : FieldId) :
    Option NumberCellSpec :=
  match cells with
  | [] => none
  | cell :: rest =>
      if cell.rowId = rowId && cell.fieldId = fieldId then some cell
      else findCell rest rowId fieldId

private def CaseSpec.checkedCell (case : CaseSpec) (rowId : RowIndex)
    (field : NumberFieldSpec) : CheckedCell :=
  let raw := (findCell case.cells rowId field.id).map (·.state.toRaw) |>.getD .empty
  formalCheck { kind := .number { scale := field.scale, signed := field.signed } } raw

private def CaseSpec.context (case : CaseSpec) : SingleGroupValidationContext where
  group := case.groupId
  candidates := case.rowIds
  read rowId fieldId :=
    match findField case.fields fieldId with
    | some field => case.checkedCell rowId field
    | none => formalCheck { kind := .number { scale := 0, signed := false } } .empty

private def CaseSpec.star (case : CaseSpec) (valueField : NumberFieldSpec) : SingleStar :=
  { valueField := valueField.toField
    having := case.having.map fun having =>
      let field := (findField case.fields having.fieldId).getD valueField
      .compare (.number .equal field.toField having.equals) }

private def CaseSpec.validateTransport (case : CaseSpec) : Except String Unit := do
  if case.id.isEmpty then throw "iteration evidence case id must not be empty"
  if case.caseRef.isEmpty then throw s!"{case.id}: caseRef must not be empty"
  if case.focusCode.isEmpty then throw s!"{case.id}: focusCode must not be empty"
  if case.focusPointer.isEmpty then throw s!"{case.id}: focusPointer must not be empty"
  if case.fields.isEmpty then throw s!"{case.id}: fields must not be empty"
  if case.rowIds.any (· == 0) then throw s!"{case.id}: row ids must be 1-based"
  if hasDuplicate case.rowIds then throw s!"{case.id}: duplicate row id"
  if hasDuplicate (case.fields.map (·.id)) then throw s!"{case.id}: duplicate field id"
  if hasDuplicate (case.cells.map fun cell => (cell.rowId, cell.fieldId)) then
    throw s!"{case.id}: duplicate row/field cell"
  if !(case.fields.any (·.id == case.valueFieldId)) then
    throw s!"{case.id}: valueFieldId {case.valueFieldId} is undeclared"
  match case.having with
  | none => pure ()
  | some having =>
      if !(case.fields.any (·.id == having.fieldId)) then
        throw s!"{case.id}: Having field {having.fieldId} is undeclared"
  for cell in case.cells do
    if !(case.rowIds.contains cell.rowId) then
      throw s!"{case.id}: cell references non-candidate row {cell.rowId}"
    if !(case.fields.any (·.id == cell.fieldId)) then
      throw s!"{case.id}: cell references undeclared field {cell.fieldId}"

/-- Replay only the truth domain admitted by capsule 5a. `unknown` remains distinct in
    this return value even though the external message boundary can observe only fired
    versus silent. -/
def CaseSpec.replay (case : CaseSpec) : Except String K := do
  case.validateTransport
  let valueField ← match findField case.fields case.valueFieldId with
    | some field => pure field
    | none => throw s!"{case.id}: valueFieldId {case.valueFieldId} is undeclared"
  pure ((case.star valueField).evalSumEquality case.context .equal case.equals)

def Bundle.validate (bundle : Bundle) : Except String Unit := do
  if bundle.schemaVersion != 1 then
    throw s!"unsupported iteration evidence schema version {bundle.schemaVersion}"
  if bundle.kernelVersion != A12Kernel.kernelVersion then
    throw s!"iteration evidence targets kernel {bundle.kernelVersion}, Lean targets {A12Kernel.kernelVersion}"
  if bundle.cases.isEmpty then throw "iteration evidence bundle must contain at least one case"
  if hasDuplicate (bundle.cases.map (·.id)) then throw "duplicate iteration evidence case id"
  if hasDuplicate (bundle.cases.map (·.caseRef)) then throw "duplicate iteration evidence caseRef"
  bundle.cases.forM CaseSpec.validateTransport

end A12Kernel.Evidence.Iteration
