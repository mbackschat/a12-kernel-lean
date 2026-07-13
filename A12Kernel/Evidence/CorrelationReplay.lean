import A12Kernel.Basic
import A12Kernel.Evidence.CorrelationSchema
import A12Kernel.Semantics.Correlation

/-! # A12Kernel.Evidence.CorrelationReplay — pure captured-outer replay -/

namespace A12Kernel.Evidence.Correlation

open A12Kernel

structure Firing where
  rowId : RowIndex
  pointer : String
  deriving Repr, DecidableEq

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

private def OriginSpec.toOrigin : OriginSpec → HavingOrigin
  | .inner => .inner
  | .outer => .outer

private def ComparisonOpSpec.toOp : ComparisonOpSpec → CorrelationComparisonOp
  | .equal => .equal
  | .notEqual => .notEqual
  | .lessThan => .lessThan

private def ComparisonOpSpec.token : ComparisonOpSpec → String
  | .equal => "=="
  | .notEqual => "!="
  | .lessThan => "<"

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

private def findOuterRow (rows : List OuterRowSpec) (rowId : RowIndex) :
    Option OuterRowSpec :=
  match rows with
  | [] => none
  | row :: rest => if row.rowId = rowId then some row else findOuterRow rest rowId

private def safeEntityPath (path : String) : Bool :=
  path.startsWith "/" && path.length > 1 && !path.endsWith "/" &&
    !path.contains '*' && !path.contains '$' && !path.contains '|' &&
    !(path.splitOn "/").contains ".." && !(path.splitOn "/").contains "."

private def directChildOf (groupPath fieldPath : String) : Bool :=
  let pathPrefix := groupPath ++ "/"
  if fieldPath.startsWith pathPrefix then
    let name := fieldPath.drop pathPrefix.length
    !name.isEmpty && !name.contains '/'
  else
    false

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

private def NumberRefSpec.toRef (fields : List NumberFieldSpec)
    (reference : NumberRefSpec) : Except String HavingNumberRef := do
  let field ← match findField fields reference.fieldId with
    | some field => pure field
    | none => throw s!"correlation filter references undeclared field {reference.fieldId}"
  pure { origin := reference.origin.toOrigin, field := field.toField }

private def NumberRefSpec.render (fields : List NumberFieldSpec)
    (reference : NumberRefSpec) : Except String String := do
  let field ← match findField fields reference.fieldId with
    | some field => pure field
    | none => throw s!"correlation filter references undeclared field {reference.fieldId}"
  pure <| match reference.origin with
    | .inner => s!"[{field.path}]"
    | .outer => s!"[${field.path}]"

private def OriginSpec.renderRepetition (groupPath : String) : OriginSpec → String
  | .inner => s!"CurrentRepetition({groupPath})"
  | .outer => s!"CurrentRepetition(${groupPath})"

private def FilterSpec.toHaving (fields : List NumberFieldSpec) :
    FilterSpec → Except String CorrelatedHaving
  | .compareNumbers op left right => do
      pure (.compareNumbers op.toOp (← left.toRef fields) (← right.toRef fields))
  | .compareRepetitions op left right =>
      pure (.compareRepetitions op.toOp left.toOrigin right.toOrigin)
  | .and left right => do
      pure (.and (← left.toHaving fields) (← right.toHaving fields))

private def FilterSpec.render (fields : List NumberFieldSpec) (groupPath : String) :
    FilterSpec → Except String String
  | .compareNumbers op left right => do
      pure s!"{← left.render fields} {op.token} {← right.render fields}"
  | .compareRepetitions op left right =>
      pure s!"{left.renderRepetition groupPath} {op.token} {right.renderRepetition groupPath}"
  | .and left right => do
      pure s!"{← left.render fields groupPath} And {← right.render fields groupPath}"

private def CaseSpec.checkedHaving (case : CaseSpec) :
    Except String OriginCheckedCorrelatedHaving := do
  let condition ← case.filter.toHaving case.fields
  match condition.check with
  | .ok checked => pure checked
  | .error .missingInner => throw "correlation filter has no inner reference"
  | .error .missingOuter => throw "correlation filter has no outer reference"

private def CaseSpec.validateTransport (case : CaseSpec) : Except String Unit := do
  if case.id.isEmpty then throw "correlation evidence case id must not be empty"
  if case.caseRef.isEmpty then throw s!"{case.id}: caseRef must not be empty"
  if case.focusCode.isEmpty then throw s!"{case.id}: focusCode must not be empty"
  if case.fields.isEmpty then throw s!"{case.id}: fields must not be empty"
  if !safeEntityPath case.groupPath then
    throw s!"{case.id}: invalid groupPath '{case.groupPath}'"
  if case.rowIds.isEmpty then throw s!"{case.id}: rowIds must not be empty"
  if case.rowIds.any (· == 0) then throw s!"{case.id}: row ids must be 1-based"
  if hasDuplicate case.rowIds then throw s!"{case.id}: duplicate row id"
  if hasDuplicate (case.fields.map (·.id)) then throw s!"{case.id}: duplicate field id"
  if hasDuplicate (case.fields.map (·.path)) then throw s!"{case.id}: duplicate field path"
  for field in case.fields do
    if !safeEntityPath field.path then
      throw s!"{case.id}: invalid field path '{field.path}'"
    if !directChildOf case.groupPath field.path then
      throw s!"{case.id}: field '{field.path}' is not a direct child of group '{case.groupPath}'"
  if hasDuplicate (case.cells.map fun cell => (cell.rowId, cell.fieldId)) then
    throw s!"{case.id}: duplicate row/field cell"
  if !(case.fields.any (·.id == case.valueFieldId)) then
    throw s!"{case.id}: valueFieldId {case.valueFieldId} is undeclared"
  if case.outerRows.map (·.rowId) != case.rowIds then
    throw s!"{case.id}: outerRows must map every rowId once and in row order"
  if case.outerRows.any (·.pointer.isEmpty) then
    throw s!"{case.id}: outer row pointer must not be empty"
  if hasDuplicate (case.outerRows.map (·.pointer)) then
    throw s!"{case.id}: duplicate outer row pointer"
  for cell in case.cells do
    if !(case.rowIds.contains cell.rowId) then
      throw s!"{case.id}: cell references non-candidate row {cell.rowId}"
    if !(case.fields.any (·.id == cell.fieldId)) then
      throw s!"{case.id}: cell references undeclared field {cell.fieldId}"
  discard case.checkedHaving

/-- Canonical stored-English rendering for the one admitted external rule shape. This
    is intentionally not a general condition parser or renderer. -/
def CaseSpec.renderCondition (case : CaseSpec) : Except String String := do
  case.validateTransport
  let valueField ← match findField case.fields case.valueFieldId with
    | some field => pure field
    | none => throw s!"{case.id}: valueFieldId {case.valueFieldId} is undeclared"
  let suffix := valueField.path.drop case.groupPath.length
  let starPath := case.groupPath ++ "*" ++ suffix
  pure s!"FieldFilled({valueField.path}) And AtLeastOneFieldFilled({starPath} Having {← case.filter.render case.fields case.groupPath})"

/-- Replay returns only ordered outer row identities and their externally meaningful
    pointers. Message polarity remains an observation retained by the IO driver. -/
def CaseSpec.replay (case : CaseSpec) : Except String (List Firing) := do
  case.validateTransport
  let valueField ← match findField case.fields case.valueFieldId with
    | some field => pure field
    | none => throw s!"{case.id}: valueFieldId {case.valueFieldId} is undeclared"
  let star : SingleCorrelatedStar :=
    { valueField := valueField.toField, having := ← case.checkedHaving }
  let firingRows := star.firingRows case.context
  firingRows.mapM fun rowId =>
    match findOuterRow case.outerRows rowId with
    | some row => pure { rowId, pointer := row.pointer }
    | none => throw s!"{case.id}: firing row {rowId} has no pointer mapping"

def Bundle.validate (bundle : Bundle) : Except String Unit := do
  if bundle.schemaVersion != 1 then
    throw s!"unsupported correlation evidence schema version {bundle.schemaVersion}"
  if bundle.kernelVersion != A12Kernel.kernelVersion then
    throw s!"correlation evidence targets kernel {bundle.kernelVersion}, Lean targets {A12Kernel.kernelVersion}"
  if bundle.cases.isEmpty then throw "correlation evidence bundle must contain at least one case"
  if hasDuplicate (bundle.cases.map (·.id)) then throw "duplicate correlation evidence case id"
  if hasDuplicate (bundle.cases.map (·.caseRef)) then throw "duplicate correlation evidence caseRef"
  bundle.cases.forM CaseSpec.validateTransport

end A12Kernel.Evidence.Correlation
