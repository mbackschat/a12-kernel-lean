import A12Kernel.Basic
import A12Kernel.Elaboration.Correlation
import A12Kernel.Evidence.CorrelationSchema

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

private def NumberCellStateSpec.toRaw : NumberCellStateSpec → RawCell
  | .empty => .empty
  | .number value => .parsed (.num value)
  | .rejected => .rejected .malformed

private def OriginSpec.toOrigin : OriginSpec → HavingOrigin
  | .inner => .inner
  | .outer => .outer

private def ComparisonOpSpec.toSurfaceOp : ComparisonOpSpec → SurfaceComparisonOp
  | .equal => .equal
  | .notEqual => .notEqual
  | .lessThan => .less

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

private def safeConditionPath (path : String) : Bool :=
  !path.isEmpty && !path.endsWith "/" && !path.contains '*' &&
    !path.contains '$' && !path.contains '|' &&
    !(path.splitOn "/").contains ".." && !(path.splitOn "/").contains "."

private def directChildOf (groupPath fieldPath : String) : Bool :=
  let pathPrefix := groupPath ++ "/"
  if fieldPath.startsWith pathPrefix then
    let name := fieldPath.drop pathPrefix.length
    !name.isEmpty && !name.contains '/'
  else
    false

private def CaseSpec.rawContext (case : CaseSpec) : RawSingleGroupContext where
  candidates := case.rowIds
  read rowId fieldId :=
    (findCell case.cells rowId fieldId).map (·.state.toRaw) |>.getD .empty

private def pathSegments (path : String) : List String :=
  (path.splitOn "/").filter (!·.isEmpty)

private def pathBase (path : String) : PathBase :=
  if path.startsWith "/" then .absolute else .relative 0

private def surfaceFieldPath (path : String) : SurfaceFieldPath :=
  let segments := pathSegments path
  { base := pathBase path, groups := segments.dropLast,
    field := segments.getLast?.getD "" }

private def surfaceGroupPath (path : String) : SurfaceGroupPath :=
  { base := pathBase path, groups := pathSegments path }

private def surfaceStarPath (groupPath : String) (field : String) :
    SurfaceSingleStarFieldPath :=
  let segments := pathSegments groupPath
  { base := pathBase groupPath, groupsBeforeStar := segments.dropLast,
    starredGroup := segments.getLast?.getD "", field }

private def NumberFieldSpec.toDeclaration (groupPath : GroupPath)
    (groupId : RepeatableLevel) (field : NumberFieldSpec) : FlatFieldDecl :=
  { id := field.id, groupPath, name := (pathSegments field.path).getLast?.getD "",
    policy := { kind := .number { scale := field.scale, signed := field.signed } },
    repeatableScope := [groupId] }

private def CaseSpec.model (case : CaseSpec) : FlatModel :=
  let groupPath := pathSegments case.groupPath
  { fields := case.fields.map (·.toDeclaration groupPath case.groupId)
    repeatableGroups := [{ level := case.groupId, path := groupPath }] }

private def CaseSpec.declaringGroup (case : CaseSpec) : GroupPath :=
  (pathSegments case.groupPath).dropLast

private def NumberRefSpec.toSurfaceRef (fields : List NumberFieldSpec)
    (reference : NumberRefSpec) : Except String SurfaceHavingNumberRef := do
  let field ← match findField fields reference.fieldId with
    | some field => pure field
    | none => throw s!"correlation filter references undeclared field {reference.fieldId}"
  let origin := reference.origin.toOrigin
  let surfaceField := surfaceFieldPath field.conditionPath
  pure { origin, field := surfaceField }

private def surfaceRepetitionRef (origin : OriginSpec) (groupPath : String) :
    SurfaceHavingRepetitionRef :=
  { origin := origin.toOrigin, group := surfaceGroupPath groupPath }

private def NumberRefSpec.render (fields : List NumberFieldSpec)
    (reference : NumberRefSpec) : Except String String := do
  let field ← match findField fields reference.fieldId with
    | some field => pure field
    | none => throw s!"correlation filter references undeclared field {reference.fieldId}"
  pure <| match reference.origin with
    | .inner => s!"[{field.conditionPath}]"
    | .outer => s!"[${field.conditionPath}]"

private def OriginSpec.renderRepetition (groupPath : String) : OriginSpec → String
  | .inner => s!"CurrentRepetition({groupPath})"
  | .outer => s!"CurrentRepetition(${groupPath})"

private def FilterSpec.toSurfaceHaving (fields : List NumberFieldSpec)
    (groupPath : String) : FilterSpec → Except String SurfaceCorrelatedHaving
  | .compareNumbers op left right => do
      pure (.compareNumbers op.toSurfaceOp
        (← left.toSurfaceRef fields) (← right.toSurfaceRef fields))
  | .compareRepetitions op left right =>
      pure (.compareRepetitions op.toSurfaceOp
        (surfaceRepetitionRef left groupPath)
        (surfaceRepetitionRef right groupPath))
  | .and left right => do
      pure (.and (← left.toSurfaceHaving fields groupPath)
        (← right.toSurfaceHaving fields groupPath))

private def FilterSpec.render (fields : List NumberFieldSpec) (groupPath : String) :
    FilterSpec → Except String String
  | .compareNumbers op left right => do
      pure s!"{← left.render fields} {op.token} {← right.render fields}"
  | .compareRepetitions op left right =>
      pure s!"{left.renderRepetition groupPath} {op.token} {right.renderRepetition groupPath}"
  | .and left right => do
      pure s!"{← left.render fields groupPath} And {← right.render fields groupPath}"

private def CaseSpec.surfaceRule (case : CaseSpec) :
    Except String SurfaceSingleCorrelatedRule := do
  let valueField ← match findField case.fields case.valueFieldId with
    | some field => pure field
    | none => throw s!"{case.id}: valueFieldId {case.valueFieldId} is undeclared"
  let guardField ← match findField case.fields case.guardFieldId with
    | some field => pure field
    | none => throw s!"{case.id}: guardFieldId {case.guardFieldId} is undeclared"
  pure {
    errorField := surfaceFieldPath guardField.conditionPath
    guardField := surfaceFieldPath guardField.conditionPath
    valueField := surfaceStarPath case.conditionGroupPath
      ((pathSegments valueField.conditionPath).getLast?.getD "")
    having := ← case.filter.toSurfaceHaving case.fields case.conditionGroupPath }

private def CaseSpec.validateTransport (case : CaseSpec) : Except String Unit := do
  if case.id.isEmpty then throw "correlation evidence case id must not be empty"
  if case.caseRef.isEmpty then throw s!"{case.id}: caseRef must not be empty"
  if case.focusCode.isEmpty then throw s!"{case.id}: focusCode must not be empty"
  if case.fields.isEmpty then throw s!"{case.id}: fields must not be empty"
  if !safeEntityPath case.groupPath then
    throw s!"{case.id}: invalid groupPath '{case.groupPath}'"
  if !safeConditionPath case.conditionGroupPath then
    throw s!"{case.id}: invalid conditionGroupPath '{case.conditionGroupPath}'"
  if case.rowIds.isEmpty then throw s!"{case.id}: rowIds must not be empty"
  if case.rowIds.any (· == 0) then throw s!"{case.id}: row ids must be 1-based"
  if hasDuplicate case.rowIds then throw s!"{case.id}: duplicate row id"
  if hasDuplicate (case.fields.map (·.id)) then throw s!"{case.id}: duplicate field id"
  if hasDuplicate (case.fields.map (·.path)) then throw s!"{case.id}: duplicate field path"
  if hasDuplicate (case.fields.map (·.conditionPath)) then
    throw s!"{case.id}: duplicate field conditionPath"
  for field in case.fields do
    if !safeEntityPath field.path then
      throw s!"{case.id}: invalid field path '{field.path}'"
    if !directChildOf case.groupPath field.path then
      throw s!"{case.id}: field '{field.path}' is not a direct child of group '{case.groupPath}'"
    if !safeConditionPath field.conditionPath then
      throw s!"{case.id}: invalid field conditionPath '{field.conditionPath}'"
    if !directChildOf case.conditionGroupPath field.conditionPath then
      throw s!"{case.id}: condition field '{field.conditionPath}' is not a direct child of condition group '{case.conditionGroupPath}'"
  if hasDuplicate (case.cells.map fun cell => (cell.rowId, cell.fieldId)) then
    throw s!"{case.id}: duplicate row/field cell"
  if !(case.fields.any (·.id == case.valueFieldId)) then
    throw s!"{case.id}: valueFieldId {case.valueFieldId} is undeclared"
  if !(case.fields.any (·.id == case.guardFieldId)) then
    throw s!"{case.id}: guardFieldId {case.guardFieldId} is undeclared"
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
  let surfaceRule ← case.surfaceRule
  match elaborateSingleCorrelatedRule case.model case.declaringGroup surfaceRule with
  | .ok _ => pure ()
  | .error error => throw s!"{case.id}: correlation elaboration rejected the projection: {repr error}"

/-- Canonical stored-English rendering for the one admitted external rule shape. This
    is intentionally not a general condition parser or renderer. -/
def CaseSpec.renderCondition (case : CaseSpec) : Except String String := do
  case.validateTransport
  let valueField ← match findField case.fields case.valueFieldId with
    | some field => pure field
    | none => throw s!"{case.id}: valueFieldId {case.valueFieldId} is undeclared"
  let guardField ← match findField case.fields case.guardFieldId with
    | some field => pure field
    | none => throw s!"{case.id}: guardFieldId {case.guardFieldId} is undeclared"
  let suffix := valueField.conditionPath.drop case.conditionGroupPath.length
  let starPath := case.conditionGroupPath ++ "*" ++ suffix
  pure s!"FieldFilled({guardField.conditionPath}) And AtLeastOneFieldFilled({starPath} Having {← case.filter.render case.fields case.conditionGroupPath})"

/-- Replay returns only ordered outer row identities and their externally meaningful
    pointers. Message polarity remains an observation retained by the IO driver. -/
def CaseSpec.replay (case : CaseSpec) : Except String (List Firing) := do
  case.validateTransport
  let surfaceRule ← case.surfaceRule
  let checked ← match elaborateSingleCorrelatedRule case.model case.declaringGroup surfaceRule with
    | .ok checked => pure checked
    | .error error =>
        throw s!"{case.id}: correlation elaboration rejected the projection: {repr error}"
  let firingRows ← match checked.firingRows case.rawContext with
    | .ok rows => pure rows
    | .error error => throw s!"{case.id}: invalid candidate topology: {repr error}"
  firingRows.mapM fun rowId =>
    match findOuterRow case.outerRows rowId with
    | some row => pure { rowId, pointer := row.pointer }
    | none => throw s!"{case.id}: firing row {rowId} has no pointer mapping"

def Bundle.validate (bundle : Bundle) : Except String Unit := do
  if bundle.schemaVersion != 2 then
    throw s!"unsupported correlation evidence schema version {bundle.schemaVersion}"
  if bundle.kernelVersion != A12Kernel.kernelVersion then
    throw s!"correlation evidence targets kernel {bundle.kernelVersion}, Lean targets {A12Kernel.kernelVersion}"
  if bundle.cases.isEmpty then throw "correlation evidence bundle must contain at least one case"
  if hasDuplicate (bundle.cases.map (·.id)) then throw "duplicate correlation evidence case id"
  if hasDuplicate (bundle.cases.map (·.caseRef)) then throw "duplicate correlation evidence caseRef"
  bundle.cases.forM CaseSpec.validateTransport

end A12Kernel.Evidence.Correlation
