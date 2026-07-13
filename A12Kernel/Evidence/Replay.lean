import A12Kernel.Basic
import A12Kernel.Elaboration.Flat
import A12Kernel.Evidence.Schema
import A12Kernel.Semantics.Required

/-! # A12Kernel.Evidence.Replay — pure projection replay

The external boundary observes emitted message signatures, not the evaluator's internal
`unknown`/`notFired` distinction. Replay therefore projects both of those verdicts to no
authored emission and preserves VALUE/OMISSION only when the focused rule fires.
-/

namespace A12Kernel.Evidence

open A12Kernel

private def FieldKindSpec.toPolicyKind : FieldKindSpec → FieldKind
  | .number scale signed => .number { scale, signed }
  | .boolean => .boolean
  | .confirm => .confirm

private def FieldSpec.toDeclaration (field : FieldSpec) : FlatFieldDecl :=
  { id := field.id
    groupPath := field.groups
    name := field.name
    policy := { kind := field.kind.toPolicyKind } }

private def PathSpec.toSurface (path : PathSpec) : SurfaceFieldPath :=
  { base := match path.base with
      | .absolute => .absolute
      | .relative parents => .relative parents
    groups := path.groups
    field := path.field }

private def LiteralSpec.toSurface : LiteralSpec → SurfaceLiteral
  | .number value => .number value
  | .boolean value => .boolean value

private def comparisonOf (name : String) : Except String SurfaceComparisonOp :=
  match name with
  | "equal" => pure .equal
  | "notEqual" => pure .notEqual
  | other => throw s!"unsupported comparison '{other}'"

private def ConditionSpec.toSurface : ConditionSpec → Except String SurfaceCondition
  | .compare comparison path literal => do
      pure (.compare (← comparisonOf comparison) path.toSurface literal.toSurface)
  | .fieldNotFilled path => pure (.fieldNotFilled path.toSurface)
  | .and left right => do pure (.and (← left.toSurface) (← right.toSurface))
  | .or left right => do pure (.or (← left.toSurface) (← right.toSurface))

private def CellStateSpec.toRaw : CellStateSpec → RawCell
  | .empty => .empty
  | .number value => .parsed (.num value)
  | .boolean value => .parsed (.bool value)
  | .confirm value => .parsed (.conf value)
  | .rejected => .rejected .malformed

private def findCell (cells : List CellSpec) (id : FieldId) : Option CellSpec :=
  match cells with
  | [] => none
  | cell :: rest => if cell.fieldId = id then some cell else findCell rest id

private def CaseSpec.rawContext (case : CaseSpec) : RawFlatContext where
  read id := (findCell case.cells id).map (·.state.toRaw) |>.getD .empty

private def CaseSpec.model (case : CaseSpec) : FlatModel :=
  { fields := case.fields.map FieldSpec.toDeclaration
    fieldRefByShortNameAllowed := true }

private def signature (code pointer : String) : Verdict → List String
  | .fired .value => [s!"{code}|VALUE_ERROR|{pointer}"]
  | .fired .omission => [s!"{code}|OMISSION_ERROR|{pointer}"]
  | .notFired | .unknown => []

private def hasDuplicate [BEq α] (values : List α) : Bool :=
  match values with
  | [] => false
  | value :: rest => rest.contains value || hasDuplicate rest

private def CaseSpec.validateTransport (case : CaseSpec) : Except String Unit := do
  if case.id.isEmpty then throw "evidence case id must not be empty"
  if case.caseRef.isEmpty then throw s!"{case.id}: caseRef must not be empty"
  if case.focusCode.isEmpty then throw s!"{case.id}: focusCode must not be empty"
  if case.fields.isEmpty then throw s!"{case.id}: fields must not be empty"
  if hasDuplicate (case.fields.map (·.id)) then throw s!"{case.id}: duplicate field id"
  if hasDuplicate (case.cells.map (·.fieldId)) then throw s!"{case.id}: duplicate cell id"
  for cell in case.cells do
    if !(case.fields.any (·.id == cell.fieldId)) then
      throw s!"{case.id}: cell references undeclared field {cell.fieldId}"
  match case.model.validate with
  | .ok _ => pure ()
  | .error error => throw s!"{case.id}: invalid projected model: {repr error}"

private def CaseSpec.replayFlat (case : CaseSpec) (declaringGroup : List String)
    (condition : ConditionSpec) (hasContent : Bool) : Except String (List String) := do
  let surface ← condition.toSurface
  match elaborateAndEvalFull case.model declaringGroup case.rawContext hasContent surface with
  | .ok verdict => pure (signature case.focusCode case.focusPointer verdict)
  | .error error => throw s!"{case.id}: elaboration failed: {repr error}"

private def FlatFieldDecl.toFlatField (declaration : FlatFieldDecl) : FlatField :=
  match declaration.policy.kind with
  | .number info => .number { id := declaration.id, info }
  | .boolean => .boolean { id := declaration.id }
  | .confirm => .confirm { id := declaration.id }

private def CaseSpec.replayRequired (case : CaseSpec) (targetFieldId : FieldId) :
    Except String (List String) := do
  let declaration ← match case.model.lookupUniqueId targetFieldId with
    | .ok declaration => pure declaration
    | .error error => throw s!"{case.id}: required target lookup failed: {repr error}"
  let result := applyAbsoluteRequired declaration.toFlatField
    (case.model.checkContext case.rawContext)
  pure (signature case.focusCode case.focusPointer result.mandatoryVerdict)

def CaseSpec.replay (case : CaseSpec) : Except String (List String) := do
  case.validateTransport
  match case.operation with
  | .flat declaringGroup condition hasContent =>
      case.replayFlat declaringGroup condition hasContent
  | .absoluteRequired targetFieldId => case.replayRequired targetFieldId

def Bundle.validate (bundle : Bundle) : Except String Unit := do
  if bundle.schemaVersion != 1 then
    throw s!"unsupported evidence schema version {bundle.schemaVersion}"
  if bundle.kernelVersion != A12Kernel.kernelVersion then
    throw s!"evidence targets kernel {bundle.kernelVersion}, Lean targets {A12Kernel.kernelVersion}"
  if bundle.cases.isEmpty then throw "evidence bundle must contain at least one case"
  if hasDuplicate (bundle.cases.map (·.id)) then throw "duplicate evidence case id"
  if hasDuplicate (bundle.cases.map (·.caseRef)) then throw "duplicate evidence caseRef"
  bundle.cases.forM CaseSpec.validateTransport

end A12Kernel.Evidence
