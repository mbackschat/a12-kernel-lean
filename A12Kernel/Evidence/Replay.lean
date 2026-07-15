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

private def findRawCell (cells : List (FieldId × RawCell)) (id : FieldId) : Option RawCell :=
  match cells with
  | [] => none
  | (fieldId, raw) :: rest => if fieldId = id then some raw else findRawCell rest id

private def CaseSpec.model (case : CaseSpec) : FlatModel :=
  { fields := case.fields.map FieldSpec.toDeclaration
    fieldRefByShortNameAllowed := case.fieldRefByShortNameAllowed }

private def CaseSpec.rawContext (case : CaseSpec) : RawFlatContext where
  read id := (case.cells.find? (·.fieldId == id)).map (·.state.toRaw) |>.getD .empty

/-- The canonical typed input shared by retained-evidence replay and the normalized
    protocol bridge. Explicit evidence `empty` cells are removed because protocol-v1
    represents clean emptiness by sparse omission. -/
structure FlatReplayInput where
  model : FlatModel
  declaringGroup : GroupPath
  condition : SurfaceCondition
  cells : List (FieldId × RawCell)
  hasContent : Bool
  deriving Repr, DecidableEq

namespace FlatReplayInput

private def rawContext (input : FlatReplayInput) : RawFlatContext where
  read id := (findRawCell input.cells id).getD .empty

def replay (input : FlatReplayInput) : Except String Verdict :=
  match elaborateAndEvalFull input.model input.declaringGroup input.rawContext
      input.hasContent input.condition with
  | .ok verdict => pure verdict
  | .error error => throw s!"flat evidence elaboration failed: {repr error}"

end FlatReplayInput

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

def CaseSpec.toFlatReplayInput (case : CaseSpec) : Except String FlatReplayInput := do
  case.validateTransport
  let (declaringGroup, condition, hasContent) ← match case.operation with
    | .flat declaringGroup condition hasContent => pure (declaringGroup, condition, hasContent)
    | _ => throw s!"{case.id}: expected a flat evidence operation"
  let cells := case.cells.filterMap fun cell =>
    match cell.state with
    | .empty => none
    | state => some (cell.fieldId, state.toRaw)
  pure {
    model := case.model
    declaringGroup
    condition := ← condition.toSurface
    cells
    hasContent }

private def CaseSpec.replayRequired (case : CaseSpec) (targetFieldId : FieldId) :
    Except String (List String) := do
  let declaration ← match case.model.lookupUniqueId targetFieldId with
    | .ok declaration => pure declaration
    | .error error => throw s!"{case.id}: required target lookup failed: {repr error}"
  let field ← match declaration.toPresenceField? with
    | some field => pure field
    | none => throw s!"{case.id}: required target kind is outside the retained presence fragment"
  let result := applyAbsoluteRequired field (case.model.checkContext case.rawContext)
  pure (signature case.focusCode case.focusPointer result.mandatoryVerdict)

private def resolveErrorCode : ResolveError → Option String
  | .invalidEntity _ => some "MVK_INVALID_ENTITY"
  | .shortNameNotUnique _ => some "MVK_FIELDNAME_NOT_UNIQUE"
  | _ => none

private def CaseSpec.replayResolve (case : CaseSpec) (declaringGroup : List String)
    (path : PathSpec) : Except String (List String) :=
  match case.model.resolveField declaringGroup path.toSurface with
  | .ok declaration => throw s!"{case.id}: expected resolution rejection, resolved {declaration.path}"
  | .error error => match resolveErrorCode error with
      | some code => pure [code]
      | none => throw s!"{case.id}: unsupported projected resolution error: {repr error}"

def CaseSpec.replay (case : CaseSpec) : Except String (List String) := do
  match case.operation with
  | .flat _ _ _ =>
      let verdict ← (← case.toFlatReplayInput).replay
      pure (signature case.focusCode case.focusPointer verdict)
  | .absoluteRequired targetFieldId =>
      case.validateTransport
      case.replayRequired targetFieldId
  | .resolve declaringGroup path =>
      case.validateTransport
      case.replayResolve declaringGroup path

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
