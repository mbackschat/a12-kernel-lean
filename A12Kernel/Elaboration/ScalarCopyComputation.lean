import A12Kernel.Elaboration.DocumentComputationStep
import A12Kernel.Elaboration.Flat.ComputationBinding

namespace A12Kernel

/-- Same-kind Boolean/Confirm reads and component-compatible range reads implement the direct-copy comparison contract (spec/09 §1). -/
def scalarCopyCompatible (model : FlatModel) (target source : FlatFieldDecl) : Bool :=
  match target.policy.kind, source.policy.kind with
  | .boolean, .boolean | .confirm, .confirm => true
  | .dateRange, .dateRange => model.dateRangeComparisonProfilesMatch { id := target.id } { id := source.id }
  | _, _ => false

inductive ScalarCopyElabError where
  | resolve (cause : ResolveError)
  | placement (cause : AddressedRepeatableTargetElabError)
  | incompatible
  | targetReference
  | indexTarget
  deriving Repr, DecidableEq

/-- A direct scalar read retains its declaration and target-bound address instead of borrowing entity-list admission. -/
structure CheckedScalarCopyComputation (model : FlatModel) where
  private mk ::
  target : FlatFieldDecl
  source : FlatFieldDecl
  compatible : scalarCopyCompatible model target source = true
  bound : source.repetitionBoundBy target.repeatableScope = true
  distinct : source.id ≠ target.id

/-- Resolve at the lexical group and bind source repetitions at the target, as other computation carriers do. -/
def checkScalarCopyComputation (model : FlatModel) (group : GroupPath) (field : FieldId)
    (reference : SurfaceFieldPath) : Except ScalarCopyElabError (CheckedScalarCopyComputation model) := do
  let _ ← model.validate |>.mapError .resolve
  let target ← model.lookupUniqueId field |>.mapError .resolve
  if !GroupPath.isValid group then throw (.resolve (.invalidRuleGroup group))
  if model.isIndexField field then throw .indexTarget
  if !target.repeatableScope.isEmpty then
    let _ ← checkAddressedRepeatableTarget model group field |>.mapError .placement
  let source ← model.resolveComputationOperandUnchecked group target.groupPath reference |>.mapError .resolve
  if hDistinct : source.id = target.id then throw .targetReference
  else if hCompatible : scalarCopyCompatible model target source = true then
    if hBound : source.repetitionBoundBy target.repeatableScope = true then
      pure { target, source, compatible := hCompatible, bound := hBound, distinct := hDistinct }
    else throw .incompatible
  else throw .incompatible

inductive ScalarCopyFault where
  | environment (cause : EnvBindingError)
  | document (cause : CheckedDocumentError)
  | range (cause : DateRangeTargetEvaluationFault)
  | readBack (cause : DocumentComputationStepFault)
  deriving Repr, DecidableEq

namespace CheckedScalarCopyComputation

def family (operation : CheckedScalarCopyComputation model) : DocumentTargetFamily :=
  if operation.target.policy.kind == .dateRange then .dateRange else .boolean

/-- Observe exactly one source in the fresh document; formal failure and emptiness stay terminal after alternative selection (spec/09 §1). -/
def evaluateAt (operation : CheckedScalarCopyComputation model) (document : CheckedDocument model)
    (environment : Env) : Except ScalarCopyFault (DocumentTargetOutcome × CheckedCell) := do
  let path ← (environment.pathForScope operation.source.repeatableScope).mapError .environment
  let cell ← (document.read { field := operation.source.id, path }).mapError .document
  if operation.target.policy.kind == .dateRange then
    let result := dateRangeComputationCell cell
    let outcome ← (model.evaluateDateRangeTarget operation.target.id result).mapError .range
    let some policy := operation.target.toDateRangeDeclarationPolicy? | throw (.readBack .targetNotReadable)
    pure (.dateRange outcome, ← (DocumentComputationReadBack.dateRange model policy outcome).mapError .readBack)
  else
    let result : BooleanComputationOutcome := match observeCell .computation cell with
      | .value (.bool value) | .value (.conf value) => .value value
      | .empty => .noValue
      | .unknown cause | .poison cause => .poison cause
      | .value _ => .poison .malformed
    let kind := if operation.target.policy.kind == .confirm then BooleanConstantOperation.confirmTrue
      else .boolean false
    pure (.boolean result, DocumentComputationReadBack.booleanConstant kind result)

end CheckedScalarCopyComputation
end A12Kernel
