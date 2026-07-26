import A12Kernel.Elaboration.NumericComputation.Evaluation
import A12Kernel.Elaboration.ParallelComputationClearing

/-! # Isolated direct parallel Number run

This bounded capsule is the complete checked computation inventory for one unguarded direct Number copy across the already-checked exact-text parallel route. Because the run has exactly one computed target and the route's operand lies in a distinct group, the operand is a source field rather than an unresolved computed dependency. Execution enumerates existing target rows only, omits every target covered by an invalid-index post-loop mark, reads a clean unmatched operand as numeric zero, and retains each evaluated result at its exact target address. General expressions, guards, multi-computation scheduling, successful-result projection, clearing classification, and application remain separate. -/

namespace A12Kernel

inductive ParallelNumericDirectPlanError where
  | route (error : ParallelComputationPlanError)
  | operandFrameOutsideTarget (scope : List RepeatableLevel)
  | operationScaleMismatch (targetScale operandScale : Nat)
  deriving Repr, DecidableEq

/-- One exact target-addressed rich outcome from the direct parallel computation. -/
structure ParallelNumericDirectOutcome where
  address : CellAddr
  outcome : NumericTargetOutcome
  deriving Repr, DecidableEq

/-- The complete one-computation inventory for one checked unguarded direct-copy run over the existing parallel route certificate. -/
structure CheckedIsolatedParallelNumericDirectRun (model : FlatModel) where
  private mk ::
  route : CheckedParallelNumericClearingPlan model
  operandScopeAvailable : (match route.groups.outerScopePlan with
      | .framed .right _ _ => false
      | .common _ | .framed .left _ _ => true) = true
  operationScaleAdmitted :
    exactNumericScaleComparisonAllowed
      (.field route.target.info.scale)
      (.field route.operand.info.scale) = true

namespace CheckedIsolatedParallelNumericDirectRun

def WellFormed
    (checked : CheckedIsolatedParallelNumericDirectRun model) : Prop :=
  checked.route.WellFormed ∧
    (match checked.route.groups.outerScopePlan with
      | .framed .right _ _ => false
      | .common _ | .framed .left _ _ => true) = true ∧
    exactNumericScaleComparisonAllowed
      (.field checked.route.target.info.scale)
      (.field checked.route.operand.info.scale) = true

inductive ExecutionError where
  | marking (side : ParallelComputationIndexSide)
      (error : ParallelComputationMarkingError)
  | targetRows (error : ActualRowEnvironmentError)
  | environment (error : EnvBindingError)
  | indexColumn (side : ParallelComputationIndexSide)
      (error : CheckedIndexColumnError)
  | missingTargetIndex (address : CellAddr)
  | document (error : CheckedDocumentError)
  | numeric (error : NumericComputationFault)
  | unsupportedTarget (fault : NumericTargetCheckFault)
  deriving Repr, DecidableEq

private def targetAddress
    (checked : CheckedIsolatedParallelNumericDirectRun model)
    (environment : Env) : Except ExecutionError CellAddr := do
  let path ←
    environment.pathForScope checked.route.targetDeclaration.repeatableScope
      |>.mapError .environment
  pure { field := checked.route.targetField, path }

private def operandCell
    (checked : CheckedIsolatedParallelNumericDirectRun model)
    (preliminary : CheckedIndexPreliminary model)
    (targetEnvironment : Env) (key : SemanticIndexKey) :
    Except ExecutionError CheckedCell := do
  let operandColumn ←
    preliminary.resolveIndexColumn
      checked.route.groups.rightGroup targetEnvironment
      |>.mapError (ExecutionError.indexColumn .operand)
  match operandColumn.entries.find? fun entry => entry.key == key with
  | none => pure { rawPresent := false, parsed := none, findings := [] }
  | some entry =>
      let path ←
        entry.environment.pathForScope
          checked.route.operandDeclaration.repeatableScope
          |>.mapError .environment
      preliminary.base.read {
        field := checked.route.operandDeclaration.id
        path
      } |>.mapError .document

private def executeTarget
    (checked : CheckedIsolatedParallelNumericDirectRun model)
    (preliminary : CheckedIndexPreliminary model)
    (targetEnvironment : Env) :
    Except ExecutionError ParallelNumericDirectOutcome := do
  let address ← checked.targetAddress targetEnvironment
  let targetColumn ←
    preliminary.resolveIndexColumn
      checked.route.groups.leftGroup targetEnvironment
      |>.mapError (ExecutionError.indexColumn .target)
  let targetEntry ← match targetColumn.entries.find? fun entry =>
      entry.environment == targetEnvironment with
    | some entry => pure entry
    | none => throw (.missingTargetIndex address)
  let cell ← checked.operandCell preliminary
    targetEnvironment targetEntry.key
  let context : ScalarComputationContext := { read := fun _ => cell }
  let value ←
    context.readNumeric checked.route.operandDeclaration
      |>.mapError .numeric
  match checked.route.targetPolicy.check value with
  | .supported outcome => pure { address, outcome }
  | .unsupported fault => throw (.unsupportedTarget fault)

/-- Execute every existing target row not covered by either side's checked invalid-index marks. Collection order is the checked document's private canonicalization. -/
def execute
    (checked : CheckedIsolatedParallelNumericDirectRun model)
    (preliminary : CheckedIndexPreliminary model) :
    Except ExecutionError (List ParallelNumericDirectOutcome) := do
  let targetMarks ←
    checked.route.invalidIndexMarks preliminary .target
      |>.mapError (ExecutionError.marking .target)
  let operandMarks ←
    checked.route.invalidIndexMarks preliminary .operand
      |>.mapError (ExecutionError.marking .operand)
  let targetEnvironments ←
    checked.route.targetEnvironments preliminary.base
      |>.mapError .targetRows
  let candidates ← targetEnvironments.mapM fun targetEnvironment => do
    let coveredByTarget ←
      (checked.route.markPlanFor .target).coversAny
        targetEnvironment targetMarks
        |>.mapError ExecutionError.environment
    let coveredByOperand ←
      (checked.route.markPlanFor .operand).coversAny
        targetEnvironment operandMarks
        |>.mapError ExecutionError.environment
    if coveredByTarget || coveredByOperand then
      pure none
    else
      some <$> checked.executeTarget preliminary targetEnvironment
  pure (candidates.filterMap id)

end CheckedIsolatedParallelNumericDirectRun

/-- Check one unguarded direct Number copy without reimplementing the parallel route or the shared static scale gate. -/
def checkIsolatedParallelNumericDirectRun (model : FlatModel)
    (declaringGroup : GroupPath) (targetField : FieldId)
    (operandReference : SurfaceFieldPath) :
    Except ParallelNumericDirectPlanError
      (CheckedIsolatedParallelNumericDirectRun model) := do
  let route ←
    checkParallelNumericComputationClearingPlan
      model declaringGroup targetField operandReference
      |>.mapError .route
  if scopeAvailable :
      (match route.groups.outerScopePlan with
        | .framed .right _ _ => false
        | .common _ | .framed .left _ _ => true) = true then
    if admitted :
        exactNumericScaleComparisonAllowed
          (.field route.target.info.scale)
          (.field route.operand.info.scale) = true then
      pure (CheckedIsolatedParallelNumericDirectRun.mk
        route scopeAvailable admitted)
    else
      throw (.operationScaleMismatch
        route.target.info.scale route.operand.info.scale)
  else
    throw (.operandFrameOutsideTarget
      (model.repeatableScopeForGroupPath route.groups.rightGroup.path))

end A12Kernel
