import A12Kernel.Elaboration.NumericComputation.Evaluation
import A12Kernel.Elaboration.ParallelComputationClearing

/-! # Isolated direct parallel Number run

This bounded capsule is the complete checked computation inventory for one unguarded direct Number copy across the already-checked exact-text parallel route. Because the run has exactly one computed target and the route's operand lies in a distinct group, the operand is a source field rather than an unresolved computed dependency. Execution enumerates existing target rows only, omits every target covered by an invalid-index post-loop mark, reads a clean unmatched operand as numeric zero, and retains each evaluated result at its exact target address. General expressions, guards, multi-computation scheduling, successful-result projection, clearing classification, and application remain separate. -/

namespace A12Kernel

inductive ParallelNumericDirectPlanError where
  | route (error : ParallelComputationPlanError)
  | guardNotLimitedToOperand
  | operandFrameOutsideTarget (scope : List RepeatableLevel)
  | operationScaleMismatch (targetScale operandScale : Nat)
  deriving Repr, DecidableEq

/-- Whether an optional bounded guard reads only the route's already-joined operand. -/
def parallelNumericDirectGuardAdmitted
    (operand : FieldId) : Option ComputationCondition → Bool
  | none => true
  | some condition => referencesOnly condition
where
  referencesOnly : ComputationCondition → Bool
    | .leaf (.fieldFilled field) | .leaf (.fieldNotFilled field) =>
        field == operand
    | .and left right | .or left right =>
        referencesOnly left && referencesOnly right

/-- One exact target-addressed rich outcome from the direct parallel computation. -/
structure ParallelNumericDirectOutcome where
  address : CellAddr
  outcome : NumericTargetOutcome
  deriving Repr, DecidableEq

/-- The complete one-computation inventory for one checked unguarded direct-copy run over the existing parallel route certificate. -/
structure CheckedIsolatedParallelNumericDirectRun (model : FlatModel) where
  private mk ::
  route : CheckedParallelNumericClearingPlan model
  precondition : Option ComputationCondition
  guardAdmitted :
    parallelNumericDirectGuardAdmitted
      route.operandDeclaration.id precondition = true
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
    parallelNumericDirectGuardAdmitted
      checked.route.operandDeclaration.id checked.precondition = true ∧
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
    (targetEnvironment : Env) (address : CellAddr) :
    Except ExecutionError ParallelNumericDirectOutcome := do
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
  let guardResult := match checked.precondition with
    | none => ComputationConditionResult.holds
    | some guard => guard.eval context
  match guardResult with
  | .notTrue => pure { address, outcome := .noValue }
  | .poison cause =>
      pure { address, outcome := .inheritedPoison cause }
  | .holds =>
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
  let coverage ←
    checked.route.targetCoverage preliminary
      |>.mapError fun
        | .marking side error => .marking side error
        | .targetRows error => .targetRows error
        | .targetEnvironment error => .environment error
  let candidates ← coverage.mapM fun target => do
    if target.indexInvalid then
      pure none
    else
      some <$> checked.executeTarget preliminary
        target.environment target.address
  pure (candidates.filterMap id)

end CheckedIsolatedParallelNumericDirectRun

/-- Check one optionally guarded direct Number copy without reimplementing the parallel route or the shared static scale gate. Every guard leaf must reuse the already-joined operand read. -/
def checkIsolatedParallelNumericDirectRunWithGuard (model : FlatModel)
    (declaringGroup : GroupPath) (targetField : FieldId)
    (operandReference : SurfaceFieldPath)
    (precondition : Option ComputationCondition) :
    Except ParallelNumericDirectPlanError
      (CheckedIsolatedParallelNumericDirectRun model) := do
  let route ←
    checkParallelNumericComputationClearingPlan
      model declaringGroup targetField operandReference
      |>.mapError .route
  if guardAdmitted :
      parallelNumericDirectGuardAdmitted
        route.operandDeclaration.id precondition = true then
    if scopeAvailable :
        (match route.groups.outerScopePlan with
          | .framed .right _ _ => false
          | .common _ | .framed .left _ _ => true) = true then
      if admitted :
          exactNumericScaleComparisonAllowed
            (.field route.target.info.scale)
            (.field route.operand.info.scale) = true then
        pure (CheckedIsolatedParallelNumericDirectRun.mk
          route precondition guardAdmitted scopeAvailable admitted)
      else
        throw (.operationScaleMismatch
          route.target.info.scale route.operand.info.scale)
    else
      throw (.operandFrameOutsideTarget
        (model.repeatableScopeForGroupPath route.groups.rightGroup.path))
  else
    throw .guardNotLimitedToOperand

/-- Check the original unguarded direct-copy fragment. -/
def checkIsolatedParallelNumericDirectRun (model : FlatModel)
    (declaringGroup : GroupPath) (targetField : FieldId)
    (operandReference : SurfaceFieldPath) :
    Except ParallelNumericDirectPlanError
      (CheckedIsolatedParallelNumericDirectRun model) :=
  checkIsolatedParallelNumericDirectRunWithGuard model declaringGroup
    targetField operandReference none

end A12Kernel
