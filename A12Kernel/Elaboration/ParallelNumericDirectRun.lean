import A12Kernel.Elaboration.NumericComputation.Evaluation
import A12Kernel.Elaboration.ParallelComputationClearing

/-! # Isolated direct parallel Number run

This bounded capsule checks one optionally guarded Number expression whose every field atom is the already-joined operand of one exact-text parallel route. It reuses the shared authored numeric tree, lowering, operation admission, authoring rules, scale summary, target policy, and evaluator; the route remains the sole owner of addressed reads and invalid-index disposition. Because the run has exactly one computed target and the route's operand lies in a distinct group, the operand is a source field rather than an unresolved computed dependency. Execution enumerates existing target rows only, omits every target covered by an invalid-index post-loop mark, reads a clean unmatched operand as numeric zero, and retains each evaluated result at its exact target address. Other operand fields, warning suppression, multi-computation scheduling, and broader repeatable overlays remain separate. -/

namespace A12Kernel

inductive ParallelNumericDirectPlanError where
  | route (error : ParallelComputationPlanError)
  | guardNotLimitedToOperand
  | expressionResolve (error : ResolveError)
  | expressionNotLimitedToOperand
  | unsupportedExpression
  | authoring (result : NumericAuthoringCheck)
  | operandFrameOutsideTarget (scope : List RepeatableLevel)
  | operationScaleMismatch
      (targetScale : Nat) (operation : NumericScaleSummary)
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
  expression : AuthoredNumericExpr FlatFieldDecl
  guardAdmitted :
    parallelNumericDirectGuardAdmitted
      route.operandDeclaration.id precondition = true
  expressionUsesOperand : expression.hasAtom = true
  expressionOperandsOwned :
    expression.allAtoms (· == route.operandDeclaration) = true
  expressionAdmitted :
    expression.isAdmittedResolvedNumericOperation = true
  expressionAuthoring :
    expression.numericOperationAuthoringCheck = .accepted
  operandScopeAvailable : (match route.groups.outerScopePlan with
      | .framed .right _ _ => false
      | .common _ | .framed .left _ _ => true) = true
  operationScale : NumericScaleSummary
  operationScaleOwned :
    expression.summary? FlatFieldDecl.numericScaleSummary =
      some operationScale
  operationScaleAdmitted :
    exactNumericScaleComparisonAllowed
      (.field route.target.info.scale)
      operationScale = true

namespace CheckedIsolatedParallelNumericDirectRun

def WellFormed
    (checked : CheckedIsolatedParallelNumericDirectRun model) : Prop :=
  checked.route.WellFormed ∧
    parallelNumericDirectGuardAdmitted
      checked.route.operandDeclaration.id checked.precondition = true ∧
    checked.expression.hasAtom = true ∧
    checked.expression.allAtoms
      (· == checked.route.operandDeclaration) = true ∧
    checked.expression.isAdmittedResolvedNumericOperation = true ∧
    checked.expression.numericOperationAuthoringCheck = .accepted ∧
    (match checked.route.groups.outerScopePlan with
      | .framed .right _ _ => false
      | .common _ | .framed .left _ _ => true) = true ∧
    checked.expression.summary? FlatFieldDecl.numericScaleSummary =
      some checked.operationScale ∧
    exactNumericScaleComparisonAllowed
      (.field checked.route.target.info.scale)
      checked.operationScale = true

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
      let value ← checked.expression.evaluateComputation context
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

/-- Resolve one bounded expression atom to the route-owned operand. This is a certificate construction over the shared numeric tree, not a second evaluator or addressing path. -/
private def FlatModel.resolveParallelNumericDirectExpression
    (model : FlatModel) (declaringGroup : GroupPath)
    (route : CheckedParallelNumericClearingPlan model)
    (expression : AuthoredNumericExpr SurfaceNumericAtom) :
    Except ParallelNumericDirectPlanError
      (AuthoredNumericExpr FlatFieldDecl) :=
  expression.mapM fun
    | .field reference => do
        let declaration ←
          model.resolveFieldDeclarationUnchecked declaringGroup reference
            |>.mapError ParallelNumericDirectPlanError.expressionResolve
        if declaration == route.operandDeclaration then
          pure declaration
        else
          throw .expressionNotLimitedToOperand
    | _ => throw .expressionNotLimitedToOperand

/-- Check one optionally guarded Number operation without reimplementing the parallel route, numeric lowering, operation admission, authoring checks, or scale gate. Every field atom and guard leaf must reuse the already-joined operand read. -/
def checkIsolatedParallelNumericExpressionRunWithGuard (model : FlatModel)
    (declaringGroup : GroupPath) (targetField : FieldId)
    (operandReference : SurfaceFieldPath)
    (expression : AuthoredNumericExpr SurfaceNumericAtom)
    (precondition : Option ComputationCondition) :
    Except ParallelNumericDirectPlanError
      (CheckedIsolatedParallelNumericDirectRun model) := do
  let route ←
    checkParallelNumericComputationClearingPlan
      model declaringGroup targetField operandReference
      |>.mapError .route
  let resolved ←
    model.resolveParallelNumericDirectExpression
      declaringGroup route expression
  if usesOperand : resolved.hasAtom = true then
    if operandsOwned :
        resolved.allAtoms (· == route.operandDeclaration) = true then
      if expressionAdmitted :
          resolved.isAdmittedResolvedNumericOperation = true then
        match authoring : resolved.numericOperationAuthoringCheck with
        | .accepted =>
          match scaleOwned :
              resolved.summary? FlatFieldDecl.numericScaleSummary with
          | none => throw .unsupportedExpression
          | some operationScale =>
            if guardAdmitted :
                parallelNumericDirectGuardAdmitted
                  route.operandDeclaration.id precondition = true then
              if scopeAvailable :
                  (match route.groups.outerScopePlan with
                    | .framed .right _ _ => false
                    | .common _ | .framed .left _ _ => true) = true then
                if scaleAdmitted :
                    exactNumericScaleComparisonAllowed
                      (.field route.target.info.scale)
                      operationScale = true then
                  pure (CheckedIsolatedParallelNumericDirectRun.mk
                    route precondition resolved guardAdmitted usesOperand
                    operandsOwned expressionAdmitted authoring scopeAvailable
                    operationScale scaleOwned scaleAdmitted)
                else
                  throw (.operationScaleMismatch
                    route.target.info.scale operationScale)
              else
                throw (.operandFrameOutsideTarget
                  (model.repeatableScopeForGroupPath
                    route.groups.rightGroup.path))
            else
              throw .guardNotLimitedToOperand
        | result => throw (.authoring result)
      else
        throw .unsupportedExpression
    else
      throw .expressionNotLimitedToOperand
  else
    throw .expressionNotLimitedToOperand

/-- Check one optionally guarded direct Number copy as the atom-only specialization of the shared expression route. -/
def checkIsolatedParallelNumericDirectRunWithGuard (model : FlatModel)
    (declaringGroup : GroupPath) (targetField : FieldId)
    (operandReference : SurfaceFieldPath)
    (precondition : Option ComputationCondition) :
    Except ParallelNumericDirectPlanError
      (CheckedIsolatedParallelNumericDirectRun model) :=
  checkIsolatedParallelNumericExpressionRunWithGuard model declaringGroup
    targetField operandReference (.atom (.field operandReference)) precondition

/-- Check the original unguarded direct-copy fragment. -/
def checkIsolatedParallelNumericDirectRun (model : FlatModel)
    (declaringGroup : GroupPath) (targetField : FieldId)
    (operandReference : SurfaceFieldPath) :
    Except ParallelNumericDirectPlanError
      (CheckedIsolatedParallelNumericDirectRun model) :=
  checkIsolatedParallelNumericDirectRunWithGuard model declaringGroup
    targetField operandReference none

end A12Kernel
