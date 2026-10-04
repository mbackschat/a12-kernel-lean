import A12Kernel.Elaboration.NumericComputation.Evaluation

/-! # Checked numeric-computation target attachment -/

namespace A12Kernel

private def FlatModel.resolveNumericComputationTargetPolicy
    (model : FlatModel) (target : FieldId) :
    Except NumericComputationElabError NumericTargetPolicy := do
  let declaration ← model.lookupUniqueId target |>.mapError .targetResolve
  match declaration.policy.kind, declaration.toNumericTargetPolicy? with
  | .number _, some policy => pure policy
  | .number _, none => throw .incoherentCore
  | _, _ => throw (.targetNotNumber target)

/-- Resolve the complete computation surface and attach the target declaration's complete Number policy in one checked construction. -/
def elaborateCompleteNumericTargetComputationOperation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (expression : AuthoredNumericExpr SurfaceNumericComputationAtom)
    (suppressExactScaleWarning : Bool := false)
    (targetScope : ComputationTargetScope := .fixed) :
    Except NumericComputationElabError
      (CheckedNumericTargetComputationOperation model) := do
  let operation ← elaborateCompleteNumericComputationOperation
    model declaringGroup targetField expression suppressExactScaleWarning targetScope
  operation.attachTargetPolicy
    (← model.resolveNumericComputationTargetPolicy targetField)

/-- Resolve a direct/plain-star/filtered-star entity-list computation and retain the target declaration's complete Number policy. -/
def elaborateNumberEntityTargetComputationOperation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (expression :
      AuthoredNumericExpr (SurfaceNumericAtom SurfaceNumberEntitySource))
    (suppressExactScaleWarning : Bool := false) :
    Except NumericComputationElabError
      (CheckedNumericTargetComputationOperation model) :=
  elaborateCompleteNumericTargetComputationOperation model declaringGroup
    targetField (expression.map SurfaceNumericComputationAtom.numeric)
    suppressExactScaleWarning

/-- Backwards-compatible direct-field aggregate surface whose checked target policy comes solely from the validated declaration. -/
def elaborateNumericTargetComputationOperation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (expression : AuthoredNumericExpr SurfaceNumericAtom)
    (suppressExactScaleWarning : Bool := false) :
    Except NumericComputationElabError
      (CheckedNumericTargetComputationOperation model) :=
  elaborateNumberEntityTargetComputationOperation model declaringGroup
    targetField
    (expression.map SurfaceNumericAtom.toNumberEntityComputationAtom)
    suppressExactScaleWarning

namespace CheckedNumericTargetComputationOperation

/-- A selected band changes only the store attempt; an unbanded operation keeps its original
warning-suppression policy (spec/09). The authored expression remains available for validation. -/
def checkResult (operation : CheckedNumericTargetComputationOperation model)
    (result : NumericComputationResult) : NumericTargetCheckResult :=
  match operation.bandedRounding with
  | some mode => operation.policy.checkBanded mode result
  | none => if operation.operation.core.suppressExactScaleWarning then
      operation.policy.checkWithScaleWarningSuppressed result
    else operation.policy.check result

/-- Evaluate the authored expression before applying its retained output policy. -/
def evaluate (operation : CheckedNumericTargetComputationOperation model)
    (context : ScalarComputationContext) :
    Except NumericComputationFault NumericTargetCheckResult := do
  pure (operation.checkResult (← operation.operation.evaluate context))

/-- Preserve the same retained target-policy dispatch after repeatable expression evaluation. Source-relative target policy and result classification are not recomputed or reordered. -/
def evaluateIn (operation : CheckedNumericTargetComputationOperation model)
    (context : NumericComputationEvaluationContext) :
    Except NumericComputationFault NumericTargetCheckResult := do
  pure (operation.checkResult (← operation.operation.evaluateIn context))

end CheckedNumericTargetComputationOperation

end A12Kernel
