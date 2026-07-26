import A12Kernel.Semantics.ParallelComputationClearing

/-! # Parallel-computation clearing locks -/

namespace A12Kernel.Conformance.ParallelComputationClearing

open A12Kernel

private def targetScope : List RepeatableLevel := [10, 20, 30]
private def offPathParentScope : List RepeatableLevel := [10, 40]
private def onPathParentScope : List RepeatableLevel := [10, 20]

private def firstSibling : Env := [(10, 1), (20, 1), (30, 1)]
private def secondSibling : Env := [(10, 1), (20, 2), (30, 1)]

private def offPathPlan :=
  ParallelComputationMarkPlan.ofScopes targetScope offPathParentScope

private def onPathPlan :=
  ParallelComputationMarkPlan.ofScopes targetScope onPathParentScope

private def mark? (plan : ParallelComputationMarkPlan)
    (cause : Option FormalCause) (targetEnvironment : Env) :
    Option (ParallelComputationMark plan) :=
  (plan.markForUnavailable cause targetEnvironment).toOption.bind id

private def covered? (plan : ParallelComputationMarkPlan)
    (mark : Option (ParallelComputationMark plan))
    (targetEnvironment : Env) : Option Bool := do
  let mark ← mark
  (plan.covers mark targetEnvironment).toOption

private def markError? (plan : ParallelComputationMarkPlan)
    (targetEnvironment : Env) : Option EnvBindingError :=
  match plan.markForUnavailable (some .duplicateIndex) targetEnvironment with
  | .error error => some error
  | .ok _ => none

/- A clean column emits no post-loop mark. The cause subclass of an invalid column is deliberately erased. -/
example :
    mark? offPathPlan none firstSibling = none ∧
    mark? offPathPlan (some .duplicateIndex) firstSibling =
      mark? offPathPlan (some .required) firstSibling := by
  native_decide

/- An off-path malformed index shares only the outer coordinate and therefore marks both sibling target rows. -/
example :
    let mark := mark? offPathPlan (some .duplicateIndex) firstSibling
    covered? offPathPlan mark firstSibling = some true ∧
      covered? offPathPlan mark secondSibling = some true := by
  native_decide

/- An on-path malformed index retains the sibling coordinate, so the clean sibling survives. -/
example :
    let mark := mark? onPathPlan (some .duplicateIndex) firstSibling
    covered? onPathPlan mark firstSibling = some true ∧
      covered? onPathPlan mark secondSibling = some false := by
  native_decide

/- Missing target coordinates remain structural rather than becoming a broad semantic mark. -/
example :
    markError? offPathPlan [(10, 1)] = some (.missingBinding 20) := by
  native_decide

end A12Kernel.Conformance.ParallelComputationClearing
