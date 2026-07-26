import A12Kernel.Semantics.ParallelComputationClearing

/-! # Parallel-computation clearing laws -/

namespace A12Kernel

@[simp] theorem commonRepeatablePrefix_prefix_left
    (left right : List RepeatableLevel) :
    (commonRepeatablePrefix left right).isPrefixOf left = true := by
  induction left generalizing right with
  | nil => rfl
  | cons level remaining induction =>
      cases right with
      | nil => rfl
      | cons rightLevel rightRemaining =>
          by_cases same : level = rightLevel
          · subst rightLevel
            simp [commonRepeatablePrefix, induction]
          · simp [commonRepeatablePrefix, same]

@[simp] theorem commonRepeatablePrefix_prefix_right
    (left right : List RepeatableLevel) :
    (commonRepeatablePrefix left right).isPrefixOf right = true := by
  induction left generalizing right with
  | nil => rfl
  | cons level remaining induction =>
      cases right with
      | nil => rfl
      | cons rightLevel rightRemaining =>
          by_cases same : level = rightLevel
          · subst rightLevel
            simp [commonRepeatablePrefix, induction]
          · simp [commonRepeatablePrefix, same]

theorem parallelComputationMark_sharedScope
    (targetScope malformedIndexParentScope : List RepeatableLevel) :
    (ParallelComputationMarkPlan.ofScopes
      targetScope malformedIndexParentScope).sharedScope =
        commonRepeatablePrefix targetScope malformedIndexParentScope := by
  rfl

/-- The index failure subclass does not enter the post-loop invalidity key. -/
theorem parallelComputationMark_causeBlind
    (plan : ParallelComputationMarkPlan)
    (first second : FormalCause) (targetEnvironment : Env) :
    plan.markForUnavailable (some first) targetEnvironment =
      plan.markForUnavailable (some second) targetEnvironment := by
  rfl

/-- The instance from which an invalid mark is derived is always inside that mark's blast radius. -/
theorem parallelComputationMark_covers_source
    (plan : ParallelComputationMarkPlan)
    (cause : FormalCause) (targetEnvironment : Env)
    (mark : ParallelComputationMark plan)
    (marked :
      plan.markForUnavailable (some cause) targetEnvironment =
        .ok (some mark)) :
    plan.covers mark targetEnvironment = .ok true := by
  cases resolved : targetEnvironment.pathForScope plan.targetScope with
  | error fault =>
      simp_all [ParallelComputationMarkPlan.markForUnavailable]
  | ok path =>
      simp [ParallelComputationMarkPlan.markForUnavailable, resolved] at marked
      have coordinates := congrArg
        (fun candidate : ParallelComputationMark plan =>
          candidate.coordinates) marked
      simp at coordinates
      simp [ParallelComputationMarkPlan.covers, resolved, coordinates]

end A12Kernel
