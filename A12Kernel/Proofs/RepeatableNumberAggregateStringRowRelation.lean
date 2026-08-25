import A12Kernel.Elaboration.RepeatableNumberAggregateStringRowRelation

/-! # Aggregate-to-repeatable String transition law -/

namespace A12Kernel

theorem repeatableNumberAggregateStringRow_transition_trace
    (plan : CheckedRepeatableNumberAggregateStringRowCascade model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (world : World)
    (input : CheckedDocument model)
    (outcomes : RepeatableNumberAggregateStringRowCascadeOutcomes)
    (executed : plan.execute world patterns input = .ok outcomes) :
    RepeatableNumberAggregateStringRowTransition plan patterns world input
      {} { aggregate := some outcomes.cascade.aggregate.outcome } ∧
    RepeatableNumberAggregateStringRowTransition plan patterns world input
      { aggregate := some outcomes.cascade.aggregate.outcome }
      { aggregate := some outcomes.cascade.aggregate.outcome,
        suffix := some outcomes.suffix } := by
  unfold CheckedRepeatableNumberAggregateStringRowCascade.execute at executed
  cases cascadeResult : plan.cascade.execute world input with
  | error cause =>
      simp [cascadeResult, Except.mapError, Bind.bind, Except.bind] at executed
  | ok cascade =>
      cases suffixResult : plan.suffix.executeWithRead patterns input
          (plan.readPolicy cascade.aggregate.outcome input) with
      | error cause =>
          simp [cascadeResult, suffixResult, Except.mapError,
            Bind.bind, Except.bind] at executed
      | ok suffix =>
          simp [cascadeResult, suffixResult, Except.mapError,
            Bind.bind, Except.bind] at executed
          cases executed
          exact ⟨.cascade cascade cascadeResult,
            .suffix cascade.aggregate.outcome suffix suffixResult⟩

end A12Kernel
