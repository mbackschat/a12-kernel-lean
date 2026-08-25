import A12Kernel.Elaboration.RepeatableNumberAggregateRowRelation

/-! # Aggregate-to-repeatable Number transition law -/

namespace A12Kernel

theorem repeatableNumberAggregateRow_transition_trace
    (plan : CheckedRepeatableNumberAggregateRowCascade model)
    (world : World)
    (input : CheckedDocument model)
    (outcomes : RepeatableNumberAggregateRowCascadeOutcomes)
    (executed : plan.execute world input = .ok outcomes) :
    RepeatableNumberAggregateRowTransition plan world input
      {} { aggregate := some outcomes.cascade.aggregate.outcome } ∧
    RepeatableNumberAggregateRowTransition plan world input
      { aggregate := some outcomes.cascade.aggregate.outcome }
      { aggregate := some outcomes.cascade.aggregate.outcome,
        suffix := some outcomes.suffix } := by
  unfold CheckedRepeatableNumberAggregateRowCascade.execute at executed
  cases cascadeResult : plan.cascade.execute world input with
  | error cause =>
      simp [cascadeResult, Except.mapError, Bind.bind, Except.bind] at executed
  | ok cascade =>
      cases suffixResult : plan.suffix.executeWithRead input
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
