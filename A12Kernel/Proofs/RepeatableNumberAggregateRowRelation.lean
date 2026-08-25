import A12Kernel.Elaboration.RepeatableNumberAggregateRowRelation

/-! # Aggregate-to-repeatable Number transition law -/

namespace A12Kernel

theorem repeatableNumberAggregateRow_transition_trace
    (plan : CheckedRepeatableNumberAggregateRowCascade model)
    (world : World)
    (input : CheckedDocument model)
    (cascadeOutcomes : RepeatableNumberAggregateCascadeOutcomes)
    (suffixOutcomes : List (SourcedNumericTargetOutcome CellAddr))
    (cascadeExecuted : plan.cascade.execute world input = .ok cascadeOutcomes)
    (suffixExecuted :
      plan.suffix.executeWithRead input
        (plan.readPolicy cascadeOutcomes.aggregate.outcome input) =
          .ok suffixOutcomes) :
    RepeatableNumberAggregateRowTransition plan world input
      {} { aggregate := some cascadeOutcomes.aggregate.outcome } ∧
    RepeatableNumberAggregateRowTransition plan world input
      { aggregate := some cascadeOutcomes.aggregate.outcome }
      { aggregate := some cascadeOutcomes.aggregate.outcome,
        suffix := some suffixOutcomes } := by
  exact ⟨.cascade cascadeOutcomes cascadeExecuted,
    .suffix cascadeOutcomes.aggregate.outcome suffixOutcomes suffixExecuted⟩

end A12Kernel
