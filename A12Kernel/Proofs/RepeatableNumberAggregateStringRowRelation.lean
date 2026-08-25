import A12Kernel.Elaboration.RepeatableNumberAggregateStringRowRelation

/-! # Aggregate-to-repeatable String transition law -/

namespace A12Kernel

theorem repeatableNumberAggregateStringRow_transition_trace
    (plan : CheckedRepeatableNumberAggregateStringRowCascade model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (world : World)
    (input : CheckedDocument model)
    (cascadeOutcomes : RepeatableNumberAggregateCascadeOutcomes)
    (suffixOutcomes : List (SourcedStringTargetOutcome CellAddr))
    (cascadeExecuted : plan.cascade.execute world input = .ok cascadeOutcomes)
    (suffixExecuted :
      plan.suffix.executeWithRead patterns input
        (plan.readPolicy cascadeOutcomes.aggregate.outcome input) =
          .ok suffixOutcomes) :
    RepeatableNumberAggregateStringRowTransition plan patterns world input
      {} { aggregate := some cascadeOutcomes.aggregate.outcome } ∧
    RepeatableNumberAggregateStringRowTransition plan patterns world input
      { aggregate := some cascadeOutcomes.aggregate.outcome }
      { aggregate := some cascadeOutcomes.aggregate.outcome,
        suffix := some suffixOutcomes } := by
  exact ⟨.cascade cascadeOutcomes cascadeExecuted,
    .suffix cascadeOutcomes.aggregate.outcome suffixOutcomes suffixExecuted⟩

end A12Kernel
