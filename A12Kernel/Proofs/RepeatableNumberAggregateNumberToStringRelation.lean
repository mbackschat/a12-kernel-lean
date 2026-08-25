import A12Kernel.Elaboration.RepeatableNumberAggregateNumberToStringRelation

/-! # Aggregate-to-fixed repeatable Number-to-String transition law -/

namespace A12Kernel

theorem repeatableNumberAggregateNumberToString_transition_trace
    (plan : CheckedRepeatableNumberAggregateNumberToStringRowChain model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (world : World)
    (input : CheckedDocument model)
    (cascadeOutcomes : RepeatableNumberAggregateCascadeOutcomes)
    (suffixOutcomes : CurrentRepetitionNumberToStringOutcomes)
    (cascadeExecuted : plan.cascade.execute world input = .ok cascadeOutcomes)
    (suffixExecuted :
      plan.suffix.executeWithRead patterns input
        (plan.cascade.readCompletion cascadeOutcomes.aggregate.outcome input) =
          .ok suffixOutcomes) :
    RepeatableNumberAggregateNumberToStringTransition plan patterns world input
      {} { aggregate := some cascadeOutcomes.aggregate.outcome } ∧
    RepeatableNumberAggregateNumberToStringTransition plan patterns world input
      { aggregate := some cascadeOutcomes.aggregate.outcome }
      { aggregate := some cascadeOutcomes.aggregate.outcome,
        suffix := some suffixOutcomes } := by
  exact ⟨.cascade cascadeOutcomes cascadeExecuted,
    .suffix cascadeOutcomes.aggregate.outcome suffixOutcomes suffixExecuted⟩

end A12Kernel
