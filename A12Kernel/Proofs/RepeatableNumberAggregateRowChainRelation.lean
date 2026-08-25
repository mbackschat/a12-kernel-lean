import A12Kernel.Elaboration.RepeatableNumberAggregateRowChainRelation

/-! # Aggregate-to-fixed repeatable Number-chain transition law -/

namespace A12Kernel

theorem repeatableNumberAggregateRowChain_transition_trace
    (plan : CheckedRepeatableNumberAggregateRowChain model)
    (world : World)
    (input : CheckedDocument model)
    (cascadeOutcomes : RepeatableNumberAggregateCascadeOutcomes)
    (suffixOutcomes : CurrentRepetitionNumberCascadeOutcomes)
    (cascadeExecuted : plan.cascade.execute world input = .ok cascadeOutcomes)
    (suffixExecuted :
      plan.suffix.executeWithRead input
        (plan.cascade.readCompletion cascadeOutcomes.aggregate.outcome input) =
          .ok suffixOutcomes) :
    RepeatableNumberAggregateRowChainTransition plan world input
      {} { aggregate := some cascadeOutcomes.aggregate.outcome } ∧
    RepeatableNumberAggregateRowChainTransition plan world input
      { aggregate := some cascadeOutcomes.aggregate.outcome }
      { aggregate := some cascadeOutcomes.aggregate.outcome,
        suffix := some suffixOutcomes } := by
  exact ⟨.cascade cascadeOutcomes cascadeExecuted,
    .suffix cascadeOutcomes.aggregate.outcome suffixOutcomes suffixExecuted⟩

end A12Kernel
