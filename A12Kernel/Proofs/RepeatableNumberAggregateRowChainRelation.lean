import A12Kernel.Elaboration.RepeatableNumberAggregateRowChainRelation

/-! # Aggregate-to-fixed repeatable Number-chain transition law -/

namespace A12Kernel

theorem repeatableNumberAggregateRowChain_transition_trace
    (plan : CheckedRepeatableNumberAggregateRowChain model)
    (world : World)
    (input : CheckedDocument model)
    (outcomes : RepeatableNumberAggregateRowChainOutcomes)
    (executed : plan.execute world input = .ok outcomes) :
    RepeatableNumberAggregateRowChainTransition plan world input
      {} { aggregate := some outcomes.cascade.aggregate.outcome } ∧
    RepeatableNumberAggregateRowChainTransition plan world input
      { aggregate := some outcomes.cascade.aggregate.outcome }
      { aggregate := some outcomes.cascade.aggregate.outcome,
        suffix := some outcomes.suffix } := by
  unfold CheckedRepeatableNumberAggregateRowChain.execute at executed
  cases cascadeResult : plan.cascade.execute world input with
  | error cause =>
      simp [cascadeResult, Except.mapError, Bind.bind, Except.bind] at executed
  | ok cascade =>
      cases suffixResult : plan.suffix.executeWithRead input
          (plan.cascade.readCompletion cascade.aggregate.outcome input) with
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
