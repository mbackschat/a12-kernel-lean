import A12Kernel.Elaboration.RepeatableNumberAggregateNumberToStringRelation

/-! # Aggregate-to-fixed repeatable Number-to-String transition law -/

namespace A12Kernel

theorem repeatableNumberAggregateNumberToString_transition_trace
    (plan : CheckedRepeatableNumberAggregateNumberToStringRowChain model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (world : World)
    (input : CheckedDocument model)
    (outcomes : RepeatableNumberAggregateNumberToStringRowChainOutcomes)
    (executed : plan.execute patterns world input = .ok outcomes) :
    RepeatableNumberAggregateNumberToStringTransition plan patterns world input
      {} { aggregate := some outcomes.cascade.aggregate.outcome } ∧
    RepeatableNumberAggregateNumberToStringTransition plan patterns world input
      { aggregate := some outcomes.cascade.aggregate.outcome }
      { aggregate := some outcomes.cascade.aggregate.outcome,
        suffix := some outcomes.suffix } := by
  unfold CheckedRepeatableNumberAggregateNumberToStringRowChain.execute at executed
  cases cascadeResult : plan.cascade.execute world input with
  | error cause =>
      simp [cascadeResult, Except.mapError, Bind.bind, Except.bind] at executed
  | ok cascade =>
      cases suffixResult : plan.suffix.executeWithRead patterns input
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
