import A12Kernel.Elaboration.RepeatableNumberAggregateMixedRunRelation

/-! # Aggregate-to-suffix transition correspondence -/

namespace A12Kernel

theorem repeatableNumberAggregateMixedRun_transition_trace
    (plan : CheckedRepeatableNumberAggregateMixedRun model)
    (world : World)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model)
    (cascadeOutcomes : RepeatableNumberAggregateCascadeOutcomes)
    (result : ScalarComputationRunState)
    (cascadeExecuted : plan.cascade.execute world input = .ok cascadeOutcomes)
    (suffixExecuted :
      plan.run.executeSteps world patterns input plan.run.steps {
        completed := [.number {
          targetField := plan.cascade.total.operation.core.target.id
          outcome := cascadeOutcomes.aggregate.outcome
        }]
      } = .ok result) :
    RepeatableNumberAggregateMixedRunTransition plan world patterns input
      {} { aggregate := some cascadeOutcomes.aggregate.outcome } ∧
    RepeatableNumberAggregateMixedRunTransition plan world patterns input
      { aggregate := some cascadeOutcomes.aggregate.outcome }
      { aggregate := some cascadeOutcomes.aggregate.outcome,
        scalars := result.outcomes.drop 1 } := by
  exact ⟨.cascade cascadeOutcomes cascadeExecuted,
    .suffix cascadeOutcomes.aggregate.outcome result suffixExecuted⟩

end A12Kernel
