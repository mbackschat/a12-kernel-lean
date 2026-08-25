import A12Kernel.Elaboration.RepeatableNumberAggregateMixedRunRelation

/-! # Aggregate-to-suffix transition correspondence -/

namespace A12Kernel

theorem repeatableNumberAggregateMixedRun_transition_trace
    (plan : CheckedRepeatableNumberAggregateMixedRun model)
    (world : World)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model)
    (outcomes : RepeatableNumberAggregateMixedRunOutcomes)
    (executed : plan.execute world patterns input = .ok outcomes) :
    RepeatableNumberAggregateMixedRunTransition plan world patterns input
      {} { aggregate := some outcomes.cascade.aggregate.outcome } ∧
    RepeatableNumberAggregateMixedRunTransition plan world patterns input
      { aggregate := some outcomes.cascade.aggregate.outcome }
      { aggregate := some outcomes.cascade.aggregate.outcome,
        scalars := outcomes.scalars } := by
  unfold CheckedRepeatableNumberAggregateMixedRun.execute at executed
  cases cascadeResult : plan.cascade.execute world input with
  | error cause =>
      simp [cascadeResult, Except.mapError, Bind.bind, Except.bind] at executed
  | ok cascade =>
      cases suffixResult : plan.run.executeSteps world patterns input
          plan.run.steps {
            completed := [.number {
              targetField := plan.cascade.total.operation.core.target.id
              outcome := cascade.aggregate.outcome
            }]
          } with
      | error cause =>
          simp [cascadeResult, suffixResult, Except.mapError,
            Bind.bind, Except.bind] at executed
      | ok final =>
          simp [cascadeResult, suffixResult, Except.mapError,
            Bind.bind, Except.bind] at executed
          cases executed
          constructor
          · exact .cascade cascade cascadeResult
          · simpa [List.drop_one] using
              (RepeatableNumberAggregateMixedRunTransition.suffix
                cascade.aggregate.outcome final suffixResult)

end A12Kernel
