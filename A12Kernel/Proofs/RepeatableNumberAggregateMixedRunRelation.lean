import A12Kernel.Elaboration.RepeatableNumberAggregateMixedRunRelation
import A12Kernel.Proofs.ScalarComputationRunRelation

/-! # Aggregate-to-suffix transition correspondence -/

namespace A12Kernel

private theorem repeatableNumberAggregateMixedRun_aggregateTarget_not_runTarget
    (plan : CheckedRepeatableNumberAggregateMixedRun model) :
    plan.cascade.total.operation.core.target.id ∉ plan.run.targetFields := by
  intro member
  have distinct := List.all_eq_true.mp plan.distinctTargets
    plan.cascade.total.operation.core.target.id member
  simp at distinct

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

/-- Every composite execution fault is either an aggregate-prefix fault or a
seeded scalar-suffix failure that preserves its successful scalar prefix. -/
theorem repeatableNumberAggregateMixedRun_execute_failure_trace
    (plan : CheckedRepeatableNumberAggregateMixedRun model)
    (world : World)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model)
    (fault : RepeatableNumberAggregateMixedRunFault)
    (executed : plan.execute world patterns input = .error fault) :
    ∃ state,
      RepeatableNumberAggregateMixedRunFailureTrace
        plan world patterns input state fault := by
  unfold CheckedRepeatableNumberAggregateMixedRun.execute at executed
  cases cascadeResult : plan.cascade.execute world input with
  | error cause =>
      simp [cascadeResult, Except.mapError, Bind.bind, Except.bind] at executed
      cases executed
      exact ⟨{}, .cascade cause cascadeResult⟩
  | ok cascade =>
      let initial : ScalarComputationRunState := {
        completed := [.number {
          targetField := plan.cascade.total.operation.core.target.id
          outcome := cascade.aggregate.outcome
        }]
      }
      cases suffixResult : plan.run.executeSteps world patterns input
          plan.run.steps initial with
      | error cause =>
          simp [initial, cascadeResult, suffixResult, Except.mapError,
            Bind.bind, Except.bind] at executed
          cases executed
          have seedDisjoint :
              ∀ target ∈ [plan.cascade.total.operation.core.target.id],
                target ∉ plan.run.targetFields := by
            intro target member
            simp only [List.mem_singleton] at member
            subst target
            exact
              repeatableNumberAggregateMixedRun_aggregateTarget_not_runTarget
                plan
          obtain ⟨outcomes, final, failure, _appended⟩ :=
            scalarComputationRun_executeSteps_seeded_failureTrace
              plan.run world patterns input
              [plan.cascade.total.operation.core.target.id]
              [] plan.run.steps initial cause seedDisjoint (by simp)
              (by simp [initial, ScalarComputationRunState.targetFields,
                ScalarComputationCompletion.targetField])
              suffixResult
          exact ⟨{
              aggregate := some cascade.aggregate.outcome
              scalars := final.outcomes.drop 1
            }, .suffix cascade outcomes final cause
              (.cascade cascade cascadeResult) failure⟩
      | ok final =>
          simp [initial, cascadeResult, suffixResult, Except.mapError,
            Bind.bind, Except.bind, pure, Except.pure] at executed

end A12Kernel
