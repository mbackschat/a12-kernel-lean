import A12Kernel.Elaboration.RepeatableNumberAggregateCascadeRelation
import A12Kernel.Proofs.NumericComputationRunRelation

/-! # Row-to-aggregate transition laws -/

namespace A12Kernel

/-- Every successful core cascade is exactly one row phase followed by one
aggregate phase over those same rich row outcomes. -/
theorem repeatableNumberAggregateCascade_execute_transition_trace
    (plan : CheckedRepeatableNumberAggregateCascade model)
    (world : World)
    (input : CheckedDocument model)
    (outcomes : RepeatableNumberAggregateCascadeOutcomes)
    (executed : plan.execute world input = .ok outcomes) :
    RepeatableNumberAggregateCascadeTransition plan world input
        {} { rows := some outcomes.rows } ∧
      RepeatableNumberAggregateCascadeTransition plan world input
        { rows := some outcomes.rows }
        { rows := some outcomes.rows,
          aggregate := some outcomes.aggregate } := by
  unfold CheckedRepeatableNumberAggregateCascade.execute at executed
  cases rowResult : plan.row.execute input with
  | error cause =>
      simp [rowResult, Except.mapError, Bind.bind, Except.bind] at executed
  | ok rows =>
      cases aggregateResult :
          plan.executeAggregateAfterRows world input rows with
      | error cause =>
          simp [rowResult, aggregateResult, Except.mapError,
            Bind.bind, Except.bind] at executed
      | ok aggregate =>
          simp [rowResult, aggregateResult, Except.mapError,
            Bind.bind, Except.bind] at executed
          cases executed
          exact ⟨.rows rows rowResult,
            .aggregate rows aggregate aggregateResult⟩

/-- The first successful core-cascade transition can only complete the rows;
an aggregate requires that retained row state. -/
theorem repeatableNumberAggregateCascade_initial_transition_has_no_aggregate
    (transition : RepeatableNumberAggregateCascadeTransition
      plan world input {} next) :
    next.aggregate = none := by
  cases transition with
  | rows => rfl

private theorem repeatableNumberAggregateRunCascade_aggregateTarget_not_runTarget
    (plan : CheckedRepeatableNumberAggregateRunCascade model) :
    plan.cascade.total.operation.core.target.id ∉ plan.run.targetFields := by
  intro member
  have distinct := List.all_eq_true.mp plan.distinctTargets
    plan.cascade.total.operation.core.target.id member
  simp at distinct

/-- Every successful aggregate-seeded finite Number execution has an exact
suffix trace whose labels exclude the retained aggregate seed. -/
theorem repeatableNumberAggregateRunCascade_execute_trace
    (plan : CheckedRepeatableNumberAggregateRunCascade model)
    (world : World)
    (input : CheckedDocument model)
    (outcomes : RepeatableNumberAggregateRunCascadeOutcomes)
    (executed : plan.execute world input = .ok outcomes) :
    ∃ final,
      NumericComputationRunTrace plan.run world input
        { completed := [{
            targetField := plan.cascade.total.operation.core.target.id
            outcome := outcomes.cascade.aggregate.outcome
          }] }
        outcomes.scalars final := by
  unfold CheckedRepeatableNumberAggregateRunCascade.execute at executed
  cases cascadeResult : plan.cascade.execute world input with
  | error cause =>
      simp [cascadeResult, Except.mapError, Bind.bind, Except.bind] at executed
  | ok cascade =>
      cases suffixResult : plan.run.executeTables world input plan.run.tables {
          completed := [{
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
          have seedDisjoint :
              ∀ target ∈ [plan.cascade.total.operation.core.target.id],
                target ∉ plan.run.targetFields := by
            intro target member
            simp only [List.mem_singleton] at member
            subst target
            exact
              repeatableNumberAggregateRunCascade_aggregateTarget_not_runTarget
                plan
          obtain ⟨labels, trace, appended⟩ :=
            numericComputationRun_executeTables_seeded_trace
              plan.run world input
              [plan.cascade.total.operation.core.target.id]
              [] plan.run.tables {
                completed := [{
                  targetField := plan.cascade.total.operation.core.target.id
                  outcome := cascade.aggregate.outcome
                }]
              } final seedDisjoint (by simp)
              (by simp [NumericComputationRunState.targetFields]) suffixResult
          have labelsFinal : labels = final.outcomes.drop 1 := by
            have dropped := congrArg (List.drop 1) appended
            simpa [NumericComputationRunState.outcomes] using dropped
          exact ⟨final, by simpa [labelsFinal] using trace⟩

end A12Kernel
