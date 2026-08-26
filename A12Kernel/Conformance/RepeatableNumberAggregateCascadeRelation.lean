import A12Kernel.Proofs.RepeatableNumberAggregateCascadeRelation

/-! # Repeatable Number aggregate transition locks -/

namespace A12Kernel.Conformance.RepeatableNumberAggregateCascadeRelation

open A12Kernel

/- A successful core cascade retains its exact rows before adding the aggregate. -/
example (plan : CheckedRepeatableNumberAggregateCascade model)
    (world : World) (input : CheckedDocument model)
    (outcomes : RepeatableNumberAggregateCascadeOutcomes)
    (executed : plan.execute world input = .ok outcomes) :
    RepeatableNumberAggregateCascadeTransition plan world input
        {} { rows := some outcomes.rows } ∧
      RepeatableNumberAggregateCascadeTransition plan world input
        { rows := some outcomes.rows }
        { rows := some outcomes.rows, aggregate := some outcomes.aggregate } :=
  repeatableNumberAggregateCascade_execute_transition_trace
    plan world input outcomes executed

/- The aggregate cannot appear in the first transition. -/
example (transition : RepeatableNumberAggregateCascadeTransition
    plan world input {} next) :
    next.aggregate = none :=
  repeatableNumberAggregateCascade_initial_transition_has_no_aggregate
    transition

/- A retained aggregate completion stays outside successful finite Number suffix labels. -/
example (plan : CheckedRepeatableNumberAggregateRunCascade model)
    (world : World) (input : CheckedDocument model)
    (outcomes : RepeatableNumberAggregateRunCascadeOutcomes)
    (executed : plan.execute world input = .ok outcomes) :
    ∃ final,
      NumericComputationRunTrace plan.run world input
        { completed := [{
            targetField := plan.cascade.total.operation.core.target.id
            outcome := outcomes.cascade.aggregate.outcome
          }] }
        outcomes.scalars final :=
  repeatableNumberAggregateRunCascade_execute_trace
    plan world input outcomes executed

end A12Kernel.Conformance.RepeatableNumberAggregateCascadeRelation
