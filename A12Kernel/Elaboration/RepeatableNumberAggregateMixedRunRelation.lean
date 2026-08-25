import A12Kernel.Elaboration.RepeatableNumberAggregateMixedRun

/-! # Purpose-specific aggregate-to-suffix transition relation -/

namespace A12Kernel

structure RepeatableNumberAggregateMixedRunState where
  aggregate : Option NumericTargetOutcome := none
  scalars : List ScalarComputationOutcome := []
  deriving Repr, DecidableEq

inductive RepeatableNumberAggregateMixedRunTransition
    (plan : CheckedRepeatableNumberAggregateMixedRun model)
    (world : World)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model) :
    RepeatableNumberAggregateMixedRunState →
      RepeatableNumberAggregateMixedRunState → Prop where
  | cascade
      (outcomes : RepeatableNumberAggregateCascadeOutcomes)
      (executed : plan.cascade.execute world input = .ok outcomes) :
      RepeatableNumberAggregateMixedRunTransition plan world patterns input
        {} { aggregate := some outcomes.aggregate.outcome }
  | suffix
      (aggregate : NumericTargetOutcome)
      (result : ScalarComputationRunState)
      (executed :
        plan.run.executeSteps world patterns input plan.run.steps {
          completed := [.number {
            targetField := plan.cascade.total.operation.core.target.id
            outcome := aggregate
          }]
        } = .ok result) :
      RepeatableNumberAggregateMixedRunTransition plan world patterns input
        { aggregate := some aggregate }
        { aggregate := some aggregate, scalars := result.outcomes.drop 1 }

end A12Kernel
