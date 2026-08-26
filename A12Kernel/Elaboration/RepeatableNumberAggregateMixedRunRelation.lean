import A12Kernel.Elaboration.RepeatableNumberAggregateMixedRun
import A12Kernel.Elaboration.ScalarComputationRunRelation

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

/-- A composite failure occurs either before aggregate completion or inside the
seeded mixed suffix. The suffix trace retains every successful scalar prefix,
while the aggregate seed remains outside the suffix outcome list. -/
inductive RepeatableNumberAggregateMixedRunFailureTrace
    (plan : CheckedRepeatableNumberAggregateMixedRun model)
    (world : World)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model) :
    RepeatableNumberAggregateMixedRunState →
      RepeatableNumberAggregateMixedRunFault → Prop where
  | cascade
      (fault : RepeatableNumberAggregateCascadeFault)
      (executed : plan.cascade.execute world input = .error fault) :
      RepeatableNumberAggregateMixedRunFailureTrace
        plan world patterns input {} (.cascade fault)
  | suffix
      (cascade : RepeatableNumberAggregateCascadeOutcomes)
      (outcomes : List ScalarComputationOutcome)
      (final : ScalarComputationRunState)
      (fault : ScalarComputationRunFault)
      (cascadeSuccess : RepeatableNumberAggregateMixedRunTransition
        plan world patterns input {}
        { aggregate := some cascade.aggregate.outcome })
      (failure : ScalarComputationRunFailureTrace plan.run world patterns input
        { completed := [.number {
            targetField := plan.cascade.total.operation.core.target.id
            outcome := cascade.aggregate.outcome
          }] }
        outcomes final fault) :
      RepeatableNumberAggregateMixedRunFailureTrace plan world patterns input
        { aggregate := some cascade.aggregate.outcome,
          scalars := final.outcomes.drop 1 }
        (.run fault)

end A12Kernel
