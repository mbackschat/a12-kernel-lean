import A12Kernel.Elaboration.RepeatableNumberAggregateRowCascade

/-! # Aggregate-to-fixed repeatable Number-chain transition relation -/

namespace A12Kernel

structure RepeatableNumberAggregateRowChainState where
  aggregate : Option NumericTargetOutcome := none
  suffix : Option CurrentRepetitionNumberCascadeOutcomes := none
  deriving Repr, DecidableEq

inductive RepeatableNumberAggregateRowChainTransition
    (plan : CheckedRepeatableNumberAggregateRowChain model)
    (world : World)
    (input : CheckedDocument model) :
    RepeatableNumberAggregateRowChainState →
      RepeatableNumberAggregateRowChainState → Prop where
  | cascade
      (outcomes : RepeatableNumberAggregateCascadeOutcomes)
      (executed : plan.cascade.execute world input = .ok outcomes) :
      RepeatableNumberAggregateRowChainTransition plan world input
        {} { aggregate := some outcomes.aggregate.outcome }
  | suffix
      (aggregate : NumericTargetOutcome)
      (outcomes : CurrentRepetitionNumberCascadeOutcomes)
      (executed :
        plan.suffix.executeWithRead input
          (plan.cascade.readCompletion aggregate input) = .ok outcomes) :
      RepeatableNumberAggregateRowChainTransition plan world input
        { aggregate := some aggregate }
        { aggregate := some aggregate, suffix := some outcomes }

end A12Kernel
