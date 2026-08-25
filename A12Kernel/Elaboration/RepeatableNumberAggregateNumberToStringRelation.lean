import A12Kernel.Elaboration.RepeatableNumberAggregateRowCascade

/-! # Aggregate-to-fixed repeatable Number-to-String transition relation -/

namespace A12Kernel

structure RepeatableNumberAggregateNumberToStringState where
  aggregate : Option NumericTargetOutcome := none
  suffix : Option CurrentRepetitionNumberToStringOutcomes := none
  deriving Repr, DecidableEq

inductive RepeatableNumberAggregateNumberToStringTransition
    (plan : CheckedRepeatableNumberAggregateNumberToStringRowChain model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (world : World)
    (input : CheckedDocument model) :
    RepeatableNumberAggregateNumberToStringState →
      RepeatableNumberAggregateNumberToStringState → Prop where
  | cascade
      (outcomes : RepeatableNumberAggregateCascadeOutcomes)
      (executed : plan.cascade.execute world input = .ok outcomes) :
      RepeatableNumberAggregateNumberToStringTransition plan patterns world input
        {} { aggregate := some outcomes.aggregate.outcome }
  | suffix
      (aggregate : NumericTargetOutcome)
      (outcomes : CurrentRepetitionNumberToStringOutcomes)
      (executed :
        plan.suffix.executeWithRead patterns input
          (plan.cascade.readCompletion aggregate input) = .ok outcomes) :
      RepeatableNumberAggregateNumberToStringTransition plan patterns world input
        { aggregate := some aggregate }
        { aggregate := some aggregate, suffix := some outcomes }

end A12Kernel
