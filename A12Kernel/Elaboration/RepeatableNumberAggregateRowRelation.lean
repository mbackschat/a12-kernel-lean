import A12Kernel.Elaboration.RepeatableNumberAggregateRowCascade

/-! # Aggregate-to-repeatable Number transition relation -/

namespace A12Kernel

structure RepeatableNumberAggregateRowState where
  aggregate : Option NumericTargetOutcome := none
  suffix : Option (List (SourcedNumericTargetOutcome CellAddr)) := none
  deriving Repr, DecidableEq

inductive RepeatableNumberAggregateRowTransition
    (plan : CheckedRepeatableNumberAggregateRowCascade model)
    (world : World)
    (input : CheckedDocument model) :
    RepeatableNumberAggregateRowState →
      RepeatableNumberAggregateRowState → Prop where
  | cascade
      (outcomes : RepeatableNumberAggregateCascadeOutcomes)
      (executed : plan.cascade.execute world input = .ok outcomes) :
      RepeatableNumberAggregateRowTransition plan world input
        {} { aggregate := some outcomes.aggregate.outcome }
  | suffix
      (aggregate : NumericTargetOutcome)
      (outcomes : List (SourcedNumericTargetOutcome CellAddr))
      (executed :
        plan.suffix.executeWithRead input
          (plan.readPolicy aggregate input) = .ok outcomes) :
      RepeatableNumberAggregateRowTransition plan world input
        { aggregate := some aggregate }
        { aggregate := some aggregate, suffix := some outcomes }

end A12Kernel
