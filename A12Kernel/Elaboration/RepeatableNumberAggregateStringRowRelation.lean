import A12Kernel.Elaboration.RepeatableNumberAggregateStringRowCascade

/-! # Aggregate-to-repeatable String transition relation -/

namespace A12Kernel

structure RepeatableNumberAggregateStringRowState where
  aggregate : Option NumericTargetOutcome := none
  suffix : Option (List (SourcedStringTargetOutcome CellAddr)) := none
  deriving Repr, DecidableEq

inductive RepeatableNumberAggregateStringRowTransition
    (plan : CheckedRepeatableNumberAggregateStringRowCascade model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (world : World)
    (input : CheckedDocument model) :
    RepeatableNumberAggregateStringRowState →
      RepeatableNumberAggregateStringRowState → Prop where
  | cascade
      (outcomes : RepeatableNumberAggregateCascadeOutcomes)
      (executed : plan.cascade.execute world input = .ok outcomes) :
      RepeatableNumberAggregateStringRowTransition plan patterns world input
        {} { aggregate := some outcomes.aggregate.outcome }
  | suffix
      (aggregate : NumericTargetOutcome)
      (outcomes : List (SourcedStringTargetOutcome CellAddr))
      (executed :
        plan.suffix.executeWithRead patterns input
          (plan.readPolicy aggregate input) = .ok outcomes) :
      RepeatableNumberAggregateStringRowTransition plan patterns world input
        { aggregate := some aggregate }
        { aggregate := some aggregate, suffix := some outcomes }

end A12Kernel
