import A12Kernel.Elaboration.RepeatableNumberAggregateCascade

/-! # Row-to-aggregate transition relation

This purpose-specific relation exposes the two successful phases of the core
repeatable Number cascade. It retains exact rich row outcomes before the root
aggregate is available and reuses the executor's aggregate-phase owner.
-/

namespace A12Kernel

structure RepeatableNumberAggregateCascadeState where
  rows : Option (List (SourcedNumericTargetOutcome CellAddr)) := none
  aggregate : Option (SourcedNumericTargetOutcome CellAddr) := none
  deriving Repr, DecidableEq

inductive RepeatableNumberAggregateCascadeTransition
    (plan : CheckedRepeatableNumberAggregateCascade model)
    (world : World)
    (input : CheckedDocument model) :
    RepeatableNumberAggregateCascadeState →
      RepeatableNumberAggregateCascadeState → Prop where
  | rows
      (outcomes : List (SourcedNumericTargetOutcome CellAddr))
      (executed : plan.row.execute input = .ok outcomes) :
      RepeatableNumberAggregateCascadeTransition plan world input
        {} { rows := some outcomes }
  | aggregate
      (rows : List (SourcedNumericTargetOutcome CellAddr))
      (outcome : SourcedNumericTargetOutcome CellAddr)
      (executed :
        plan.executeAggregateAfterRows world input rows = .ok outcome) :
      RepeatableNumberAggregateCascadeTransition plan world input
        { rows := some rows }
        { rows := some rows, aggregate := some outcome }

end A12Kernel
