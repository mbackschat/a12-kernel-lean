import A12Kernel.Elaboration.RepeatableNumberAggregateRowCascade

/-! # Aggregate-to-repeatable Number cascade laws -/

namespace A12Kernel

@[simp]
theorem repeatableNumberAggregateCascade_read_completed
    (cascade : CheckedRepeatableNumberAggregateCascade model)
    (outcome : NumericTargetOutcome) (input : CheckedDocument model) :
    cascade.readCompletion outcome input cascade.aggregateAddress =
      .ok (NumericDependencyCell.ofOutcome outcome).checked := by
  simp [CheckedRepeatableNumberAggregateCascade.readCompletion]

theorem repeatableNumberAggregateCascade_read_input
    (cascade : CheckedRepeatableNumberAggregateCascade model)
    (outcome : NumericTargetOutcome) (input : CheckedDocument model)
    (address : CellAddr) (ordinary : address ≠ cascade.aggregateAddress) :
    cascade.readCompletion outcome input address = input.read address := by
  simp [CheckedRepeatableNumberAggregateCascade.readCompletion, ordinary]

@[simp]
theorem checkedRepeatableNumberAggregateRowCascade_analyze
    (plan : CheckedRepeatableNumberAggregateRowCascade model) :
    plan.analyze = {
      cascade := plan.cascade.analyze
      suffixTarget := plan.suffix.placement.targetField
      repeatableScope := plan.suffix.placement.targetDeclaration.repeatableScope
      fieldDependencies := plan.cascade.analyze.fieldDependencies ++ [
        (plan.suffix.placement.targetField,
          [plan.suffix.placement.sourceDeclaration.id])]
    } := by
  rfl

@[simp]
theorem repeatableNumberAggregateRowCascade_read_completed
    (plan : CheckedRepeatableNumberAggregateRowCascade model)
    (outcome : NumericTargetOutcome) (input : CheckedDocument model) :
    plan.readPolicy outcome input plan.aggregateAddress =
      .ok (NumericDependencyCell.ofOutcome outcome).checked := by
  exact repeatableNumberAggregateCascade_read_completed
    plan.cascade outcome input

theorem repeatableNumberAggregateRowCascade_read_input
    (plan : CheckedRepeatableNumberAggregateRowCascade model)
    (outcome : NumericTargetOutcome) (input : CheckedDocument model)
    (address : CellAddr) (ordinary : address ≠ plan.aggregateAddress) :
    plan.readPolicy outcome input address = input.read address := by
  exact repeatableNumberAggregateCascade_read_input
    plan.cascade outcome input address ordinary

@[simp]
theorem checkedRepeatableNumberAggregateRowChain_analyze
    (plan : CheckedRepeatableNumberAggregateRowChain model) :
    plan.analyze = {
      cascade := plan.cascade.analyze
      suffix := plan.suffix.analyze
    } := by
  rfl

@[simp]
theorem checkedRepeatableNumberAggregateNumberToStringRowChain_analyze
    (plan : CheckedRepeatableNumberAggregateNumberToStringRowChain model) :
    plan.analyze = {
      cascade := plan.cascade.analyze
      suffix := plan.suffix.analyze
    } := by
  rfl

end A12Kernel
