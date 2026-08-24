import A12Kernel.Elaboration.RepeatableNumberAggregateRowCascade

/-! # Aggregate-to-repeatable Number cascade laws -/

namespace A12Kernel

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
  simp [CheckedRepeatableNumberAggregateRowCascade.readPolicy]

theorem repeatableNumberAggregateRowCascade_read_input
    (plan : CheckedRepeatableNumberAggregateRowCascade model)
    (outcome : NumericTargetOutcome) (input : CheckedDocument model)
    (address : CellAddr) (ordinary : address ≠ plan.aggregateAddress) :
    plan.readPolicy outcome input address = input.read address := by
  simp [CheckedRepeatableNumberAggregateRowCascade.readPolicy, ordinary]

end A12Kernel
