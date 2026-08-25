import A12Kernel.Elaboration.RepeatableNumberAggregateStringRowCascade

/-! # Aggregate-to-repeatable String laws -/

namespace A12Kernel

@[simp]
theorem checkedRepeatableNumberAggregateStringRowCascade_analyze
    (plan : CheckedRepeatableNumberAggregateStringRowCascade model) :
    plan.analyze = {
      cascade := plan.cascade.analyze
      suffixTarget := plan.suffix.targetField
      repeatableScope := plan.suffix.targetDeclaration.repeatableScope
      fieldDependencies := plan.cascade.analyze.fieldDependencies ++ [
        (plan.suffix.targetField, [plan.suffix.sourceDeclaration.id])]
    } := by
  rfl

@[simp]
theorem repeatableNumberAggregateStringRowCascade_read_completed
    (plan : CheckedRepeatableNumberAggregateStringRowCascade model)
    (outcome : NumericTargetOutcome) (input : CheckedDocument model) :
    plan.readPolicy outcome input plan.aggregateAddress =
      .ok (StringDependencyCell.ofNumericOutcome outcome).checked := by
  simp [CheckedRepeatableNumberAggregateStringRowCascade.readPolicy]

theorem repeatableNumberAggregateStringRowCascade_read_input
    (plan : CheckedRepeatableNumberAggregateStringRowCascade model)
    (outcome : NumericTargetOutcome) (input : CheckedDocument model)
    (address : CellAddr) (ordinary : address ≠ plan.aggregateAddress) :
    plan.readPolicy outcome input address =
      CheckedAddressedFieldValueAsString.readSource input address := by
  simp [CheckedRepeatableNumberAggregateStringRowCascade.readPolicy, ordinary]

end A12Kernel
