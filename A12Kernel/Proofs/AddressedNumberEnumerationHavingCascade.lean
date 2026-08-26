import A12Kernel.Elaboration.AddressedNumberEnumerationHavingCascade

/-! # Number dependency inside Enumeration `Having` laws -/

namespace A12Kernel

/-- The checked route retains the exact filter-only dependency that makes the consumer a later stage. -/
theorem addressedNumberEnumerationHavingCascade_filterDependency
    (plan : CheckedAddressedNumberEnumerationHavingCascade model) :
    plan.havingDependencies.contains plan.producer.placement.targetField = true :=
  plan.filterDependency

/-- Analyze exposes the producer edge and complete downstream checked-plan inventory without adding runtime reachability. -/
@[simp]
theorem addressedNumberEnumerationHavingCascade_analyze
    (plan : CheckedAddressedNumberEnumerationHavingCascade model) :
    plan.analyze = {
      producerTarget := plan.producer.placement.targetField
      consumerTarget := plan.consumer.target.field
      fieldDependencies := [
        (plan.producer.placement.targetField,
          [plan.producer.placement.sourceDeclaration.id]),
        (plan.consumer.target.field,
          plan.consumer.source.fieldDependencies)]
    } := by
  rfl

/-- Execution delegates exactly to the completed Number phase followed by the Enumeration consumer over that phase's transient dependency cells. -/
theorem addressedNumberEnumerationHavingCascade_execute_delegates
    (plan : CheckedAddressedNumberEnumerationHavingCascade model)
    (input : CheckedDocument model) :
    plan.execute input = (do
      let producer ← plan.producer.execute input |>.mapError
        AddressedNumberEnumerationHavingCascadeFault.producer
      let consumer ← plan.consumer.executeWithRead input
          (readAfterNumericDependencies input producer) |>.mapError
            AddressedNumberEnumerationHavingCascadeFault.consumer
      pure { producer, consumer }) := by
  rfl

end A12Kernel
