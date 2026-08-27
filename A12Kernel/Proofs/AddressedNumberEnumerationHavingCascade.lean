import A12Kernel.Elaboration.AddressedNumberEnumerationHavingCascade
import A12Kernel.Proofs.AddressedEnumerationComputation

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

/-- Result projection reuses the two established family owners over the exact already-sourced phases. -/
theorem addressedNumberEnumerationHavingCascade_executeResult_projects
    (plan : CheckedAddressedNumberEnumerationHavingCascade model)
    (input : CheckedDocument model)
    (numberPayloadAt : CellAddr → NumberPayload)
    (numberMessages : List (ComputationFormalMessage NumberPayload))
    (stringResidualMessages : List StringResidual)
    (producer : List (SourcedNumericTargetOutcome CellAddr))
    (enumeration : AddressedEnumerationFirstFilledComputationRunView
      model StringResidual)
    (producerExecuted : plan.producer.execute input = .ok producer)
    (enumerationExecuted : plan.consumer.executeResultWithRead input
      (readAfterNumericDependencies input producer) stringResidualMessages =
        .ok enumeration) :
    plan.executeResult input numberPayloadAt numberMessages
      stringResidualMessages = .ok {
        number := NumericComputationRunView.fromSourceOutcomesWithMessages
          MessagePointer.ofCellAddr numberPayloadAt numberMessages producer
        enumeration
  } := by
  unfold CheckedAddressedNumberEnumerationHavingCascade.executeResult
  rw [producerExecuted]
  change (do
    let result ← plan.consumer.executeResultWithRead input
        (readAfterNumericDependencies input producer) stringResidualMessages
      |>.mapError AddressedNumberEnumerationHavingCascadeFault.consumer
    pure ({
      number := NumericComputationRunView.fromSourceOutcomesWithMessages
        MessagePointer.ofCellAddr numberPayloadAt numberMessages producer
      enumeration := result
    } : AddressedNumberEnumerationHavingCascadeRunView
      model NumberPayload StringResidual)) = _
  rw [enumerationExecuted]
  rfl

end A12Kernel
