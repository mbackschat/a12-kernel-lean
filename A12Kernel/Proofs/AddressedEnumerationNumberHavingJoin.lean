import A12Kernel.Elaboration.AddressedEnumerationNumberHavingJoin
import A12Kernel.Proofs.AddressedEnumerationComputation

/-! # Computed Enumeration value plus Number `Having` laws -/

namespace A12Kernel

/-- The checked route retains the direct Enumeration producer edge used by Analyze. -/
theorem addressedEnumerationNumberHavingJoin_enumerationSourceDirect
    (plan : CheckedAddressedEnumerationNumberHavingJoin model) :
    directAddressedEnumerationSourceField? plan.enumerationProducer.source =
      some plan.enumerationSourceField :=
  plan.enumerationSourceDirect

/-- The filtered selected value is exactly the completed Enumeration target. -/
theorem addressedEnumerationNumberHavingJoin_enumerationValueDependency
    (plan : CheckedAddressedEnumerationNumberHavingJoin model) :
    plan.sourceShape.starredField = plan.enumerationProducer.target.field :=
  plan.enumerationValueDependency

/-- The same filtered operand retains the completed Number target in its `Having` inventory. -/
theorem addressedEnumerationNumberHavingJoin_numberFilterDependency
    (plan : CheckedAddressedEnumerationNumberHavingJoin model) :
    plan.sourceShape.havingDependencies.contains
      plan.numberProducer.placement.targetField = true :=
  plan.numberFilterDependency

/-- Analyze exposes both typed producer edges and the consumer's complete checked inventory. -/
@[simp]
theorem addressedEnumerationNumberHavingJoin_analyze
    (plan : CheckedAddressedEnumerationNumberHavingJoin model) :
    plan.analyze = {
      numberProducerTarget := plan.numberProducer.placement.targetField
      enumerationProducerTarget := plan.enumerationProducer.target.field
      consumerTarget := plan.consumer.target.field
      fieldDependencies := [
        (plan.numberProducer.placement.targetField,
          [plan.numberProducer.placement.sourceDeclaration.id]),
        (plan.enumerationProducer.target.field,
          [plan.enumerationSourceField]),
        (plan.consumer.target.field,
          plan.consumer.source.fieldDependencies)]
    } := by
  rfl

/-- Execution delegates to both completed producer phases and one combined exact-address read view. -/
theorem addressedEnumerationNumberHavingJoin_execute_delegates
    (plan : CheckedAddressedEnumerationNumberHavingJoin model)
    (input : CheckedDocument model) :
    plan.execute input = (do
      let numberProducer ← plan.numberProducer.execute input |>.mapError
        AddressedEnumerationNumberHavingJoinFault.numberProducer
      let enumerationProducer ← plan.enumerationProducer.execute input |>.mapError
        AddressedEnumerationNumberHavingJoinFault.enumerationProducer
      let enumerationDependencies ←
        projectEnumerationDependencyCells enumerationProducer |>.mapError
          (fun error => AddressedEnumerationNumberHavingJoinFault.enumerationDependency
            error.target error.cause)
      let read := readAfterEnumerationDependenciesWith enumerationDependencies
        (readAfterNumericDependencies input numberProducer)
      let consumer ← plan.consumer.executeWithRead input read |>.mapError
        AddressedEnumerationNumberHavingJoinFault.consumer
      pure { numberProducer, enumerationProducer, consumer }) := by
  rfl

/-- Result projection classifies the three already-executed phases without recomputation. -/
theorem addressedEnumerationNumberHavingJoin_executeResult_projects
    (plan : CheckedAddressedEnumerationNumberHavingJoin model)
    (input : CheckedDocument model)
    (numberPayloadAt : CellAddr → NumberPayload)
    (numberMessages : List (ComputationFormalMessage NumberPayload))
    (enumerationProducerResidualMessages consumerResidualMessages :
      List StringResidual)
    (outcomes : AddressedEnumerationNumberHavingJoinOutcomes)
    (executed : plan.execute input = .ok outcomes) :
    (plan.executeResult input numberPayloadAt numberMessages
      enumerationProducerResidualMessages consumerResidualMessages).map
      (fun view =>
        (view.number, view.enumerationProducer, view.consumer)) = .ok (
      NumericComputationRunView.fromSourceOutcomesWithMessages
        MessagePointer.ofCellAddr numberPayloadAt numberMessages
        outcomes.numberProducer,
      projectAddressedEnumerationResults input enumerationProducerResidualMessages
        outcomes.enumerationProducer,
      projectAddressedEnumerationResults input consumerResidualMessages
        outcomes.consumer) := by
  unfold CheckedAddressedEnumerationNumberHavingJoin.executeResult
  rw [executed]
  rfl

/-- Neither statically compatible Enumeration phase can invent a target-rejection entry. -/
theorem addressedEnumerationNumberHavingJoin_executeResult_hasNoEnumerationErrors
    (plan : CheckedAddressedEnumerationNumberHavingJoin model)
    (input : CheckedDocument model)
    (numberPayloadAt : CellAddr → NumberPayload)
    (numberMessages : List (ComputationFormalMessage NumberPayload))
    (enumerationProducerResidualMessages consumerResidualMessages :
      List StringResidual)
    (outcomes : AddressedEnumerationNumberHavingJoinOutcomes)
    (executed : plan.execute input = .ok outcomes) :
    (plan.executeResult input numberPayloadAt numberMessages
      enumerationProducerResidualMessages consumerResidualMessages).map
      (fun view =>
        (view.enumerationProducer.withErrors, view.consumer.withErrors)) =
      .ok ([], []) := by
  unfold CheckedAddressedEnumerationNumberHavingJoin.executeResult
  rw [executed]
  change Except.ok (
    (projectAddressedEnumerationResults input
      enumerationProducerResidualMessages
      outcomes.enumerationProducer).withErrors,
    (projectAddressedEnumerationResults input consumerResidualMessages
      outcomes.consumer).withErrors) = Except.ok ([], [])
  rw [addressedEnumerationResults_haveNoTargetErrors,
    addressedEnumerationResults_haveNoTargetErrors]

/-- Enumeration application delegates to the producer and consumer result folds in phase order. -/
theorem addressedEnumerationNumberHavingJoinRun_applyEnumerations_delegates
    (view : AddressedEnumerationNumberHavingJoinRunView
      model NumberPayload StringResidual)
    (destination : CheckedDocument model) :
    view.applyEnumerationsToChecked destination = (do
      let afterProducer ← view.enumerationProducer.applyTo
        destination.sourceStringTargetStateAt
      view.consumer.applyTo afterProducer) := by
  rfl

end A12Kernel
