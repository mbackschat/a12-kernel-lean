import A12Kernel.Elaboration.AddressedEnumerationNumberHavingJoin
import A12Kernel.Proofs.AddressedEnumerationComputation
import A12Kernel.Proofs.ComputationFormalInput

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

/-- The checked serial route fixes `FieldValueAsNumber` on the completed Enumeration target rather than any stale sibling field. -/
theorem addressedEnumerationToNumberHavingCascade_numberDependency
    (plan : CheckedAddressedEnumerationToNumberHavingCascade model) :
    plan.numberProducer.placement.sourceDeclaration.id =
      plan.enumerationProducer.target.field :=
  plan.enumerationNumberDependency

/-- Analyze retains the conversion projection and all three exact dependency inventories. -/
@[simp]
theorem addressedEnumerationToNumberHavingCascade_analyze
    (plan : CheckedAddressedEnumerationToNumberHavingCascade model) :
    plan.analyze = {
      enumerationProducerTarget := plan.enumerationProducer.target.field
      numberProjection := plan.numberProducer.projectionRef
      numberProducerTarget := plan.numberProducer.placement.targetField
      consumerTarget := plan.consumer.target.field
      fieldDependencies := [
        (plan.enumerationProducer.target.field, [plan.enumerationSourceField]),
        (plan.numberProducer.placement.targetField,
          [plan.numberProducer.placement.sourceDeclaration.id]),
        (plan.consumer.target.field,
          plan.consumer.source.fieldDependencies)]
    } := by
  rfl

/-- Execution delegates exactly through the Enumeration overlay, the dependent Number conversion, and the combined final read view. -/
theorem addressedEnumerationToNumberHavingCascade_execute_delegates
    (plan : CheckedAddressedEnumerationToNumberHavingCascade model)
    (input : CheckedDocument model) :
    plan.execute input = (do
      let enumerationProducer ← plan.enumerationProducer.execute input |>.mapError
        AddressedEnumerationToNumberHavingCascadeFault.enumerationProducer
      let enumerationDependencies ←
        projectEnumerationDependencyCells enumerationProducer |>.mapError
          (fun error =>
            AddressedEnumerationToNumberHavingCascadeFault.enumerationDependency
              error.target error.cause)
      let enumerationRead :=
        readAfterEnumerationDependencies input enumerationDependencies
      let numberProducer ← plan.numberProducer.executeWithRead input enumerationRead
        |>.mapError AddressedEnumerationToNumberHavingCascadeFault.numberProducer
      let read := readAfterEnumerationDependenciesWith enumerationDependencies
        (readAfterNumericDependencies input numberProducer)
      let consumer ← plan.consumer.executeWithRead input read |>.mapError
        AddressedEnumerationToNumberHavingCascadeFault.consumer
      pure { enumerationProducer, numberProducer, consumer }) := by
  rfl

/-- Caller-supplied state remains below both completed typed overlays throughout the fixed serial route. -/
theorem addressedEnumerationToNumberHavingCascade_executeWithFallbackRead_delegates
    (plan : CheckedAddressedEnumerationToNumberHavingCascade model)
    (input : CheckedDocument model)
    (fallbackRead : CellAddr → Except CheckedDocumentError CheckedCell) :
    plan.executeWithFallbackRead input fallbackRead = (do
      let enumerationProducer ← plan.enumerationProducer.executeWithRead input
        fallbackRead |>.mapError
          AddressedEnumerationToNumberHavingCascadeFault.enumerationProducer
      let enumerationDependencies ←
        projectEnumerationDependencyCells enumerationProducer |>.mapError
          (fun error =>
            AddressedEnumerationToNumberHavingCascadeFault.enumerationDependency
              error.target error.cause)
      let enumerationRead := readAfterEnumerationDependenciesWith
        enumerationDependencies fallbackRead
      let numberProducer ← plan.numberProducer.executeWithRead input enumerationRead
        |>.mapError AddressedEnumerationToNumberHavingCascadeFault.numberProducer
      let read := readAfterEnumerationDependenciesWith enumerationDependencies
        (readAfterNumericDependenciesWith numberProducer fallbackRead)
      let consumer ← plan.consumer.executeWithRead input read |>.mapError
        AddressedEnumerationToNumberHavingCascadeFault.consumer
      pure { enumerationProducer, numberProducer, consumer }) := by
  rfl

/-- Result projection classifies the three already-executed serial phases without recomputation. -/
theorem addressedEnumerationToNumberHavingCascade_executeResult_projects
    (plan : CheckedAddressedEnumerationToNumberHavingCascade model)
    (input : CheckedDocument model)
    (numberPayloadAt : CellAddr → NumberPayload)
    (numberMessages : List (ComputationFormalMessage NumberPayload))
    (enumerationProducerResidualMessages consumerResidualMessages :
      List StringResidual)
    (outcomes : AddressedEnumerationToNumberHavingCascadeOutcomes)
    (executed : plan.execute input = .ok outcomes) :
    (plan.executeResult input numberPayloadAt numberMessages
      enumerationProducerResidualMessages consumerResidualMessages).map
      (fun view =>
        (view.enumerationProducer, view.number, view.consumer)) = .ok (
      projectAddressedEnumerationResults input enumerationProducerResidualMessages
        outcomes.enumerationProducer,
      NumericComputationRunView.fromSourceOutcomesWithMessages
        MessagePointer.ofCellAddr numberPayloadAt numberMessages
        outcomes.numberProducer,
      projectAddressedEnumerationResults input consumerResidualMessages
        outcomes.consumer) := by
  unfold CheckedAddressedEnumerationToNumberHavingCascade.executeResult
  unfold CheckedAddressedEnumerationToNumberHavingCascade.execute at executed
  unfold CheckedAddressedEnumerationToNumberHavingCascade.executeResultWithFallbackRead
  rw [executed]
  rfl

/-- Neither statically compatible Enumeration phase can invent a target-rejection entry. -/
theorem addressedEnumerationToNumberHavingCascade_executeResult_hasNoEnumerationErrors
    (plan : CheckedAddressedEnumerationToNumberHavingCascade model)
    (input : CheckedDocument model)
    (numberPayloadAt : CellAddr → NumberPayload)
    (numberMessages : List (ComputationFormalMessage NumberPayload))
    (enumerationProducerResidualMessages consumerResidualMessages :
      List StringResidual)
    (outcomes : AddressedEnumerationToNumberHavingCascadeOutcomes)
    (executed : plan.execute input = .ok outcomes) :
    (plan.executeResult input numberPayloadAt numberMessages
      enumerationProducerResidualMessages consumerResidualMessages).map
      (fun view =>
        (view.enumerationProducer.withErrors, view.consumer.withErrors)) =
      .ok ([], []) := by
  unfold CheckedAddressedEnumerationToNumberHavingCascade.executeResult
  unfold CheckedAddressedEnumerationToNumberHavingCascade.execute at executed
  unfold CheckedAddressedEnumerationToNumberHavingCascade.executeResultWithFallbackRead
  rw [executed]
  change Except.ok (
    (projectAddressedEnumerationResults input
      enumerationProducerResidualMessages
      outcomes.enumerationProducer).withErrors,
    (projectAddressedEnumerationResults input consumerResidualMessages
      outcomes.consumer).withErrors) = Except.ok ([], [])
  rw [addressedEnumerationResults_haveNoTargetErrors,
    addressedEnumerationResults_haveNoTargetErrors]

/-- Whole-call formal inputs remain call-global while the three family channels retain only their independently owned messages. -/
theorem addressedEnumerationToNumberHavingCascade_executeResultWithFormalInputs_exact
    (plan : CheckedAddressedEnumerationToNumberHavingCascade model)
    (input : CheckedDocument model)
    (inputPlan : CheckedComputationFormalInputPlan model)
    (prepared : ComputationFormalInputPreparation model)
    (outcomes : AddressedEnumerationToNumberHavingCascadeOutcomes)
    (view : AddressedEnumerationToNumberHavingCascadeFormalInputRunView model)
    (planned : plan.formalInputPlan = .ok inputPlan)
    (preparation : inputPlan.prepare input = .ok prepared)
    (executed : plan.executeWithFallbackRead input
      prepared.preliminary.readComputation = .ok outcomes)
    (produced : plan.executeResultWithFormalInputs input = .ok view) :
    view.formalErrorsInOperands = prepared.formalErrorsInOperands ∧
      view.phases.enumerationProducer =
        projectAddressedEnumerationResults input [] outcomes.enumerationProducer ∧
      view.phases.number =
        NumericComputationRunView.fromSourceOutcomesWithMessages
          MessagePointer.ofCellAddr (fun _ => ()) [] outcomes.numberProducer ∧
      view.phases.consumer =
        projectAddressedEnumerationResults input [] outcomes.consumer := by
  rw [CheckedAddressedEnumerationToNumberHavingCascade.executeResultWithFormalInputs,
    planned] at produced
  simp only [bind, Except.bind, Except.mapError, preparation] at produced
  rw [CheckedAddressedEnumerationToNumberHavingCascade.executeResultWithFallbackRead,
    executed] at produced
  simp only [bind, Except.bind, pure, Except.pure,
    Except.ok.injEq] at produced
  subst view
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- A post-preparation serial execution failure retains the exact eager inventory beside the unchanged typed fault. -/
theorem addressedEnumerationToNumberHavingCascade_executeResultWithFormalInputs_failure_exact
    (plan : CheckedAddressedEnumerationToNumberHavingCascade model)
    (input : CheckedDocument model)
    (inputPlan : CheckedComputationFormalInputPlan model)
    (prepared : ComputationFormalInputPreparation model)
    (fault : AddressedEnumerationToNumberHavingCascadeFault)
    (planned : plan.formalInputPlan = .ok inputPlan)
    (preparation : inputPlan.prepare input = .ok prepared)
    (executed : plan.executeResultWithFallbackRead input
      prepared.preliminary.readComputation (fun _ => ()) []
      ([] : List ComputationFormalInputFinding) [] = .error fault) :
    plan.executeResultWithFormalInputs input =
      .error (.execution prepared.formalErrorsInOperands fault) := by
  rw [CheckedAddressedEnumerationToNumberHavingCascade.executeResultWithFormalInputs,
    planned]
  simp only [bind, Except.bind, Except.mapError, preparation, executed]

/-- Enumeration application delegates to the serial producer and consumer result folds in phase order. -/
theorem addressedEnumerationToNumberHavingCascadeRun_applyEnumerations_delegates
    (view : AddressedEnumerationToNumberHavingCascadeRunView
      model NumberPayload StringResidual)
    (destination : CheckedDocument model) :
    view.applyEnumerationsToChecked destination = (do
      let afterProducer ← view.enumerationProducer.applyTo
        destination.sourceStringTargetStateAt
      view.consumer.applyTo afterProducer) := by
  rfl

end A12Kernel
