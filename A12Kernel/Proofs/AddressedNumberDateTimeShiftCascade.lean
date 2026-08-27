import A12Kernel.Elaboration.AddressedNumberDateTimeShiftCascade

/-! # Repeatable Number-to-DateTime shift cascade laws -/

namespace A12Kernel

/-- The checked cascade retains the exact Number target read by the DateTime amount expression. -/
theorem checkedAddressedNumberDateTimeShiftCascade_reads_producer
    (plan : CheckedAddressedNumberDateTimeShiftCascade model) :
    plan.consumer.shift.amount.referencesField
      plan.producer.placement.targetField = true :=
  plan.consumerAmountReadsProducer

/-- Analyze exposes the two family targets and their complete direct dependency inventories in execution order. -/
@[simp] theorem addressedNumberDateTimeShiftCascade_analyze
    (plan : CheckedAddressedNumberDateTimeShiftCascade model) :
    plan.analyze = {
      targetFields := [plan.producer.placement.targetField,
        plan.consumer.checkedTarget.targetField]
      fieldDependencies := [
        (plan.producer.placement.targetField,
          [plan.producer.placement.sourceDeclaration.id]),
        (plan.consumer.checkedTarget.targetField,
          plan.consumer.fieldDependencies)]
    } := by
  rfl

/-- An exact completed producer outcome is the amount cell observed at that address. -/
theorem addressedNumberDateTimeShiftCascade_amountRead_completed
    (plan : CheckedAddressedNumberDateTimeShiftCascade model)
    (input : CheckedDocument model)
    (producer : List (SourcedNumericTargetOutcome CellAddr))
    (environment : Env) (address : CellAddr)
    (completion : SourcedNumericTargetOutcome CellAddr)
    (resolved : input.cellAddress environment
      plan.producer.placement.targetField = .ok address)
    (found : producer.find? (fun candidate =>
      candidate.targetField == address) = some completion) :
    plan.amountRead input producer environment
      plan.producer.placement.targetField =
        .ok (some (NumericDependencyCell.ofOutcome completion.outcome).checked) := by
  have resolved' : input.cellAddress environment
      plan.producer.placement.targetField = .ok address := resolved
  unfold CheckedAddressedNumberDateTimeShiftCascade.amountRead
  rw [resolved']
  simp only [bind, Except.bind, beq_self_eq_true, if_true]
  change (match producer.find? (fun candidate =>
      candidate.targetField == address) with
    | some candidate =>
        Except.ok (some (NumericDependencyCell.ofOutcome candidate.outcome).checked)
    | none =>
        Except.ok (some (NumericDependencyCell.ofObservation .empty).checked)) = _
  rw [found]

/-- A producer target with no completed outcome reads cleanly empty rather than leaking its stale immutable value. -/
theorem addressedNumberDateTimeShiftCascade_amountRead_hides_stale
    (plan : CheckedAddressedNumberDateTimeShiftCascade model)
    (input : CheckedDocument model)
    (producer : List (SourcedNumericTargetOutcome CellAddr))
    (environment : Env) (address : CellAddr)
    (resolved : input.cellAddress environment
      plan.producer.placement.targetField = .ok address)
    (missing : producer.find? (fun candidate =>
      candidate.targetField == address) = none) :
    plan.amountRead input producer environment
      plan.producer.placement.targetField =
        .ok (some (NumericDependencyCell.ofObservation .empty).checked) := by
  have resolved' : input.cellAddress environment
      plan.producer.placement.targetField = .ok address := resolved
  unfold CheckedAddressedNumberDateTimeShiftCascade.amountRead
  rw [resolved']
  simp only [bind, Except.bind, beq_self_eq_true, if_true]
  change (match producer.find? (fun candidate =>
      candidate.targetField == address) with
    | some candidate =>
        Except.ok (some (NumericDependencyCell.ofOutcome candidate.outcome).checked)
    | none =>
        Except.ok (some (NumericDependencyCell.ofObservation .empty).checked)) = _
  rw [missing]

/-- Result construction projects one execution into the two existing family owners without rebuilding or merging their outcomes. -/
theorem addressedNumberDateTimeShiftCascade_executeResult_projects
    (plan : CheckedAddressedNumberDateTimeShiftCascade model)
    (input : CheckedDocument model)
    (numberPayloadAt : CellAddr → NumberPayload)
    (numberMessages : List (ComputationFormalMessage NumberPayload))
    (dateTimeMessages : List DateTimeResidual)
    (outcomes : AddressedNumberDateTimeShiftCascadeOutcomes)
    (view : AddressedNumberDateTimeShiftCascadeRunView
      model NumberPayload DateTimeResidual)
    (executed : plan.execute input = .ok outcomes)
    (produced : plan.executeResult input numberPayloadAt numberMessages
      dateTimeMessages = .ok view) :
    view.plan = plan ∧
      view.number = NumericComputationRunView.fromSourceOutcomesWithMessages
        MessagePointer.ofCellAddr numberPayloadAt numberMessages outcomes.producer ∧
      view.dateTime = plan.consumer.resultFromOutcomes input
        dateTimeMessages outcomes.consumer := by
  rw [CheckedAddressedNumberDateTimeShiftCascade.executeResult,
    executed] at produced
  simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at produced
  subst view
  exact ⟨rfl, rfl, rfl⟩

end A12Kernel
