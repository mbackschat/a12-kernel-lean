import A12Kernel.Elaboration.AddressedDateFromDateTime

/-! # Checked `DateFromDateTime` computation laws -/

namespace A12Kernel

/-- Source extraction and target rendering use the same model-zone profile. -/
theorem dateFromDateTimeComputation_profiles_eq
    (operation : CheckedDateFromDateTimeComputation model) :
    operation.source.profile = operation.target.profile := by
  have selected :
      some operation.source.profile = some operation.target.profile := by
    simpa [CheckedTemporalTargetPolicy.timeZoneId] using
      operation.source.profileOwned.symm.trans operation.target.profileMatches
  exact Option.some.inj selected

/-- A computation-phase empty source remains clean no-value through target execution. -/
theorem dateFromDateTimeComputation_empty
    (operation : CheckedDateFromDateTimeComputation model)
    (input : CheckedDocument model)
    (read : input.read {
      field := operation.source.source.id, path := [] } = .ok cell)
    (empty : observeCell .computation cell = .empty) :
    operation.evaluateOutcome input = .ok .noValue := by
  have operandRead : operation.evaluateOperand input = .ok .noValue := by
    simp [CheckedDateFromDateTimeComputation.evaluateOperand, read, empty] <;> rfl
  unfold CheckedDateFromDateTimeComputation.evaluateOutcome
  rw [operandRead]
  rfl

/-- A reached formal source failure preserves its exact cause and never becomes a target error. -/
theorem dateFromDateTimeComputation_poison
    (operation : CheckedDateFromDateTimeComputation model)
    (input : CheckedDocument model)
    (read : input.read {
      field := operation.source.source.id, path := [] } = .ok cell)
    (poison : observeCell .computation cell = .poison cause) :
    operation.evaluateOutcome input = .ok (.poison cause) := by
  have operandRead :
      operation.evaluateOperand input = .ok (.poison cause) := by
    simp [CheckedDateFromDateTimeComputation.evaluateOperand, read, poison] <;> rfl
  unfold CheckedDateFromDateTimeComputation.evaluateOutcome
  rw [operandRead]
  rfl

/-- A present DateTime transports the extractor's own Date midnight into the declaration-owned target. -/
theorem dateFromDateTimeComputation_value
    (operation : CheckedDateFromDateTimeComputation model)
    (input : CheckedDocument model)
    (value : TemporalValue) (date : DateValue)
    (read : input.read {
      field := operation.source.source.id, path := [] } = .ok cell)
    (observed :
      observeCell .computation cell = .value (.temporal value))
    (extracted : operation.source.extract? value = some date) :
    operation.evaluateOutcome input =
      (operation.target.evaluate (.value date.instant)).mapError .target := by
  have operandRead :
      operation.evaluateOperand input = .ok (.value date.instant) := by
    simp [CheckedDateFromDateTimeComputation.evaluateOperand,
      read, observed, extracted] <;> rfl
  unfold CheckedDateFromDateTimeComputation.evaluateOutcome
  rw [operandRead]

/-- A reached empty source stays clean no-value at every addressed row. -/
theorem addressedDateFromDateTime_empty
    (operation : CheckedAddressedDateFromDateTime model) (address : CellAddr)
    (empty : observeCell .computation cell = .empty) :
    operation.evaluateSourceCell address cell = .ok .noValue := by
  simp [CheckedAddressedDateFromDateTime.evaluateSourceCell, empty] <;> rfl

/-- A reached formal source failure retains its exact cause and row address. -/
theorem addressedDateFromDateTime_poison
    (operation : CheckedAddressedDateFromDateTime model) (address : CellAddr)
    (poison : observeCell .computation cell = .poison cause) :
    operation.evaluateSourceCell address cell = .ok (.poison cause) := by
  simp [CheckedAddressedDateFromDateTime.evaluateSourceCell, poison] <;> rfl

/-- Addressed result construction retains the checked operation and classifies every executed outcome under its exact target address. -/
theorem checkedAddressedDateFromDateTime_executeResult_projects
    (operation : CheckedAddressedDateFromDateTime model)
    (input : CheckedDocument model) (messages : List ResidualMessage)
    (outcomes : List AddressedDateFromDateTimeOutcome)
    (view : AddressedDateFromDateTimeRunView model ResidualMessage)
    (executed : operation.execute input = .ok outcomes)
    (produced : operation.executeResult input messages = .ok view) :
    view.operation = operation ∧
      view.fullDate = FullDateComputationRunView.fromOutcomesAt
        input.sourceFullDateTargetStateAt messages
        (outcomes.map fun entry => (entry.targetField, entry.outcome)) := by
  rw [CheckedAddressedDateFromDateTime.executeResult, executed] at produced
  simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at produced
  subst view
  exact ⟨rfl, rfl⟩

/-- Addressed application is exactly the common FullDate fold over the separately supplied document's exact cell-state projection. -/
theorem addressedDateFromDateTimeRun_applyToChecked_delegates
    (view : AddressedDateFromDateTimeRunView model ResidualMessage)
    (destination : CheckedDocument model) :
    view.applyToChecked destination =
      view.fullDate.applyTo destination.sourceFullDateTargetStateAt := by
  rfl

end A12Kernel
