import A12Kernel.Elaboration.AddressedWorldTimeConstruction

/-! # Checked Time target laws -/

namespace A12Kernel

@[simp] theorem timeConstructionResult_value
    (time : TimeOfDay) :
    (TimeConstructionResult.value time).asTimeComputationResult =
      .value time := rfl

@[simp] theorem timeConstructionResult_unavailable
    (cause : FormalCause) :
    (TimeConstructionResult.unavailable cause).asTimeComputationResult =
      .poison cause := rfl

/-- Every selected clock is retained exactly through target rendering. -/
theorem timeTarget_evaluate_value
    (target : CheckedTimeTarget model) (time : TimeOfDay) :
    target.evaluate (.value time) =
      .accepted (target.format.render time) := rfl

/-- The checked computation certificate excludes its target from every supplied component dependency. -/
theorem checkedTimeConstructionComputation_excludes_target
    (operation : CheckedTimeConstructionComputation model) :
    operation.components.referencesField
      operation.target.checked.target.id = false :=
  operation.targetNotReferenced

/-- A real checked construction reaches exact target rendering without an intermediate instant. -/
theorem checkedTimeConstructionComputation_evaluate_value
    (operation : CheckedTimeConstructionComputation model)
    (input : CheckedDocument model) (time : TimeOfDay)
    (evaluated :
      operation.evaluateConstruction input = .ok (.value time)) :
    operation.evaluateOutcome input =
      .ok (.accepted (operation.target.format.render time)) := by
  simp [CheckedTimeConstructionComputation.evaluateOutcome, evaluated,
    TimeConstructionResult.asTimeComputationResult,
    CheckedTimeTarget.evaluate, Except.map]

/-- The checked world-aware computation certificate excludes its target from every static component and dynamic amount dependency. -/
theorem checkedWorldTimeConstructionComputation_excludes_target
    (operation : CheckedWorldTimeConstructionComputation model) :
    operation.components.referencesField
      operation.target.checked.target.id = false :=
  operation.targetNotReferenced

/-- A real world-aware construction reaches exact target rendering without retaining the transport date or instant. -/
theorem checkedWorldTimeConstructionComputation_evaluate_value
    (operation : CheckedWorldTimeConstructionComputation model)
    (world : World) (input : CheckedDocument model) (time : TimeOfDay)
    (evaluated :
      operation.evaluateConstruction world input = .ok (.value time)) :
    operation.evaluateOutcome world input =
      .ok (.accepted (operation.target.format.render time)) := by
  simp [CheckedWorldTimeConstructionComputation.evaluateOutcome, evaluated,
    TimeConstructionResult.asTimeComputationResult,
    CheckedTimeTarget.evaluate, Except.map]

/-- Time has no target-local error branch, so only residual messages affect the public error predicate. -/
theorem timeComputationRun_noErrorOccurred_iff
    (view : TimeComputationRunView ResidualMessage Target) :
    view.noErrorOccurred = true ↔
      view.formalErrorsInOperands = [] := by
  have noComputedErrors : view.withErrors = [] := by
    cases errorList : view.withErrors with
    | nil => rfl
    | cons error _ => exact nomatch error
  simp [TimeComputationRunView.noErrorOccurred,
    TemporalComputationRunView.noErrorOccurred, noComputedErrors]

/-- An ordinary successful Time instance equal to its immutable source target produces no changed action. -/
theorem timeComputationRun_sourceValueChangedAt_identical
    (sourceState : Target → TimeTargetState)
    (computed : TimeComputedInstance Target)
    (identical : (sourceState computed.targetField).storedValue =
      some computed.value) :
    TimeComputationRunView.sourceValueChangedAt sourceState computed =
      false := by
  simp [TimeComputationRunView.sourceValueChangedAt, identical]

/-- An ordinary successful Time instance different from its immutable source target produces a changed action. -/
theorem timeComputationRun_sourceValueChangedAt_different
    (sourceState : Target → TimeTargetState)
    (computed : TimeComputedInstance Target)
    (different : (sourceState computed.targetField).storedValue ≠
      some computed.value) :
    TimeComputationRunView.sourceValueChangedAt sourceState computed =
      true := by
  simp [TimeComputationRunView.sourceValueChangedAt, different]

/-- The repeatable construction certificate excludes its target from every addressed field dependency. -/
theorem checkedAddressedTimeConstructionComputation_excludes_target
    (operation : CheckedAddressedTimeConstructionComputation model) :
    operation.referencesField operation.checkedTarget.targetField = false :=
  operation.targetNotReferenced

/-- A checked addressed extractor retains exactly the token selected by its constructor position. -/
theorem checkedAddressedTimeExtractorField_position_matches
    (checked : CheckedAddressedTimeExtractorField model targetScope) :
    checked.position.extractor = checked.part := by
  have admitted := checked.admitted
  unfold FlatModel.admitsTimeExtractorComponentField at admitted
  split at admitted <;> simp_all

/-- Repeatable construction retains the operation and delegates exact row outcomes to ordinary source-relative Time classification. -/
theorem addressedTimeConstruction_executeResult_projects
    (operation : CheckedAddressedTimeConstructionComputation model)
    (input : CheckedDocument model) (messages : List ResidualMessage)
    (outcomes : List AddressedTimeConstructionOutcome)
    (view : AddressedTimeConstructionRunView model ResidualMessage)
    (executed : operation.execute input = .ok outcomes)
    (produced : operation.executeResult input messages = .ok view) :
    view.operation = operation ∧
    view.time = TimeComputationRunView.fromOutcomesAt
        input.sourceTimeTargetStateAt messages
        (outcomes.map fun entry => (entry.targetField, entry.outcome)) := by
  have executedWithRead :
      operation.executeWithRead input input.read = .ok outcomes := by
    simpa [CheckedAddressedTimeConstructionComputation.execute] using executed
  rw [CheckedAddressedTimeConstructionComputation.executeResult,
    CheckedAddressedTimeConstructionComputation.executeResultWithRead,
    executedWithRead] at produced
  simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at produced
  subst view
  exact ⟨rfl, rfl⟩

/-- Repeatable construction applies exactly the ordinary Time action fold to a separately supplied same-model destination. -/
theorem addressedTimeConstruction_applyToChecked_delegates
    (view : AddressedTimeConstructionRunView model ResidualMessage)
    (destination : CheckedDocument model) :
    view.applyToChecked destination =
      view.time.applyTo destination.sourceTimeTargetStateAt := by
  rfl

/-- The mixed addressed/world construction certificate excludes its target from every addressed source and dynamic amount dependency. -/
theorem checkedAddressedWorldTimeConstructionComputation_excludes_target
    (operation : CheckedAddressedWorldTimeConstructionComputation model) :
    operation.referencesField operation.checkedTarget.targetField = false :=
  operation.targetNotReferenced

/-- A bound field-backed shift reads its complete DateTime source within the target row's certified scope. -/
theorem checkedAddressedShiftedTimeExtractor_source_bounded
    (checked : CheckedAddressedShiftedTimeExtractor model targetScope) :
    checked.shift.source.sourceDeclaration.repetitionBoundBy targetScope = true :=
  checked.shift.source.sourceScopeBound

/-- Analysis retains the nested source before every authored amount dependency. -/
@[simp] theorem addressedShiftedTimeComponent_fieldDependencies
    (checked : CheckedAddressedShiftedTimeExtractor model targetScope) :
    CheckedAddressedWorldTimeComponent.fieldDependencies
        (.shiftedField checked) =
      checked.shift.source.source.id :: checked.shift.amount.fieldDependencies := by
  rfl

/-- World-aware repeatable construction retains the operation and delegates exact row outcomes to ordinary source-relative Time classification. -/
theorem addressedWorldTimeConstruction_executeResult_projects
    (operation : CheckedAddressedWorldTimeConstructionComputation model)
    (world : World) (input : CheckedDocument model)
    (messages : List ResidualMessage)
    (outcomes : List AddressedTimeConstructionOutcome)
    (view : AddressedWorldTimeConstructionRunView model ResidualMessage)
    (executed : operation.execute world input = .ok outcomes)
    (produced : operation.executeResult world input messages = .ok view) :
    view.operation = operation ∧
      view.time = TimeComputationRunView.fromOutcomesAt
        input.sourceTimeTargetStateAt messages
        (outcomes.map fun entry => (entry.targetField, entry.outcome)) := by
  rw [CheckedAddressedWorldTimeConstructionComputation.executeResult,
    executed] at produced
  simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at produced
  subst view
  exact ⟨rfl, rfl⟩

/-- World-aware repeatable construction applies exactly the ordinary Time action fold to a separately supplied same-model destination. -/
theorem addressedWorldTimeConstruction_applyToChecked_delegates
    (view : AddressedWorldTimeConstructionRunView model ResidualMessage)
    (destination : CheckedDocument model) :
    view.applyToChecked destination =
      view.time.applyTo destination.sourceTimeTargetStateAt := by
  rfl

/-- A retained Time clear creates a present-empty destination target even when that target was absent. -/
theorem timeComputationDestination_applyRetainedClear_same
    {Target : Type} [DecidableEq Target]
    (destination : TimeComputationDestination Target)
    (target : Target) :
    destination.applyRetainedClear target target = .presentEmpty := by
  simp [TimeComputationDestination.applyRetainedClear,
    TemporalComputationDestination.applyRetainedClear,
    TemporalComputationDestination.update,
    TemporalTargetState.applyRetainedClear]
  cases destination target <;> rfl

/-- A checked Time application with admitted unique targets delegates exactly to the established value/clear fold over the checked document's source projection. -/
theorem timeComputationRun_applyToChecked_delegates
    (view : TimeComputationRunView ResidualMessage)
    (destination : CheckedDocument model)
    (unique : FieldId.firstDuplicate? view.actionTargets = none)
    (valid : TimeComputationRunView.validateActionTargets model
      view.actionTargets = .ok ()) :
    view.applyToChecked destination =
      (view.applyTo destination.sourceTimeTargetState).mapError
        (fun | .duplicateActionTarget duplicate => TimeComputationRunView.TimeComputationCheckedApplicationError.duplicateActionTarget duplicate) := by
  simp [TimeComputationRunView.applyToChecked, unique, valid]
  rfl

/-- Residual messages never change already-classified Time application actions. -/
theorem timeComputationRun_residualMessages_doNotAffectApplication
    (input : CheckedDocument model)
    (firstMessages secondMessages : List ResidualMessage)
    (outcomes : List (FieldId × TimeTargetOutcome))
    (destination : TimeComputationDestination) :
    (TimeComputationRunView.fromOutcomes input firstMessages outcomes).applyTo
        destination =
      (TimeComputationRunView.fromOutcomes input secondMessages outcomes).applyTo
        destination := by
  rfl

end A12Kernel
