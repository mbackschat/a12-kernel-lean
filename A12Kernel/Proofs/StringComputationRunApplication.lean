import A12Kernel.Elaboration.StringComputationRunApplication
import A12Kernel.Proofs.StringApplication

/-! # String whole-run application laws

These laws connect the generic exact-target fold to the one-target String owner and lock source-relative classification against destination-relative recomputation.
-/

namespace A12Kernel

/-- Updating one destination target yields exactly the supplied state there. -/
theorem stringComputationDestination_update_same
    [DecidableEq Target] (destination : StringComputationDestination Target)
    (target : Target) (state : StringTargetState) :
    destination.update target state target = state := by
  simp [StringComputationDestination.update]

/-- A one-target application delegates exactly to `StringTargetOutcome.applyTo`. -/
theorem stringComputationDestination_applyOutcome_same
    [DecidableEq Target] (destination : StringComputationDestination Target)
    (target : Target) (outcome : StringTargetOutcome) :
    destination.applyOutcome target outcome target =
      outcome.applyTo (destination target) := by
  simp [StringComputationDestination.applyOutcome,
    stringComputationDestination_update_same]

/-- A retained clear creates a present-empty destination target even when that target was absent. -/
theorem stringComputationDestination_applyRetainedClear_same
    [DecidableEq Target] (destination : StringComputationDestination Target)
    (target : Target) :
    destination.applyRetainedClear target target = .presentEmpty := by
  rw [StringComputationDestination.applyRetainedClear,
    stringComputationDestination_update_same]
  cases destination target <;> rfl

/-- Applying one target preserves every other destination projection. -/
theorem stringComputationDestination_applyOutcome_other
    [DecidableEq Target] (destination : StringComputationDestination Target)
    (target other : Target) (outcome : StringTargetOutcome)
    (different : other ≠ target) :
    destination.applyOutcome target outcome other = destination other := by
  simp [StringComputationDestination.applyOutcome,
    StringComputationDestination.update, different]

/-- A result with no changed, errored, or cleared action leaves the destination untouched even when successes or residual messages are nonempty. -/
theorem stringComputationRun_applyTo_noActions
    [DecidableEq Target]
    (view : StringComputationRunView ResidualMessage Target)
    (destination : StringComputationDestination Target)
    (noChanges : view.withChanges = [])
    (noErrors : view.withErrors = [])
    (noClears : view.cleared = []) :
    view.applyTo destination = .ok destination := by
  simp [StringComputationRunView.applyTo,
    StringComputationRunView.firstDuplicateActionTarget?,
    StringComputationRunView.firstDuplicateStringTarget?,
    StringComputationRunView.actionTargets, noChanges, noErrors, noClears]

/-- A checked-destination application with no source-classified actions preserves the exact caller-supplied root String projection. -/
theorem stringComputationRun_applyToChecked_noActions
    (view : StringComputationRunView ResidualMessage FieldId)
    (destination : CheckedDocument model)
    (noChanges : view.withChanges = [])
    (noErrors : view.withErrors = [])
    (noClears : view.cleared = []) :
    view.applyToChecked destination =
      .ok destination.sourceStringTargetState := by
  simp [StringComputationRunView.applyToChecked,
    StringComputationRunView.firstDuplicateActionTarget?,
    StringComputationRunView.firstDuplicateStringTarget?,
    StringComputationRunView.actionTargets,
    validateStringComputationActionTargets,
    StringComputationRunView.applyTo, noChanges, noErrors, noClears]

/-- Once exact root targets are validated, checked-destination application is precisely the established source-classified String fold. -/
theorem stringComputationRun_applyToChecked_delegates
    (view : StringComputationRunView ResidualMessage FieldId)
    (destination : CheckedDocument model)
    (noDuplicate : view.firstDuplicateActionTarget? = none)
    (valid :
      validateStringComputationActionTargets model view.actionTargets = .ok ()) :
    view.applyToChecked destination =
      (view.applyTo destination.sourceStringTargetState).mapError fun
        | .duplicateActionTarget target => .duplicateActionTarget target := by
  simp [StringComputationRunView.applyToChecked, noDuplicate, valid,
    StringComputationRunView.applyTo, Except.mapError,
    Bind.bind, Except.bind]

/-- Duplicate source actions fail before any target-kind or destination-state inspection. -/
theorem stringComputationRun_applyToChecked_duplicateTarget
    (view : StringComputationRunView ResidualMessage FieldId)
    (destination : CheckedDocument model) (target : FieldId)
    (duplicate : view.firstDuplicateActionTarget? = some target) :
    view.applyToChecked destination =
      .error (.duplicateActionTarget target) := by
  simp [StringComputationRunView.applyToChecked, duplicate]

/-- Duplicate action targets fail before any destination state is selected or changed. -/
theorem stringComputationRun_applyTo_duplicateTarget
    [DecidableEq Target]
    (view : StringComputationRunView ResidualMessage Target)
    (destination : StringComputationDestination Target) (target : Target)
    (duplicate : view.firstDuplicateActionTarget? = some target) :
    view.applyTo destination =
      .error (.duplicateActionTarget target) := by
  simp [StringComputationRunView.applyTo, duplicate]

/-- A source-unchanged success is not applied, even when the caller-supplied destination contains another value. -/
theorem stringComputationRun_unchanged_notApplied
    [DecidableEq Target] (residualMessages : List ResidualMessage)
    (target : Target) (value : StoredString)
    (destination : StringComputationDestination Target) :
    (StringComputationRunView.fromSourcedOutcomes residualMessages
      [{
        targetField := target
        outcome := .accepted value
        source := StringTargetState.presentValue value
      }]).applyTo destination =
      .ok destination := by
  simp [StringComputationRunView.fromSourcedOutcomes,
    StringComputationRunView.changedInstance?,
    StringComputationRunView.successfulInstance?,
    StringComputationRunView.computedError?,
    StringComputationRunView.shouldClear,
    StringTargetOutcome.hasComputedInstance,
    StringTargetState.storedValue,
    StringComputationRunView.applyTo,
    StringComputationRunView.firstDuplicateActionTarget?,
    StringComputationRunView.firstDuplicateStringTarget?,
    StringComputationRunView.actionTargets]

/-- A source-changed success applies the existing accepted-value transition at its exact target. -/
theorem stringComputationRun_changed_applies
    [DecidableEq Target] (residualMessages : List ResidualMessage)
    (target : Target) (value : StoredString) (source : StringTargetState)
    (destination : StringComputationDestination Target)
    (changed : source.storedValue ≠ some value) :
    (StringComputationRunView.fromSourcedOutcomes residualMessages
      [{
        targetField := target
        outcome := .accepted value
        source := source
      }]).applyTo
        destination =
      .ok (destination.applyOutcome target (.accepted value)) := by
  let entry : SourcedStringTargetOutcome Target := {
    targetField := target
    outcome := .accepted value
    source := source
  }
  have changedEntry :
      StringComputationRunView.changedInstance? entry =
        some ({ targetField := target, value } :
          StringComputedInstance Target) := by
    simp [entry, StringComputationRunView.changedInstance?,
      StringComputationRunView.successfulInstance?, changed]
  have noError :
      StringComputationRunView.computedError? entry = none := by
    simp [entry, StringComputationRunView.computedError?]
  change (StringComputationRunView.fromSourcedOutcomes
    residualMessages [entry]).applyTo destination =
      .ok (destination.applyOutcome target (.accepted value))
  simp [StringComputationRunView.fromSourcedOutcomes,
    changedEntry, noError,
    StringComputationRunView.shouldClear,
    StringTargetOutcome.hasComputedInstance,
    StringTargetState.storedValue,
    StringComputationRunView.applyTo,
    StringComputationRunView.firstDuplicateActionTarget?,
    StringComputationRunView.firstDuplicateStringTarget?,
    StringComputationRunView.actionTargets]

/-- A payloadful target error applies the existing error transition and is not also consumed by the cleared collection. -/
theorem stringComputationRun_error_applies
    [DecidableEq Target] (residualMessages : List ResidualMessage)
    (target : Target) (attempted : StoredString) (cause : StringTargetError)
    (source : StringTargetState)
    (destination : StringComputationDestination Target) :
    (StringComputationRunView.fromSourcedOutcomes residualMessages
      [{
        targetField := target
        outcome := .errored attempted cause
        source := source
      }]).applyTo destination =
      .ok (destination.applyOutcome target (.errored attempted cause)) := by
  simp [StringComputationRunView.fromSourcedOutcomes,
    StringComputationRunView.changedInstance?,
    StringComputationRunView.successfulInstance?,
    StringComputationRunView.computedError?,
    StringComputationRunView.shouldClear,
    StringTargetOutcome.hasComputedInstance,
    StringComputationRunView.applyTo,
    StringComputationRunView.firstDuplicateActionTarget?,
    StringComputationRunView.firstDuplicateStringTarget?,
    StringComputationRunView.actionTargets]

/-- A source-filled clean no-value mints a retained clear action that creates or retains a present-empty destination target. -/
theorem stringComputationRun_cleared_applies
    [DecidableEq Target] (residualMessages : List ResidualMessage)
    (target : Target) (source : StringTargetState)
    (destination : StringComputationDestination Target)
    (sourceFilled : source.storedValue.isSome = true) :
    (StringComputationRunView.fromSourcedOutcomes residualMessages
      [{
        targetField := target
        outcome := .noValue
        source := source
      }]).applyTo
        destination =
      .ok (destination.applyRetainedClear target) := by
  simp [StringComputationRunView.fromSourcedOutcomes,
    StringComputationRunView.changedInstance?,
    StringComputationRunView.successfulInstance?,
    StringComputationRunView.computedError?,
    StringComputationRunView.shouldClear,
    StringTargetOutcome.hasComputedInstance,
    StringComputationRunView.applyTo,
    StringComputationRunView.firstDuplicateActionTarget?,
    StringComputationRunView.firstDuplicateStringTarget?,
    StringComputationRunView.actionTargets, sourceFilled]

/-- Residual messages affect the error predicate but never the already-classified application plan. -/
theorem stringComputationRun_residualMessages_doNotAffectApplication
    [DecidableEq Target]
    (firstMessages secondMessages : List ResidualMessage)
    (entries : List (SourcedStringTargetOutcome Target))
    (destination : StringComputationDestination Target) :
    (StringComputationRunView.fromSourcedOutcomes
      firstMessages entries).applyTo destination =
    (StringComputationRunView.fromSourcedOutcomes
      secondMessages entries).applyTo destination := by
  rfl

end A12Kernel
