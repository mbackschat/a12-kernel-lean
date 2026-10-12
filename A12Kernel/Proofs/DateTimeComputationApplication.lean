import A12Kernel.Elaboration.DateTimeComputationApplication
import A12Kernel.Proofs.DateTimeApplication

/-! # DateTime whole-result application laws -/

namespace A12Kernel

theorem dateTimeComputationDestination_update_same
    (destination : DateTimeComputationDestination)
    (target : FieldId) (state : DateTimeTargetState) :
    destination.update target state target = state := by
  simp [DateTimeComputationDestination.update,
    TemporalComputationDestination.update]

/-- One action delegates exactly to the one-target DateTime transition. -/
theorem dateTimeComputationDestination_applyOutcome_same
    (destination : DateTimeComputationDestination)
    (target : FieldId) (outcome : DateTimeTargetOutcome) :
    destination.applyOutcome target outcome target =
      outcome.applyTo (destination target) := by
  simp [DateTimeComputationDestination.applyOutcome,
    dateTimeComputationDestination_update_same]

/-- A retained clear creates a present-empty destination target even when that target was absent. -/
theorem dateTimeComputationDestination_applyRetainedClear_same
    (destination : DateTimeComputationDestination)
    (target : FieldId) :
    destination.applyRetainedClear target target = .presentEmpty := by
  simp [DateTimeComputationDestination.applyRetainedClear,
    TemporalComputationDestination.applyRetainedClear,
    TemporalComputationDestination.update,
    TemporalTargetState.applyRetainedClear]
  cases destination target <;> rfl

/-- One action preserves every other destination field. -/
theorem dateTimeComputationDestination_applyOutcome_other
    (destination : DateTimeComputationDestination)
    (target other : FieldId) (outcome : DateTimeTargetOutcome)
    (different : other ≠ target) :
    destination.applyOutcome target outcome other = destination other := by
  simp [DateTimeComputationDestination.applyOutcome,
    DateTimeComputationDestination.update,
    TemporalComputationDestination.update, different]

/-- Unchanged successes and residual messages alone cannot mutate the destination. -/
theorem dateTimeComputationRun_applyTo_noActions
    (view : DateTimeComputationRunView ResidualMessage)
    (destination : DateTimeComputationDestination)
    (noChanges : view.withChanges = [])
    (noErrors : view.withErrors = [])
    (noClears : view.cleared = []) :
    view.applyTo destination = .ok destination := by
  simp [DateTimeComputationRunView.applyTo,
    TemporalErroredComputationRunView.applyTo,
    TemporalErroredComputationRunView.actionTargets, noChanges, noErrors, noClears,
    TemporalComputationApplicationTarget.firstDuplicate?]

/-- Duplicate action targets fail before destination state participates. -/
theorem dateTimeComputationRun_applyTo_duplicateTarget
    (view : DateTimeComputationRunView ResidualMessage)
    (destination : DateTimeComputationDestination) (field : FieldId)
    (duplicate : TemporalComputationApplicationTarget.firstDuplicate?
      view.actionTargets = some field) :
    view.applyTo destination = .error (.duplicateActionTarget field) := by
  unfold DateTimeComputationRunView.applyTo
  unfold TemporalErroredComputationRunView.applyTo
  rw [show TemporalComputationApplicationTarget.firstDuplicate?
      (TemporalErroredComputationRunView.actionTargets view
        (fun computed => computed.targetField)
        (fun computed => computed.targetField)) = some field by
    simpa [DateTimeComputationRunView.actionTargets] using duplicate]

/-- A checked DateTime application with admitted unique targets delegates exactly to the established clear/error/change fold over the checked document's source projection. -/
theorem dateTimeComputationRun_applyToChecked_delegates
    (view : DateTimeComputationRunView ResidualMessage)
    (destination : CheckedDocument model)
    (unique : FieldId.firstDuplicate? view.actionTargets = none)
    (valid : DateTimeComputationRunView.validateActionTargets model
      view.actionTargets = .ok ()) :
    view.applyToChecked destination =
      (view.applyTo destination.sourceDateTimeTargetState).mapError
        (fun | .duplicateActionTarget duplicate => DateTimeComputationRunView.DateTimeComputationCheckedApplicationError.duplicateActionTarget duplicate) := by
  simp [DateTimeComputationRunView.applyToChecked, unique, valid]
  rfl

/-- A source-unchanged accepted DateTime is not applied to a different destination. -/
theorem dateTimeComputationRun_unchanged_notApplied
    (input : CheckedDocument model) (messages : List ResidualMessage)
    (target : FieldId) (value : StoredDateTime)
    (destination : DateTimeComputationDestination)
    (unchanged :
      (input.sourceDateTimeTargetState target).computedValue = some value) :
    (DateTimeComputationRunView.fromOutcomes input messages
      [(target, .accepted value)]).applyTo destination = .ok destination := by
  simp [DateTimeComputationRunView.applyTo,
    TemporalErroredComputationRunView.applyTo,
    TemporalErroredComputationRunView.actionTargets,
    DateTimeComputationRunView.fromOutcomes,
    DateTimeComputationRunView.fromOutcomesAt,
    TemporalComputationRunView.fromErrorOutcomes,
    DateTimeComputationRunView.successfulInstance?.eq_def,
    DateTimeComputationRunView.computedError?.eq_def,
    DateTimeComputationRunView.shouldClearAt,
    DateTimeTargetOutcome.hasComputedInstance,
    DateTimeComputationRunView.sourceValueChangedAt, unchanged,
    TemporalComputationApplicationTarget.firstDuplicate?]

/-- A source-changed accepted DateTime applies the existing one-target write. -/
theorem dateTimeComputationRun_changed_applies
    (input : CheckedDocument model) (messages : List ResidualMessage)
    (target : FieldId) (value : StoredDateTime)
    (destination : DateTimeComputationDestination)
    (changed :
      (input.sourceDateTimeTargetState target).computedValue != some value) :
    (DateTimeComputationRunView.fromOutcomes input messages
      [(target, .accepted value)]).applyTo destination =
        .ok (destination.applyOutcome target (.accepted value)) := by
  simp [DateTimeComputationRunView.applyTo,
    TemporalErroredComputationRunView.applyTo,
    TemporalErroredComputationRunView.actionTargets,
    DateTimeComputationRunView.fromOutcomes,
    DateTimeComputationRunView.fromOutcomesAt,
    TemporalComputationRunView.fromErrorOutcomes,
    DateTimeComputationRunView.successfulInstance?.eq_def,
    DateTimeComputationRunView.computedError?.eq_def,
    DateTimeComputationRunView.shouldClearAt,
    DateTimeTargetOutcome.hasComputedInstance,
    DateTimeComputationRunView.sourceValueChangedAt, changed,
    TemporalComputationApplicationTarget.firstDuplicate?]

/-- A target-rejected rendering applies the one-target errored transition. -/
theorem dateTimeComputationRun_error_applies
    (input : CheckedDocument model) (messages : List ResidualMessage)
    (target : FieldId) (attempted : StoredDateTime) (cause : DateTimeTargetError)
    (destination : DateTimeComputationDestination) :
    (DateTimeComputationRunView.fromOutcomes input messages
      [(target, .errored attempted cause)]).applyTo destination =
        .ok (destination.applyOutcome target (.errored attempted cause)) := by
  simp [DateTimeComputationRunView.applyTo,
    TemporalErroredComputationRunView.applyTo,
    TemporalErroredComputationRunView.actionTargets,
    DateTimeComputationRunView.fromOutcomes,
    DateTimeComputationRunView.fromOutcomesAt,
    TemporalComputationRunView.fromErrorOutcomes,
    DateTimeComputationRunView.successfulInstance?.eq_def,
    DateTimeComputationRunView.computedError?.eq_def,
    DateTimeComputationRunView.shouldClearAt,
    DateTimeTargetOutcome.hasComputedInstance,
    TemporalComputationApplicationTarget.firstDuplicate?]

/-- A source-filled quiet no-value mints a retained clear action that creates or retains a present-empty destination target. -/
theorem dateTimeComputationRun_cleared_applies
    (input : CheckedDocument model) (messages : List ResidualMessage)
    (target : FieldId) (destination : DateTimeComputationDestination)
    (sourceFilled :
      (input.sourceDateTimeTargetState target).storedValue.isSome = true) :
    (DateTimeComputationRunView.fromOutcomes input messages
      [(target, .noValue)]).applyTo destination =
        .ok (destination.applyRetainedClear target) := by
  simp [DateTimeComputationRunView.applyTo,
    TemporalErroredComputationRunView.applyTo,
    TemporalErroredComputationRunView.actionTargets,
    DateTimeComputationRunView.fromOutcomes,
    DateTimeComputationRunView.fromOutcomesAt,
    TemporalComputationRunView.fromErrorOutcomes,
    DateTimeComputationRunView.successfulInstance?.eq_def,
    DateTimeComputationRunView.computedError?.eq_def,
    DateTimeComputationRunView.shouldClearAt,
    DateTimeTargetOutcome.hasComputedInstance, sourceFilled,
    TemporalComputationApplicationTarget.firstDuplicate?]

/-- Residual messages affect error status but never the already-classified application actions. -/
theorem dateTimeComputationRun_residualMessages_doNotAffectApplication
    (input : CheckedDocument model)
    (firstMessages secondMessages : List ResidualMessage)
    (outcomes : List (FieldId × DateTimeTargetOutcome))
    (destination : DateTimeComputationDestination) :
    (DateTimeComputationRunView.fromOutcomes input firstMessages outcomes).applyTo
        destination =
      (DateTimeComputationRunView.fromOutcomes input secondMessages outcomes).applyTo
        destination := by
  rfl

end A12Kernel
