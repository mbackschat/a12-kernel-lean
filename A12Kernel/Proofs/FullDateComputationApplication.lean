import A12Kernel.Proofs.TemporalErroredComputationApplication
import A12Kernel.Proofs.FullDateApplication

/-! # Full-Date whole-result application laws -/

namespace A12Kernel

theorem fullDateComputationDestination_update_same
    {Target : Type} [DecidableEq Target]
    (destination : FullDateComputationDestination Target)
    (target : Target) (state : FullDateTargetState) :
    destination.update target state target = state := by
  simpa [FullDateComputationDestination.update] using
    temporalComputationDestination_update_same destination target state

/-- One action delegates exactly to the one-target full-Date transition. -/
theorem fullDateComputationDestination_applyOutcome_same
    {Target : Type} [DecidableEq Target]
    (destination : FullDateComputationDestination Target)
    (target : Target) (outcome : FullDateTargetOutcome) :
    destination.applyOutcome target outcome target =
      outcome.applyTo (destination target) := by
  simp [FullDateComputationDestination.applyOutcome,
    fullDateComputationDestination_update_same]

/-- A retained clear creates a present-empty destination target even when that target was absent. -/
theorem fullDateComputationDestination_applyRetainedClear_same
    {Target : Type} [DecidableEq Target]
    (destination : FullDateComputationDestination Target)
    (target : Target) :
    destination.applyRetainedClear target target = .presentEmpty := by
  simpa [FullDateComputationDestination.applyRetainedClear] using
    temporalComputationDestination_applyRetainedClear_same destination target

/-- One action preserves every other destination field. -/
theorem fullDateComputationDestination_applyOutcome_other
    {Target : Type} [DecidableEq Target]
    (destination : FullDateComputationDestination Target)
    (target other : Target) (outcome : FullDateTargetOutcome)
    (different : other ≠ target) :
    destination.applyOutcome target outcome other = destination other := by
  simp [FullDateComputationDestination.applyOutcome,
    FullDateComputationDestination.update,
    TemporalComputationDestination.update, different]

/-- Unchanged successes and residual messages alone cannot mutate the destination. -/
theorem fullDateComputationRun_applyTo_noActions
    {Target : Type} [DecidableEq Target]
    (view : FullDateComputationRunView ResidualMessage Target)
    (destination : FullDateComputationDestination Target)
    (noChanges : view.withChanges = [])
    (noErrors : view.withErrors = [])
    (noClears : view.cleared = []) :
    view.applyTo destination = .ok destination := by
  simp [FullDateComputationRunView.applyTo,
    noChanges, noErrors, noClears,
    TemporalErroredComputationRunView.applyTo,
    TemporalErroredComputationRunView.actionTargets,
    TemporalComputationApplicationTarget.firstDuplicate?]

/-- Duplicate action targets fail before destination state participates. -/
theorem fullDateComputationRun_applyTo_duplicateTarget
    {Target : Type} [DecidableEq Target]
    (view : FullDateComputationRunView ResidualMessage Target)
    (destination : FullDateComputationDestination Target) (field : Target)
    (duplicate :
      TemporalComputationApplicationTarget.firstDuplicate?
        view.actionTargets = some field) :
    view.applyTo destination = .error (.duplicateActionTarget field) := by
  unfold FullDateComputationRunView.applyTo
  unfold TemporalErroredComputationRunView.applyTo
  rw [show TemporalComputationApplicationTarget.firstDuplicate?
      (TemporalErroredComputationRunView.actionTargets view
        (fun computed => computed.targetField)
        (fun computed => computed.targetField)) = some field by
    simpa [FullDateComputationRunView.actionTargets] using duplicate]

/-- A checked FullDate application with admitted unique targets delegates exactly to the established target-state fold over the checked document's source projection. -/
theorem fullDateComputationRun_applyToChecked_delegates
    (view : FullDateComputationRunView ResidualMessage)
    (destination : CheckedDocument model)
    (unique : FieldId.firstDuplicate? view.actionTargets = none)
    (valid : FullDateComputationRunView.validateActionTargets model
      view.actionTargets = .ok ()) :
    view.applyToChecked destination =
      view.applyTo destination.sourceFullDateTargetState := by
  simp [FullDateComputationRunView.applyToChecked, unique, valid]
  rfl

/-- A source-unchanged accepted Date is not applied to a different destination. -/
theorem fullDateComputationRun_unchanged_notApplied
    (input : CheckedDocument model) (messages : List ResidualMessage)
    (target : FieldId) (value : StoredDate)
    (destination : FullDateComputationDestination)
    (unchanged :
      (input.sourceFullDateTargetState target).storedValue = some value) :
    (FullDateComputationRunView.fromOutcomes input messages
      [(target, .accepted value)]).applyTo destination = .ok destination := by
  simp [FullDateComputationRunView.applyTo,
    TemporalErroredComputationRunView.applyTo,
    TemporalErroredComputationRunView.actionTargets,
    FullDateComputationRunView.fromOutcomes,
    FullDateComputationRunView.fromOutcomesAt,
    TemporalComputationRunView.fromErrorOutcomes,
    FullDateComputationRunView.successfulInstance?,
    FullDateComputationRunView.computedError?,
    FullDateComputationRunView.shouldClearAt,
    FullDateTargetOutcome.hasComputedInstance,
    FullDateComputationRunView.sourceValueChangedAt, unchanged,
    TemporalComputationApplicationTarget.firstDuplicate?]

/-- A source-changed accepted Date applies the existing one-target write. -/
theorem fullDateComputationRun_changed_applies
    (input : CheckedDocument model) (messages : List ResidualMessage)
    (target : FieldId) (value : StoredDate)
    (destination : FullDateComputationDestination)
    (changed :
      (input.sourceFullDateTargetState target).storedValue != some value) :
    (FullDateComputationRunView.fromOutcomes input messages
      [(target, .accepted value)]).applyTo destination =
        .ok (destination.applyOutcome target (.accepted value)) := by
  simp [FullDateComputationRunView.applyTo,
    TemporalErroredComputationRunView.applyTo,
    TemporalErroredComputationRunView.actionTargets,
    FullDateComputationRunView.fromOutcomes,
    FullDateComputationRunView.fromOutcomesAt,
    TemporalComputationRunView.fromErrorOutcomes,
    FullDateComputationRunView.successfulInstance?,
    FullDateComputationRunView.computedError?,
    FullDateComputationRunView.shouldClearAt,
    FullDateTargetOutcome.hasComputedInstance,
    FullDateComputationRunView.sourceValueChangedAt, changed,
    TemporalComputationApplicationTarget.firstDuplicate?]

/-- A target error applies the exact rejected-attempt clear transition and is not also a public clear. -/
theorem fullDateComputationRun_error_applies
    (input : CheckedDocument model) (messages : List ResidualMessage)
    (target : FieldId) (attempted : StoredDate) (cause : FullDateTargetError)
    (destination : FullDateComputationDestination) :
    (FullDateComputationRunView.fromOutcomes input messages
      [(target, .errored attempted cause)]).applyTo destination =
        .ok (destination.applyOutcome target (.errored attempted cause)) := by
  simp [FullDateComputationRunView.applyTo,
    TemporalErroredComputationRunView.applyTo,
    TemporalErroredComputationRunView.actionTargets,
    FullDateComputationRunView.fromOutcomes,
    FullDateComputationRunView.fromOutcomesAt,
    TemporalComputationRunView.fromErrorOutcomes,
    FullDateComputationRunView.successfulInstance?,
    FullDateComputationRunView.computedError?,
    FullDateComputationRunView.shouldClearAt,
    FullDateTargetOutcome.hasComputedInstance,
    TemporalComputationApplicationTarget.firstDuplicate?]

/-- A source-filled quiet no-value mints a retained clear action that creates or retains a present-empty destination target. -/
theorem fullDateComputationRun_cleared_applies
    (input : CheckedDocument model) (messages : List ResidualMessage)
    (target : FieldId) (destination : FullDateComputationDestination)
    (sourceFilled :
      (input.sourceFullDateTargetState target).storedValue.isSome = true) :
    (FullDateComputationRunView.fromOutcomes input messages
      [(target, .noValue)]).applyTo destination =
        .ok (destination.applyRetainedClear target) := by
  simp [FullDateComputationRunView.applyTo,
    TemporalErroredComputationRunView.applyTo,
    TemporalErroredComputationRunView.actionTargets,
    FullDateComputationRunView.fromOutcomes,
    FullDateComputationRunView.fromOutcomesAt,
    TemporalComputationRunView.fromErrorOutcomes,
    FullDateComputationRunView.successfulInstance?,
    FullDateComputationRunView.computedError?,
    FullDateComputationRunView.shouldClearAt,
    FullDateTargetOutcome.hasComputedInstance, sourceFilled,
    TemporalComputationApplicationTarget.firstDuplicate?]

/-- Residual messages affect error status but never the already-classified application actions. -/
theorem fullDateComputationRun_residualMessages_doNotAffectApplication
    (input : CheckedDocument model)
    (firstMessages secondMessages : List ResidualMessage)
    (outcomes : List (FieldId × FullDateTargetOutcome))
    (destination : FullDateComputationDestination) :
    (FullDateComputationRunView.fromOutcomes input firstMessages outcomes).applyTo
        destination =
      (FullDateComputationRunView.fromOutcomes input secondMessages outcomes).applyTo
        destination := by
  rfl

end A12Kernel
