import A12Kernel.Elaboration.FullDateComputationApplication
import A12Kernel.Proofs.FullDateApplication

/-! # Full-Date whole-result application laws -/

namespace A12Kernel

theorem fullDateComputationDestination_update_same
    (destination : FullDateComputationDestination)
    (target : FieldId) (state : FullDateTargetState) :
    destination.update target state target = state := by
  simp [FullDateComputationDestination.update,
    TemporalComputationDestination.update]

/-- One action delegates exactly to the one-target full-Date transition. -/
theorem fullDateComputationDestination_applyOutcome_same
    (destination : FullDateComputationDestination)
    (target : FieldId) (outcome : FullDateTargetOutcome) :
    destination.applyOutcome target outcome target =
      outcome.applyTo (destination target) := by
  simp [FullDateComputationDestination.applyOutcome,
    fullDateComputationDestination_update_same]

/-- A retained clear creates a present-empty destination target even when that target was absent. -/
theorem fullDateComputationDestination_applyRetainedClear_same
    (destination : FullDateComputationDestination)
    (target : FieldId) :
    destination.applyRetainedClear target target = .presentEmpty := by
  simp [FullDateComputationDestination.applyRetainedClear,
    TemporalComputationDestination.applyRetainedClear,
    TemporalComputationDestination.update,
    TemporalTargetState.applyRetainedClear]
  cases destination target <;> rfl

/-- One action preserves every other destination field. -/
theorem fullDateComputationDestination_applyOutcome_other
    (destination : FullDateComputationDestination)
    (target other : FieldId) (outcome : FullDateTargetOutcome)
    (different : other ≠ target) :
    destination.applyOutcome target outcome other = destination other := by
  simp [FullDateComputationDestination.applyOutcome,
    FullDateComputationDestination.update,
    TemporalComputationDestination.update, different]

/-- Unchanged successes and residual messages alone cannot mutate the destination. -/
theorem fullDateComputationRun_applyTo_noActions
    (view : FullDateComputationRunView ResidualMessage)
    (destination : FullDateComputationDestination)
    (noChanges : view.withChanges = [])
    (noErrors : view.withErrors = [])
    (noClears : view.cleared = []) :
    view.applyTo destination = .ok destination := by
  simp [FullDateComputationRunView.applyTo,
    FullDateComputationRunView.actionTargets, noChanges, noErrors, noClears,
    FieldId.firstDuplicate?]

/-- Duplicate action targets fail before destination state participates. -/
theorem fullDateComputationRun_applyTo_duplicateTarget
    (view : FullDateComputationRunView ResidualMessage)
    (destination : FullDateComputationDestination) (field : FieldId)
    (duplicate : FieldId.firstDuplicate? view.actionTargets = some field) :
    view.applyTo destination = .error (.duplicateActionTarget field) := by
  simp [FullDateComputationRunView.applyTo, duplicate]

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
    FullDateComputationRunView.actionTargets,
    FullDateComputationRunView.fromOutcomes,
    TemporalComputationRunView.fromErrorOutcomes,
    FullDateComputationRunView.successfulInstance?,
    FullDateComputationRunView.computedError?,
    FullDateComputationRunView.shouldClear,
    FullDateTargetOutcome.hasComputedInstance,
    FullDateComputationRunView.sourceValueChanged, unchanged,
    FieldId.firstDuplicate?]

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
    FullDateComputationRunView.actionTargets,
    FullDateComputationRunView.fromOutcomes,
    TemporalComputationRunView.fromErrorOutcomes,
    FullDateComputationRunView.successfulInstance?,
    FullDateComputationRunView.computedError?,
    FullDateComputationRunView.shouldClear,
    FullDateTargetOutcome.hasComputedInstance,
    FullDateComputationRunView.sourceValueChanged, changed,
    FieldId.firstDuplicate?]

/-- A target error applies the exact rejected-attempt clear transition and is not also a public clear. -/
theorem fullDateComputationRun_error_applies
    (input : CheckedDocument model) (messages : List ResidualMessage)
    (target : FieldId) (attempted : StoredDate) (cause : FullDateTargetError)
    (destination : FullDateComputationDestination) :
    (FullDateComputationRunView.fromOutcomes input messages
      [(target, .errored attempted cause)]).applyTo destination =
        .ok (destination.applyOutcome target (.errored attempted cause)) := by
  simp [FullDateComputationRunView.applyTo,
    FullDateComputationRunView.actionTargets,
    FullDateComputationRunView.fromOutcomes,
    TemporalComputationRunView.fromErrorOutcomes,
    FullDateComputationRunView.successfulInstance?,
    FullDateComputationRunView.computedError?,
    FullDateComputationRunView.shouldClear,
    FullDateTargetOutcome.hasComputedInstance,
    FieldId.firstDuplicate?]

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
    FullDateComputationRunView.actionTargets,
    FullDateComputationRunView.fromOutcomes,
    TemporalComputationRunView.fromErrorOutcomes,
    FullDateComputationRunView.successfulInstance?,
    FullDateComputationRunView.computedError?,
    FullDateComputationRunView.shouldClear,
    FullDateTargetOutcome.hasComputedInstance, sourceFilled,
    FieldId.firstDuplicate?]

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
