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
    (noClears : view.cleared = []) :
    view.applyTo destination = .ok destination := by
  simp [DateTimeComputationRunView.applyTo,
    TemporalValueComputationRunView.applyTo,
    TemporalValueComputationRunView.actionTargets, noChanges, noClears,
    FieldId.firstDuplicate?]

/-- Duplicate action targets fail before destination state participates. -/
theorem dateTimeComputationRun_applyTo_duplicateTarget
    (view : DateTimeComputationRunView ResidualMessage)
    (destination : DateTimeComputationDestination) (field : FieldId)
    (duplicate : FieldId.firstDuplicate? view.actionTargets = some field) :
    view.applyTo destination = .error (.duplicateActionTarget field) := by
  have duplicate' :
      FieldId.firstDuplicate?
        (TemporalValueComputationRunView.actionTargets view) =
          some field := by
    simpa [DateTimeComputationRunView.actionTargets] using duplicate
  simp [DateTimeComputationRunView.applyTo,
    TemporalValueComputationRunView.applyTo,
    duplicate']

/-- A source-unchanged accepted DateTime is not applied to a different destination. -/
theorem dateTimeComputationRun_unchanged_notApplied
    (input : CheckedDocument model) (messages : List ResidualMessage)
    (target : FieldId) (value : StoredDateTime)
    (destination : DateTimeComputationDestination)
    (unchanged :
      (input.sourceDateTimeTargetState target).storedValue = some value) :
    (DateTimeComputationRunView.fromOutcomes input messages
      [(target, .accepted value)]).applyTo destination = .ok destination := by
  simp [DateTimeComputationRunView.applyTo,
    TemporalValueComputationRunView.applyTo,
    TemporalValueComputationRunView.actionTargets,
    DateTimeComputationRunView.fromOutcomes,
    TemporalComputationRunView.fromValueOutcomes,
    DateTimeComputationRunView.successfulInstance?,
    DateTimeComputationRunView.shouldClear,
    DateTimeTargetOutcome.hasComputedInstance,
    DateTimeComputationRunView.sourceValueChanged, unchanged,
    FieldId.firstDuplicate?]

/-- A source-changed accepted DateTime applies the existing one-target write. -/
theorem dateTimeComputationRun_changed_applies
    (input : CheckedDocument model) (messages : List ResidualMessage)
    (target : FieldId) (value : StoredDateTime)
    (destination : DateTimeComputationDestination)
    (changed :
      (input.sourceDateTimeTargetState target).storedValue != some value) :
    (DateTimeComputationRunView.fromOutcomes input messages
      [(target, .accepted value)]).applyTo destination =
        .ok (destination.applyOutcome target (.accepted value)) := by
  simp [DateTimeComputationRunView.applyTo,
    TemporalValueComputationRunView.applyTo,
    TemporalValueComputationRunView.actionTargets,
    DateTimeComputationRunView.fromOutcomes,
    TemporalComputationRunView.fromValueOutcomes,
    DateTimeComputationRunView.successfulInstance?,
    DateTimeComputationRunView.shouldClear,
    DateTimeTargetOutcome.hasComputedInstance,
    DateTimeComputationRunView.sourceValueChanged, changed,
    FieldId.firstDuplicate?]

/-- A source-filled quiet no-value applies the existing clearing transition. -/
theorem dateTimeComputationRun_cleared_applies
    (input : CheckedDocument model) (messages : List ResidualMessage)
    (target : FieldId) (destination : DateTimeComputationDestination)
    (sourceFilled :
      (input.sourceDateTimeTargetState target).storedValue.isSome = true) :
    (DateTimeComputationRunView.fromOutcomes input messages
      [(target, .noValue)]).applyTo destination =
        .ok (destination.applyOutcome target .noValue) := by
  simp [DateTimeComputationRunView.applyTo,
    TemporalValueComputationRunView.applyTo,
    TemporalValueComputationRunView.actionTargets,
    DateTimeComputationRunView.fromOutcomes,
    TemporalComputationRunView.fromValueOutcomes,
    DateTimeComputationRunView.successfulInstance?,
    DateTimeComputationRunView.shouldClear,
    DateTimeTargetOutcome.hasComputedInstance, sourceFilled,
    FieldId.firstDuplicate?]

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
