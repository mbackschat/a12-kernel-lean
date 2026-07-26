import A12Kernel.Elaboration.StringComputationRunApplication
import A12Kernel.Proofs.StringApplication

/-! # String whole-run application laws

These laws connect the fold to the exact one-target owner and lock source-relative classification against destination-relative recomputation.
-/

namespace A12Kernel

/-- Updating one destination target yields exactly the supplied state there. -/
theorem stringComputationDestination_update_same
    (destination : StringComputationDestination)
    (target : FieldId) (state : StringTargetState) :
    destination.update target state target = state := by
  simp [StringComputationDestination.update]

/-- A one-target application delegates exactly to `StringTargetOutcome.applyTo`. -/
theorem stringComputationDestination_applyOutcome_same
    (destination : StringComputationDestination)
    (target : FieldId) (outcome : StringTargetOutcome) :
    destination.applyOutcome target outcome target =
      outcome.applyTo (destination target) := by
  simp [StringComputationDestination.applyOutcome,
    stringComputationDestination_update_same]

/-- Applying one target preserves every other destination projection. -/
theorem stringComputationDestination_applyOutcome_other
    (destination : StringComputationDestination)
    (target other : FieldId) (outcome : StringTargetOutcome)
    (different : other ≠ target) :
    destination.applyOutcome target outcome other = destination other := by
  simp [StringComputationDestination.applyOutcome,
    StringComputationDestination.update, different]

/-- A result with no changed, errored, or cleared action leaves the destination untouched even when `withoutErrors` or residual messages are nonempty. -/
theorem stringComputationRun_applyTo_noActions
    (view : StringComputationRunView ResidualMessage)
    (destination : StringComputationDestination)
    (noChanges : view.withChanges = [])
    (noErrors : view.withErrors = [])
    (noClears : view.cleared = []) :
    view.applyTo destination = .ok destination := by
  simp [StringComputationRunView.applyTo,
    StringComputationRunView.actionTargets, noChanges, noErrors, noClears,
    FieldId.firstDuplicate?]

/-- Duplicate action targets fail before any destination state is selected or changed. -/
theorem stringComputationRun_applyTo_duplicateTarget
    (view : StringComputationRunView ResidualMessage)
    (destination : StringComputationDestination) (field : FieldId)
    (duplicate : FieldId.firstDuplicate? view.actionTargets = some field) :
    view.applyTo destination =
      .error (.duplicateActionTarget field) := by
  simp [StringComputationRunView.applyTo, duplicate]

/-- A source-unchanged success is not applied, even when the caller-supplied destination contains another value. -/
theorem stringComputationRun_unchanged_notApplied
    (input : CheckedDocument model) (residualMessages : List ResidualMessage)
    (target : FieldId) (value : StoredString)
    (destination : StringComputationDestination)
    (unchanged :
      (input.sourceStringTargetState target).storedValue = some value) :
    (StringComputationRunView.fromOutcomes input residualMessages
      [(target, .accepted value)]).applyTo destination = .ok destination := by
  simp [StringComputationRunView.applyTo,
    StringComputationRunView.actionTargets,
    StringComputationRunView.fromOutcomes,
    StringComputationRunView.successfulInstance?,
    StringComputationRunView.computedError?,
    StringComputationRunView.shouldClear,
    StringTargetOutcome.hasComputedInstance,
    StringComputationRunView.sourceValueChanged, unchanged,
    FieldId.firstDuplicate?]

/-- A source-changed success applies the existing accepted-value transition at its target. -/
theorem stringComputationRun_changed_applies
    (input : CheckedDocument model) (residualMessages : List ResidualMessage)
    (target : FieldId) (value : StoredString)
    (destination : StringComputationDestination)
    (changed :
      (input.sourceStringTargetState target).storedValue != some value) :
    (StringComputationRunView.fromOutcomes input residualMessages
      [(target, .accepted value)]).applyTo destination =
        .ok (destination.applyOutcome target (.accepted value)) := by
  simp [StringComputationRunView.applyTo,
    StringComputationRunView.actionTargets,
    StringComputationRunView.fromOutcomes,
    StringComputationRunView.successfulInstance?,
    StringComputationRunView.computedError?,
    StringComputationRunView.shouldClear,
    StringTargetOutcome.hasComputedInstance,
    StringComputationRunView.sourceValueChanged, changed,
    FieldId.firstDuplicate?]

/-- A payloadful target error applies the existing error transition and is not also consumed by the cleared collection. -/
theorem stringComputationRun_error_applies
    (input : CheckedDocument model) (residualMessages : List ResidualMessage)
    (target : FieldId) (attempted : StoredString) (cause : StringTargetError)
    (destination : StringComputationDestination) :
    (StringComputationRunView.fromOutcomes input residualMessages
      [(target, .errored attempted cause)]).applyTo destination =
        .ok (destination.applyOutcome target (.errored attempted cause)) := by
  simp [StringComputationRunView.applyTo,
    StringComputationRunView.actionTargets,
    StringComputationRunView.fromOutcomes,
    StringComputationRunView.successfulInstance?,
    StringComputationRunView.computedError?,
    StringComputationRunView.shouldClear,
    StringTargetOutcome.hasComputedInstance,
    FieldId.firstDuplicate?]

/-- A source-filled clean no-value applies the existing clearing transition against the destination without creating an absent target. -/
theorem stringComputationRun_cleared_applies
    (input : CheckedDocument model) (residualMessages : List ResidualMessage)
    (target : FieldId) (destination : StringComputationDestination)
    (sourceFilled :
      (input.sourceStringTargetState target).storedValue.isSome = true) :
    (StringComputationRunView.fromOutcomes input residualMessages
      [(target, .noValue)]).applyTo destination =
        .ok (destination.applyOutcome target .noValue) := by
  simp [StringComputationRunView.applyTo,
    StringComputationRunView.actionTargets,
    StringComputationRunView.fromOutcomes,
    StringComputationRunView.successfulInstance?,
    StringComputationRunView.computedError?,
    StringComputationRunView.shouldClear,
    StringTargetOutcome.hasComputedInstance, sourceFilled,
    FieldId.firstDuplicate?]

/-- Residual messages affect the error predicate but never the already-classified application plan. -/
theorem stringComputationRun_residualMessages_doNotAffectApplication
    (input : CheckedDocument model)
    (firstMessages secondMessages : List ResidualMessage)
    (outcomes : List (FieldId × StringTargetOutcome))
    (destination : StringComputationDestination) :
    (StringComputationRunView.fromOutcomes input firstMessages outcomes).applyTo destination =
      (StringComputationRunView.fromOutcomes input secondMessages outcomes).applyTo destination := by
  rfl

end A12Kernel
