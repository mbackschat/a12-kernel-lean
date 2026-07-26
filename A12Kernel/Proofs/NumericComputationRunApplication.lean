import A12Kernel.Elaboration.NumericComputation.RunApplication
import A12Kernel.Proofs.NumericApplication

/-! # Number whole-run application laws -/

namespace A12Kernel

theorem numericComputationDestination_update_same
    (destination : NumericComputationDestination)
    (target : FieldId) (state : NumericTargetState) :
    destination.update target state target = state := by
  simp [NumericComputationDestination.update]

/-- One action delegates exactly to the one-target Number transition. -/
theorem numericComputationDestination_applyOutcome_same
    (destination : NumericComputationDestination)
    (target : FieldId) (outcome : NumericTargetOutcome) :
    destination.applyOutcome target outcome target =
      outcome.applyTo (destination target) := by
  simp [NumericComputationDestination.applyOutcome,
    numericComputationDestination_update_same]

/-- One action preserves every other destination projection. -/
theorem numericComputationDestination_applyOutcome_other
    (destination : NumericComputationDestination)
    (target other : FieldId) (outcome : NumericTargetOutcome)
    (different : other ≠ target) :
    destination.applyOutcome target outcome other = destination other := by
  simp [NumericComputationDestination.applyOutcome,
    NumericComputationDestination.update, different]

/-- Unchanged successes and residual messages alone cannot mutate the destination. -/
theorem numericComputationRun_applyTo_noActions
    (view : NumericComputationRunView ResidualMessage)
    (destination : NumericComputationDestination)
    (noChanges : view.withChanges = [])
    (noErrors : view.withErrors = [])
    (noClears : view.cleared = []) :
    view.applyTo destination = .ok destination := by
  simp [NumericComputationRunView.applyTo,
    NumericComputationRunView.actionTargets, noChanges, noErrors, noClears,
    FieldId.firstDuplicate?]

/-- Duplicate action targets fail before destination state participates. -/
theorem numericComputationRun_applyTo_duplicateTarget
    (view : NumericComputationRunView ResidualMessage)
    (destination : NumericComputationDestination) (field : FieldId)
    (duplicate : FieldId.firstDuplicate? view.actionTargets = some field) :
    view.applyTo destination =
      .error (.duplicateActionTarget field) := by
  simp [NumericComputationRunView.applyTo, duplicate]

/-- Residual messages affect result status but never the application plan. -/
theorem numericComputationRun_residualMessages_doNotAffectApplication
    (firstMessages secondMessages : List ResidualMessage)
    (entries : List SourcedNumericTargetOutcome)
    (destination : NumericComputationDestination) :
    (NumericComputationRunView.fromSourceOutcomes
      firstMessages entries).applyTo destination =
    (NumericComputationRunView.fromSourceOutcomes
      secondMessages entries).applyTo destination := by
  rfl

end A12Kernel
