import A12Kernel.Elaboration.NumericComputation.RunApplication
import A12Kernel.Proofs.NumericApplication

/-! # Number whole-run application laws -/

namespace A12Kernel

theorem numericComputationDestination_update_same
    {Target : Type} [DecidableEq Target]
    (destination : NumericComputationDestination Target)
    (target : Target) (state : NumericTargetState) :
    destination.update target state target = state := by
  simp [NumericComputationDestination.update]

/-- One action delegates exactly to the one-target Number transition. -/
theorem numericComputationDestination_applyOutcome_same
    {Target : Type} [DecidableEq Target]
    (destination : NumericComputationDestination Target)
    (target : Target) (outcome : NumericTargetOutcome) :
    destination.applyOutcome target outcome target =
      outcome.applyTo (destination target) := by
  simp [NumericComputationDestination.applyOutcome,
    numericComputationDestination_update_same]

/-- A retained clear creates a present-empty destination target even when that target was absent. -/
theorem numericComputationDestination_applyRetainedClear_same
    {Target : Type} [DecidableEq Target]
    (destination : NumericComputationDestination Target)
    (target : Target) :
    destination.applyRetainedClear target target = .presentEmpty := by
  rw [NumericComputationDestination.applyRetainedClear,
    numericComputationDestination_update_same]
  cases destination target <;> rfl

/-- One action preserves every other destination projection. -/
theorem numericComputationDestination_applyOutcome_other
    {Target : Type} [DecidableEq Target]
    (destination : NumericComputationDestination Target)
    (target other : Target) (outcome : NumericTargetOutcome)
    (different : other ≠ target) :
    destination.applyOutcome target outcome other = destination other := by
  simp [NumericComputationDestination.applyOutcome,
    NumericComputationDestination.update, different]

/-- Unchanged successes and residual messages alone cannot mutate the destination. -/
theorem numericComputationRun_applyTo_noActions
    {Target : Type} [DecidableEq Target]
    (view : NumericComputationRunView ResidualMessage Target)
    (destination : NumericComputationDestination Target)
    (noChanges : view.withChanges = [])
    (noErrors : view.withErrors = [])
    (noClears : view.cleared = []) :
    view.applyTo destination = .ok destination := by
  simp [NumericComputationRunView.applyTo,
    NumericComputationRunView.firstDuplicateActionTarget?,
    NumericComputationRunView.firstDuplicateActionTarget?.firstDuplicate?,
    NumericComputationRunView.actionTargets, noChanges, noErrors, noClears]

/-- A retained result with no actions preserves the separately supplied checked destination projection exactly. -/
theorem numericComputationRun_applyToChecked_noActions
    (view : NumericComputationRunView ResidualMessage CellAddr)
    (destination : CheckedDocument model)
    (noChanges : view.withChanges = [])
    (noErrors : view.withErrors = [])
    (noClears : view.cleared = []) :
    view.applyToChecked destination =
      .ok (NumericComputationApplicationProjection.ofChecked destination) := by
  simp [NumericComputationRunView.applyToChecked,
    NumericComputationRunView.firstDuplicateActionTarget?,
    NumericComputationRunView.firstDuplicateActionTarget?.firstDuplicate?,
    NumericComputationRunView.actionTargets, noChanges, noErrors, noClears,
    Pure.pure, Except.pure, Bind.bind, Except.bind]

/-- A singleton source-classified clear reaches present-empty through the checked destination boundary whenever that destination admits the action address. -/
theorem numericComputationRun_applyToChecked_singletonClear_state
    (view : NumericComputationRunView ResidualMessage CellAddr)
    (destination : CheckedDocument model) (target : CellAddr)
    (rows : List RowAddr)
    (noDuplicate : view.firstDuplicateActionTarget? = none)
    (singleClear : view.cleared = [target])
    (noErrors : view.withErrors = [])
    (noChanges : view.withChanges = [])
    (admitted :
      numericComputationActionRowsFor model target = .ok rows) :
    (view.applyToChecked destination).map
        (fun projection => projection.stateAt target) =
      .ok .presentEmpty := by
  simp [NumericComputationRunView.applyToChecked,
    noDuplicate, singleClear, noErrors, noChanges, admitted,
    NumericComputationApplicationProjection.ofChecked,
    NumericComputationApplicationProjection.applyRetainedClearAt,
    NumericComputationApplicationProjection.stateAt,
    Pure.pure, Except.pure, Bind.bind, Except.bind, Except.map]
  cases destination.numericTargetPlacementStateAt target <;>
    simp [NumericTargetState.applyRetainedClear]

/-- Duplicate action targets fail before destination state participates. -/
theorem numericComputationRun_applyTo_duplicateTarget
    {Target : Type} [DecidableEq Target]
    (view : NumericComputationRunView ResidualMessage Target)
    (destination : NumericComputationDestination Target) (target : Target)
    (duplicate : view.firstDuplicateActionTarget? = some target) :
    view.applyTo destination =
      .error (.duplicateActionTarget target) := by
  simp [NumericComputationRunView.applyTo, duplicate]

/-- Residual messages affect result status but never the application plan. -/
theorem numericComputationRun_residualMessages_doNotAffectApplication
    {Target : Type} [DecidableEq Target]
    (firstMessages secondMessages : List ResidualMessage)
    (entries : List (SourcedNumericTargetOutcome Target))
    (destination : NumericComputationDestination Target) :
    (NumericComputationRunView.fromPartitionedSourceOutcomes
      firstMessages entries).applyTo destination =
    (NumericComputationRunView.fromPartitionedSourceOutcomes
      secondMessages entries).applyTo destination := by
  rfl

end A12Kernel
