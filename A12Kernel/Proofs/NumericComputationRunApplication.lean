import A12Kernel.Elaboration.NumericComputation.RunApplication
import A12Kernel.Proofs.NumericComputationApplicationFold

/-! # Number whole-run application laws -/

namespace A12Kernel

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

/-- The bounded applied-document view exposes rows in exact numeric predecessor order, independently of the retained action-category order that materialized them. -/
theorem numericComputationOneLevelApplication_rows_prefix
    (projection : NumericComputationOneLevelApplicationProjection model) :
    projection.rows =
      (List.range projection.prefixExtent.2).map fun offset =>
        { group := projection.prefixExtent.1, path := [offset + 1] } := by
  rfl

/-- Every two-level applied leaf is emitted in outer order from the predecessor prefix local to that exact outer coordinate. -/
theorem numericComputationTwoLevelApplication_leafRows_scopedPrefix
    (projection : NumericComputationTwoLevelApplicationProjection model) :
    projection.leafRows =
      (List.range projection.outerExtent).flatMap fun outerOffset =>
        (List.range (projection.innerExtentAt (outerOffset + 1))).map
          fun innerOffset => {
            group := projection.levels.2
            path := [outerOffset + 1, innerOffset + 1]
          } := by
  simp [NumericComputationTwoLevelApplicationProjection.leafRows,
    NumericComputationTwoLevelApplicationProjection.outerRows,
    NumericComputationTwoLevelApplicationProjection.innerRowsAt,
    NumericComputationTwoLevelApplicationProjection.levels, List.flatMap_map]

end A12Kernel
