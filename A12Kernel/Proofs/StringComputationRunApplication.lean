import A12Kernel.Elaboration.StringComputationRunApplication
import A12Kernel.Proofs.StringComputationApplicationFold

/-! # String whole-run application laws

These laws connect the generic exact-target fold to the one-target String owner and lock source-relative classification against destination-relative recomputation.
-/

namespace A12Kernel

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

/-- The bounded repeatable String application exposes exactly the complete predecessor prefix carried by its selected level and extent. -/
theorem stringComputationOneLevelApplication_rows_prefix
    (projection : StringComputationOneLevelApplicationProjection model) :
    projection.rows =
      (List.range projection.prefixExtent.2).map fun offset =>
        { group := projection.prefixExtent.1, path := [offset + 1] } := by
  rfl

/-- Every two-level applied String leaf is emitted in outer order from the predecessor prefix local to that exact outer coordinate. -/
theorem stringComputationTwoLevelApplication_leafRows_scopedPrefix
    (projection : StringComputationTwoLevelApplicationProjection model) :
    projection.leafRows =
      (List.range projection.outerExtent).flatMap fun outerOffset =>
        (List.range (projection.innerExtentAt (outerOffset + 1))).map
          fun innerOffset => {
            group := projection.levels.2
            path := [outerOffset + 1, innerOffset + 1]
          } := by
  simp [StringComputationTwoLevelApplicationProjection.leafRows,
    StringComputationTwoLevelApplicationProjection.outerRows,
    StringComputationTwoLevelApplicationProjection.innerRowsAt,
    StringComputationTwoLevelApplicationProjection.levels, List.flatMap_map]

end A12Kernel
