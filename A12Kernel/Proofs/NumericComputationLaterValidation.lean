import A12Kernel.Elaboration.NumericComputation.LaterValidation

/-! # One-level Number application then validation laws -/

namespace A12Kernel

/-- A comparison owned by another group is rejected after successful application and before any validation row can run. -/
theorem numericComputationLaterValidation_rejects_groupMismatch
    (view : NumericComputationRunView Message CellAddr)
    (destination : CheckedDocument model) (level : RepeatableLevel)
    (comparison : CheckedOrderedNumericComparison model)
    (applied : NumericComputationOneLevelApplicationProjection model)
    (group : RepeatableGroupDecl)
    (application : view.applyToCheckedOneLevel destination level = .ok applied)
    (selectedGroup : model.repeatableGroupAtLevel? level = some group)
    (mismatch : comparison.rowGroup ≠ group.path) :
    view.evaluateOneLevelAfterApplication destination level comparison =
      .error (.comparisonGroup group.path comparison.rowGroup) := by
  simp [NumericComputationRunView.evaluateOneLevelAfterApplication,
    application, selectedGroup, mismatch] <;> rfl

/-- Unsupported checked numeric atoms are rejected after successful application and group selection rather than being collapsed to validation UNKNOWN. -/
theorem numericComputationLaterValidation_rejects_unsupported
    (view : NumericComputationRunView Message CellAddr)
    (destination : CheckedDocument model) (level : RepeatableLevel)
    (comparison : CheckedOrderedNumericComparison model)
    (applied : NumericComputationOneLevelApplicationProjection model)
    (group : RepeatableGroupDecl)
    (application : view.applyToCheckedOneLevel destination level = .ok applied)
    (selectedGroup : model.repeatableGroupAtLevel? level = some group)
    (sameGroup : comparison.rowGroup = group.path)
    (unsupported : comparison.supportsAppliedNumberValidation = false) :
    view.evaluateOneLevelAfterApplication destination level comparison =
      .error .unsupportedComparison := by
  simp [NumericComputationRunView.evaluateOneLevelAfterApplication,
    application, selectedGroup, sameGroup, unsupported] <;> rfl

end A12Kernel
