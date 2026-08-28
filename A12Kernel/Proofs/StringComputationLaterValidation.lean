import A12Kernel.Elaboration.StringComputationLaterValidation

/-! # One-level String application then Length-validation laws -/

namespace A12Kernel

/-- A String-length comparison owned by another group is rejected after successful application and before any validation row can run. -/
theorem stringComputationLaterValidation_rejects_groupMismatch
    (view : StringComputationRunView Message CellAddr)
    (destination : CheckedDocument model) (level : RepeatableLevel)
    (comparison : CheckedOrderedNumericComparison model)
    (applied : StringComputationOneLevelApplicationProjection model)
    (group : RepeatableGroupDecl)
    (application : view.applyToCheckedOneLevel destination level = .ok applied)
    (selectedGroup : model.repeatableGroupAtLevel? level = some group)
    (mismatch : comparison.rowGroup ≠ group.path) :
    view.evaluateOneLevelLengthAfterApplication destination level comparison =
      .error (.comparisonGroup group.path comparison.rowGroup) := by
  simp [StringComputationRunView.evaluateOneLevelLengthAfterApplication,
    application, selectedGroup, mismatch] <;> rfl

/-- Unsupported checked numeric atoms are rejected after successful String application and group selection rather than being collapsed to validation UNKNOWN. -/
theorem stringComputationLaterValidation_rejects_unsupported
    (view : StringComputationRunView Message CellAddr)
    (destination : CheckedDocument model) (level : RepeatableLevel)
    (comparison : CheckedOrderedNumericComparison model)
    (applied : StringComputationOneLevelApplicationProjection model)
    (group : RepeatableGroupDecl)
    (application : view.applyToCheckedOneLevel destination level = .ok applied)
    (selectedGroup : model.repeatableGroupAtLevel? level = some group)
    (sameGroup : comparison.rowGroup = group.path)
    (unsupported :
      comparison.supportsAppliedStringLengthValidation = false) :
    view.evaluateOneLevelLengthAfterApplication destination level comparison =
      .error .unsupportedComparison := by
  simp [StringComputationRunView.evaluateOneLevelLengthAfterApplication,
    application, selectedGroup, sameGroup, unsupported] <;> rfl

end A12Kernel
