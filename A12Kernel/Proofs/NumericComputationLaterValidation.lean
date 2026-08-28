import A12Kernel.Elaboration.NumericComputation.LaterValidation

/-! # Bounded Number application then validation laws -/

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

/-- A two-level comparison owned by another group is rejected after successful application and before any concrete inner row can run. -/
theorem numericComputationTwoLevelLaterValidation_rejects_groupMismatch
    (view : NumericComputationRunView Message CellAddr)
    (destination : CheckedDocument model)
    (outer inner : RepeatableLevel)
    (comparison : CheckedOrderedNumericComparison model)
    (applied : NumericComputationTwoLevelApplicationProjection model)
    (group : RepeatableGroupDecl)
    (application :
      view.applyToCheckedTwoLevel destination outer inner = .ok applied)
    (selectedGroup : model.repeatableGroupAtLevel? inner = some group)
    (mismatch : comparison.rowGroup ≠ group.path) :
    view.evaluateTwoLevelAfterApplication
        destination outer inner comparison =
      .error (.comparisonGroup group.path comparison.rowGroup) := by
  simp [NumericComputationRunView.evaluateTwoLevelAfterApplication,
    application, selectedGroup, mismatch] <;> rfl

/-- Unsupported checked numeric atoms are rejected on the two-level route before any concrete inner row can run. -/
theorem numericComputationTwoLevelLaterValidation_rejects_unsupported
    (view : NumericComputationRunView Message CellAddr)
    (destination : CheckedDocument model)
    (outer inner : RepeatableLevel)
    (comparison : CheckedOrderedNumericComparison model)
    (applied : NumericComputationTwoLevelApplicationProjection model)
    (group : RepeatableGroupDecl)
    (application :
      view.applyToCheckedTwoLevel destination outer inner = .ok applied)
    (selectedGroup : model.repeatableGroupAtLevel? inner = some group)
    (sameGroup : comparison.rowGroup = group.path)
    (unsupported : comparison.supportsAppliedNumberValidation = false) :
    view.evaluateTwoLevelAfterApplication
        destination outer inner comparison =
      .error .unsupportedComparison := by
  simp [NumericComputationRunView.evaluateTwoLevelAfterApplication,
    application, selectedGroup, sameGroup, unsupported] <;> rfl

end A12Kernel
