import A12Kernel.Elaboration.CurrentRepetitionComputation

/-! # Exact CurrentRepetition computation-cascade laws -/

namespace A12Kernel

/-- Analyze never reclassifies the structural coordinate as a field dependency. -/
@[simp]
theorem checkedCurrentRepetitionSource_referencesField_false
    (source : CheckedCurrentRepetitionSource model) (field : FieldId) :
    source.referencesField field = false := by
  rfl

/-- The bounded Analyze view preserves the exact structural group and the two authored field edges in execution order. -/
@[simp]
theorem checkedCurrentRepetitionNumberCascade_analyze
    (plan : CheckedCurrentRepetitionNumberCascade model) :
    plan.analyze = {
      structuralGroup := plan.source.path
      scope := [plan.source.group.level]
      fieldDependencies := [
        (plan.first.placement.targetField,
          [plan.first.placement.sourceDeclaration.id]),
        (plan.second.placement.targetField,
          [plan.second.placement.sourceDeclaration.id])]
    } := by
  rfl

/-- A resolved row coordinate delegates the fixed positive guard to the shared numeric comparison owner without changing that coordinate. -/
theorem checkedCurrentRepetitionNumberCascade_positiveGuardAt
    (plan : CheckedCurrentRepetitionNumberCascade model)
    (environment : Env) (coordinate : Nat)
    (found : plan.source.coordinateAt environment = .ok coordinate) :
    plan.evaluatePositiveGuardAt environment =
      .ok (coordinate, NumericComparisonOp.greater.holds coordinate 0) := by
  unfold CheckedCurrentRepetitionNumberCascade.evaluatePositiveGuardAt
  rw [found]
  rfl

/-- The structural guard is not a total constant: without its exact row binding, evaluation fails rather than guessing a coordinate. -/
theorem checkedCurrentRepetitionNumberCascade_positiveGuard_missing
    (plan : CheckedCurrentRepetitionNumberCascade model) :
    plan.evaluatePositiveGuardAt [] =
      .error (.missingBinding plan.source.group.level) := by
  rfl

end A12Kernel
