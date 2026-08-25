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
      scope := plan.source.completeScope
      fieldDependencies := [
        (plan.first.placement.targetField,
          [plan.first.placement.sourceDeclaration.id]),
        (plan.second.placement.targetField,
          [plan.second.placement.sourceDeclaration.id])]
    } := by
  rfl

/-- A resolved row coordinate delegates the fixed positive guard to the shared numeric comparison owner without changing that coordinate. -/
theorem checkedCurrentRepetitionSource_positiveGuardAt
    (source : CheckedCurrentRepetitionSource model)
    (environment : Env) (coordinate : Nat)
    (found : source.coordinateAt environment = .ok coordinate) :
    source.evaluatePositiveGuardAt environment =
      .ok (coordinate, NumericComparisonOp.greater.holds coordinate 0) := by
  unfold CheckedCurrentRepetitionSource.evaluatePositiveGuardAt
  rw [found]
  rfl

/-- The shared structural guard fails closed when its exact row binding is absent. -/
theorem checkedCurrentRepetitionSource_positiveGuard_missing
    (source : CheckedCurrentRepetitionSource model) :
    source.evaluatePositiveGuardAt [] =
      .error (.missingBinding source.group.level) := by
  rfl

/-- The original same-family cascade is a specialization of the shared positive-guard law. -/
theorem checkedCurrentRepetitionNumberCascade_positiveGuardAt
    (plan : CheckedCurrentRepetitionNumberCascade model)
    (environment : Env) (coordinate : Nat)
    (found : plan.source.coordinateAt environment = .ok coordinate) :
    plan.evaluatePositiveGuardAt environment =
      .ok (coordinate, NumericComparisonOp.greater.holds coordinate 0) := by
  exact checkedCurrentRepetitionSource_positiveGuardAt
    plan.source environment coordinate found

/-- The structural guard is not a total constant: without its exact row binding, evaluation fails rather than guessing a coordinate. -/
theorem checkedCurrentRepetitionNumberCascade_positiveGuard_missing
    (plan : CheckedCurrentRepetitionNumberCascade model) :
    plan.evaluatePositiveGuardAt [] =
      .error (.missingBinding plan.source.group.level) := by
  exact checkedCurrentRepetitionSource_positiveGuard_missing plan.source

end A12Kernel
