import A12Kernel.Conformance.NumericComputation.Table
import A12Kernel.Elaboration.NumericComputation.RunPlan

/-! # Checked scalar Number run-plan locks -/

namespace A12Kernel.Conformance.NumericComputation.RunPlan

open A12Kernel
open A12Kernel.Conformance.NumericComputation.Support

private def table? (target : FieldId)
    (expression : AuthoredNumericExpr SurfaceNumericAtom)
    (guard : ComputationCondition := .fieldNotFilled laterId) :
    Option (CheckedNumericComputationTable model) := do
  let operation ← (elaborateNumericTargetComputationOperation
    model ["Root"] target expression).toOption
  (certifyNumericComputationTable [
    { precondition := guard, operation }]).toOption

private def completeTable?
    (expression : AuthoredNumericExpr SurfaceNumericComputationAtom) :
    Option (CheckedNumericComputationTable model) := do
  let operation ← (elaborateCompleteNumericTargetComputationOperation
    model ["Root"] targetId expression).toOption
  (certifyNumericComputationTable [
    { precondition := .fieldNotFilled laterId, operation }]).toOption

private def repeatableTable? :=
  completeTable? surfaceRepeatableFirstFilled

private def collectTables? :
    List (Option (CheckedNumericComputationTable model)) →
      Option (List (CheckedNumericComputationTable model))
  | [] => some []
  | some table :: remaining => (table :: ·) <$> collectTables? remaining
  | none :: _ => none

private def runError?
    (tables : List (Option (CheckedNumericComputationTable model))) :
    Option NumericComputationRunPlanError := do
  let checked ← collectTables? tables
  match certifyNumericComputationRun checked with
  | .error error => some error
  | .ok _ => none

private def runTargets?
    (tables : List (Option (CheckedNumericComputationTable model))) :
    Option (List FieldId) := do
  let checked ← collectTables? tables
  let run ← (certifyNumericComputationRun checked).toOption
  pure (run.tables.map (·.targetField))

private def literal (value : Rat) :
    AuthoredNumericExpr SurfaceNumericAtom :=
  .literal { value, authoredScale := 0 }

/- The scalar plan rejects empty input and the first table whose selected operation could require repeatable context. -/
example :
    runError? [] = some .empty ∧
    runError? [repeatableTable?] =
        some (.repeatableContextRequired targetId) ∧
    runError? [completeTable? (surfaceRepeatableValueCount 1)] =
        some (.repeatableContextRequired targetId) ∧
    runError? [completeTable? (surfaceRepeatableTokenValueCount "X")] =
        some (.repeatableContextRequired targetId) ∧
    runError? [completeTable? surfaceProductAggregate] =
        some (.repeatableContextRequired targetId) ∧
    runError? [completeTable?
      ((surfaceRepeatableAggregate .sum).map
        SurfaceNumericComputationAtom.numeric)] =
      some (.repeatableContextRequired targetId) := by
  native_decide

/- Target uniqueness is structural and independent of operation contents. -/
example :
    runError? [table? sourceId (literal 1), table? sourceId (literal 2)] =
      some (.duplicateTarget sourceId) := by
  native_decide

/- A computed dependency must precede its consumer, whether the read occurs in the Numeric tree or a direct-presence guard. -/
example :
    runError? [
      table? targetId (surfaceField ["Root"] "Source"),
      table? sourceId (literal 2)] =
        some (.forwardDependency targetId sourceId) ∧
    runError? [
      table? targetId (literal 3) (.fieldFilled sourceId),
      table? sourceId (literal 2)] =
        some (.forwardDependency targetId sourceId) := by
  native_decide

/- The same dependency is accepted in producer-first order without changing supplied order. -/
example :
    runTargets? [
      table? sourceId (literal 2),
      table? targetId (surfaceField ["Root"] "Source")] =
        some [sourceId, targetId] ∧
    runTargets? [completeTable? (surfaceFirstFilled
      (.field (surfacePath ["Root"] "Source"))
      [.field (surfacePath ["Root"] "Later")])] =
        some [targetId] := by
  native_decide

end A12Kernel.Conformance.NumericComputation.RunPlan
