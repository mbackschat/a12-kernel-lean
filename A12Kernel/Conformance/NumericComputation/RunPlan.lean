import A12Kernel.Conformance.NumericComputation.Table
import A12Kernel.Elaboration.NumericComputation.Run

/-! # Checked scalar Number run locks -/

namespace A12Kernel.Conformance.NumericComputation.RunPlan

open A12Kernel
open A12Kernel.Conformance.NumericComputation.Support

private def table? (target : FieldId)
    (expression : AuthoredNumericExpr SurfaceNumericAtom)
    (guard : ComputationCondition := .fieldNotFilled laterId)
    (suppressExactScaleWarning : Bool := false) :
    Option (CheckedNumericComputationTable model) := do
  let operation ← (elaborateNumericTargetComputationOperation
    model ["Root"] target expression suppressExactScaleWarning).toOption
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

private def divisionByZero :
    AuthoredNumericExpr SurfaceNumericAtom :=
  .binary .divide (literal 1) (literal 0)

private def prepared :
    PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def checkedDocument (cells : List ClassifiedCellInput := []) :
    Option (CheckedDocument model) :=
  (checkDocument prepared "en_US"
    { instantiatedRows := [], cells }).toOption

private def inputCell (field : FieldId) (stored : String) (amount : Rat) :
    ClassifiedCellInput :=
  { address := { field, path := [] }, stored, raw := .parsed (.num amount) }

private def runOutcomes?
    (tables : List (Option (CheckedNumericComputationTable model)))
    (cells : List ClassifiedCellInput := []) :
    Option (List (FieldId × NumericTargetOutcome)) := do
  let checked ← collectTables? tables
  let run ← (certifyNumericComputationRun checked).toOption
  let input ← checkedDocument cells
  (run.execute input).toOption

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

/- A completed producer shadows stale source data with its exact accepted value. -/
example :
    runOutcomes? [
      table? sourceId (literal 2),
      table? targetId (surfaceField ["Root"] "Source")]
      [inputCell sourceId "9" 9, inputCell targetId "8" 8] =
        some [
          (sourceId, .accepted { unscaled := 2, scale := 0 }),
          (targetId, .accepted { unscaled := 2, scale := 0 })] := by
  native_decide

/- A clean no-result hides the stale computed input and supplies numeric empty-as-zero downstream. -/
example :
    runOutcomes? [
      table? sourceId (literal 2) (.fieldFilled wrongId),
      table? laterId (surfaceField ["Root"] "Source")
        (.fieldNotFilled wrongId)]
      [inputCell sourceId "9" 9] =
        some [
          (sourceId, .noValue),
          (laterId, .accepted { unscaled := 0, scale := 0 })] := by
  native_decide

/- A reached domain-invalid producer becomes cause-blind poison at the consumer. -/
example :
    runOutcomes? [
      table? sourceId divisionByZero
        (suppressExactScaleWarning := true),
      table? targetId (surfaceField ["Root"] "Source")] =
        some [
          (sourceId, .invalidNoValue .calculationValue),
          (targetId, .inheritedPoison .computedDependency)] := by
  native_decide

end A12Kernel.Conformance.NumericComputation.RunPlan
