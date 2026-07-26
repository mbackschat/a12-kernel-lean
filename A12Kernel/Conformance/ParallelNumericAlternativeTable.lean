import A12Kernel.Elaboration.ParallelNumericAlternativeTable
import A12Kernel.Conformance.ParallelNumericThreeGroupOperands

/-! # Parallel Number alternative-table locks

These cases reuse the scalar first-selected owner while keeping every row's checked parallel operation intact.
-/

namespace A12Kernel.Conformance.ParallelNumericAlternativeTable

open A12Kernel
open A12Kernel.Conformance.ParallelNumericThreeGroupOperands

private def literal (value : Rat) : AuthoredNumericExpr SurfaceNumericAtom :=
  .literal { value, authoredScale := 0 }

private def input : AuthoredNumericExpr SurfaceNumericAtom := .atom (.field inputPath)

private def plusOne : AuthoredNumericExpr SurfaceNumericAtom :=
  .binary .add input (literal 1)

private def divideByZero : AuthoredNumericExpr SurfaceNumericAtom :=
  .binary .divide input (literal 0)

private def row? (guard : ComputationCondition)
    (expression : AuthoredNumericExpr SurfaceNumericAtom)
    (suppressExactScaleWarning : Bool := false) :=
  (checkIsolatedParallelNumericExpressionRunWithGuard
    model ["Plan"] 2 inputPath expression (some guard)
      suppressExactScaleWarning).toOption

private def secondTargetModel : FlatModel := {
  model with
  fields := model.fields ++ [{
    id := 9
    groupPath := ["Plan", "Target"]
    name := "OtherResult"
    policy := { kind := .number { scale := 0, signed := false } }
    repeatableScope := [1]
  }]
}

private def secondModelRow? (target : FieldId)
    (expression : AuthoredNumericExpr SurfaceNumericAtom)
    (guard : ComputationCondition) :=
  (checkIsolatedParallelNumericExpressionRunWithGuard
    secondTargetModel ["Plan"] target inputPath expression
      (some guard)).toOption

private def collectRows? :
    List (Option (CheckedIsolatedParallelNumericDirectRun model)) →
      Option (List (CheckedIsolatedParallelNumericDirectRun model))
  | [] => some []
  | some row :: remaining => (row :: ·) <$> collectRows? remaining
  | none :: _ => none

private def tableError?
    (rows : List (Option (CheckedIsolatedParallelNumericDirectRun model))) :
    Option ParallelNumericAlternativeTableError := do
  let checked ← collectRows? rows
  match certifyParallelNumericAlternativeTable checked with
  | .error error => some error
  | .ok _ => none

private def checkedNumber (raw : RawCell) : CheckedCell :=
  formalCheck { kind := .number { scale := 0, signed := false } } raw

private def context (amount : CheckedCell := checkedNumber .empty) :
    ScalarComputationContext where
  read field :=
    if field == 4 then amount
    else malformedCheckedCell

private def tableOutcome?
    (rows : List (Option (CheckedIsolatedParallelNumericDirectRun model)))
    (inputContext : ScalarComputationContext := context) :
    Option NumericTargetOutcome := do
  let checked ← collectRows? rows
  let table ← (certifyParallelNumericAlternativeTable checked).toOption
  (table.evaluate inputContext).toOption

private def executionTable? :
    Option (CheckedParallelNumericAlternativeTable model) := do
  let first ← row? (.fieldFilled 7) input
  let second ← row? (.fieldFilled 4) plusOne
  (certifyParallelNumericAlternativeTable [first, second]).toOption

private def outcomes? (cells : List ClassifiedCellInput) :
    Option (List ParallelNumericDirectOutcome) := do
  let table ← executionTable?
  let preliminary ← preliminaryFor cells
  (table.execute preliminary).toOption

private def result? (cells : List ClassifiedCellInput) :
    Option
      (NumericComputationRunView (ComputationFormalMessage Bool) CellAddr) := do
  let table ← executionTable?
  let preliminary ← preliminaryFor cells
  (table.executeResult preliminary (fun _ => true) []).toOption

/- Construction requires a genuine table and rejects an unguarded or differently targeted row. -/
example :
    tableError? [row? (.fieldFilled 4) input] =
        some .fewerThanTwo ∧
      tableError? [
        (checkIsolatedParallelNumericExpressionRunWithGuard
          model ["Plan"] 2 inputPath input none).toOption,
        row? (.fieldNotFilled 4) plusOne] =
        some (.unguarded 1) ∧
      (do
        let first ← secondModelRow? 2 input (.fieldFilled 4)
        let other ← secondModelRow? 9 input (.fieldFilled 4)
        match certifyParallelNumericAlternativeTable [first, other] with
        | .error error => some error
        | .ok _ => none) =
        some (.targetMismatch 2 2 9) := by
  native_decide

/- A false guard crosses the row boundary; a selected value ends the scan. -/
example :
    tableOutcome? [
      row? (.fieldFilled 4) input,
      row? (.fieldNotFilled 4) plusOne] =
        some (.accepted { unscaled := 1, scale := 0 }) ∧
      tableOutcome? [
        row? (.fieldFilled 4) input,
        row? (.fieldNotFilled 4) plusOne]
        (context (checkedNumber (.parsed (.num 10)))) =
        some (.accepted { unscaled := 10, scale := 0 }) := by
  native_decide

/- A reached guard poison and a selected arithmetic domain failure both stop before the later row. -/
example :
    tableOutcome? [
      row? (.fieldFilled 4) input,
      row? (.fieldNotFilled 4) plusOne]
        (context ((checkedNumber .empty).withFinding .malformed)) =
        some (.inheritedPoison .malformed) ∧
      tableOutcome? [
        row? (.fieldFilled 4) divideByZero true,
        row? (.fieldFilled 4) plusOne]
        (context (checkedNumber (.parsed (.num 10)))) =
        some (.invalidNoValue .calculationValue) := by
  native_decide

/- Clean columns evaluate the first selected row independently at each target key. -/
example :
    let firstSelected :=
      cleanCells ++ [{
        address := { field := 7, path := [1] }
        stored := "yes"
        raw := .parsed (.str "yes")
      }]
    (outcomes? firstSelected).map (·.map (·.outcome)) =
      some [
        .accepted { unscaled := 10, scale := 0 },
        .accepted { unscaled := 21, scale := 0 }
      ] := by
  native_decide

/- A group referenced only by the false first row still participates statically: its invalid column suppresses and clears every covered target before the second row can select. -/
example :
    let invalidUnselectedRoute :=
      (cleanCells.filter fun cell =>
        cell.address != { field := 5, path := [2] }) ++ [
          numberCell 2 [1] { unscaled := 7, scale := 0 },
          numberCell 2 [2] { unscaled := 8, scale := 0 }
        ]
    (outcomes? invalidUnselectedRoute).map (·.map (·.outcome)) = some [] ∧
      (result? invalidUnselectedRoute).map (·.cleared) =
        some [
          { field := 2, path := [1] },
          { field := 2, path := [2] }
        ] := by
  native_decide

end A12Kernel.Conformance.ParallelNumericAlternativeTable
