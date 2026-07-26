import A12Kernel.Conformance.ParallelNumericThreeGroupOperands

/-! # Parallel Number cross-group guard locks

These cases separate a guard group's static participation in parallel index iteration from lazy observation of the guard field itself.
-/

namespace A12Kernel.Conformance.ParallelNumericCrossGroupGuard

open A12Kernel
open A12Kernel.Conformance.ParallelNumericThreeGroupOperands

private def guarded? :=
  (checkIsolatedParallelNumericExpressionRunWithGuard
    model ["Plan"] 2 inputPath (.atom (.field inputPath))
      (some (.or (.fieldFilled 4) (.fieldFilled 7)))).toOption

private def stringCell (path : List Nat) (stored : String)
    (raw : RawCell) : ClassifiedCellInput := {
  address := { field := 7, path }
  stored
  raw
}

private def outcomes? (cells : List ClassifiedCellInput) :
    Option (List ParallelNumericDirectOutcome) := do
  let checked ← guarded?
  let preliminary ← preliminaryFor cells
  (checked.execute preliminary).toOption

private def result? (cells : List ClassifiedCellInput) :
    Option
      (NumericComputationRunView (ComputationFormalMessage Bool) CellAddr) := do
  let checked ← guarded?
  let preliminary ← preliminaryFor cells
  (checked.executeResult preliminary (fun _ => true) []).toOption

/- The raw String leaf contributes one kind-neutral checked route without changing the Number operation payload. -/
example :
    guarded?.map (fun checked =>
      checked.additionalRoutes.map (·.sourceDeclaration.id)) =
      some [7] := by
  native_decide

/- A raw String presence leaf in another indexed group can select the Number operation when the anchor-side leaf is false. -/
example :
    let rightSelected :=
      (cleanCells.filter fun cell =>
        cell.address != { field := 4, path := [1] }) ++ [
          stringCell [1] "yes" (.parsed (.str "yes"))
        ]
    (outcomes? rightSelected).bind (·.head?) =
      some {
        address := { field := 2, path := [1] }
        outcome := .accepted { unscaled := 0, scale := 0 }
      } := by
  native_decide

/- With clean index columns, a holding left `Or` hides a malformed cross-group String guard carrier. -/
example :
    let hiddenMalformed :=
      cleanCells ++ [stringCell [1] "bad" (.rejected .malformed)]
    (outcomes? hiddenMalformed).bind (·.head?) =
      some {
        address := { field := 2, path := [1] }
        outcome := .accepted { unscaled := 10, scale := 0 }
      } := by
  native_decide

/- The same unread guard group still participates statically: its invalid index column suppresses all root-frame outcomes and clears source-filled targets before guard evaluation. -/
example :
    let invalidGuardIndex :=
      (cleanCells.filter fun cell =>
        cell.address != { field := 5, path := [2] }) ++ [
          numberCell 2 [1] { unscaled := 7, scale := 0 },
          numberCell 2 [2] { unscaled := 8, scale := 0 }
        ]
    (outcomes? invalidGuardIndex).map (·.map (·.outcome)) = some [] ∧
      (result? invalidGuardIndex).map (·.cleared) =
        some [
          { field := 2, path := [1] },
          { field := 2, path := [2] }
        ] := by
  native_decide

end A12Kernel.Conformance.ParallelNumericCrossGroupGuard
