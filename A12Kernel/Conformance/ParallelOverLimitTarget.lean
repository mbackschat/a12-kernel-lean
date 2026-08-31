import A12Kernel.Conformance.ParallelComputationClearingPlan
import A12Kernel.Elaboration.ParallelNumericDirectRun

/-! # An over-limit row on the indexed-parallel carrier

The parallel carrier was the one repeatable-target carrier left outside the over-limit clearing
correction, on the reading that a row beyond capacity carries no index entry and so might be
outside the route's execution domain rather than capacity-excluded. Those two accounts move
together on every document whose excess row has no resolvable partner, which is why the exclusion
stood unmeasured.

The a12-dmkits round at `SPEC-2026-08-31-08` separates them by giving the excess row a **resolvable**
join: an execution-domain reading predicts the row is simply absent, a capacity reading predicts it
appears and is cleared. It appears, cleared, with the value it could have computed not written. The
fixtures here lock that account, and the second one is what makes `cleared` mean anything — an
in-capacity row whose join resolves to nothing computes the kind's empty value instead of clearing,
so a clear reports exclusion rather than an unresolved partner.
-/

namespace A12Kernel.Conformance.ParallelOverLimitTarget

open A12Kernel
open A12Kernel.Conformance.ParallelComputationClearingPlan (model operandPath operandNumericCell)

/-- Target rows 1 and 2 are in capacity and row 3 is beyond the group's declared maximum of two;
the operand group carries two rows so a key can resolve from either. -/
private def rows : List RowAddr := [
  { group := 50, path := [1] },
  { group := 60, path := [1, 1] },
  { group := 60, path := [1, 2] },
  { group := 60, path := [1, 3] },
  { group := 70, path := [1] },
  { group := 70, path := [2] }]

private def indexCell (field : FieldId) (path : List Nat) (stored : String) :
    ClassifiedCellInput :=
  { address := { field, path }, stored, raw := .parsed (.str stored) }

private def targetCell (path : List Nat) (amount : Int) : ClassifiedCellInput :=
  { address := { field := 2, path }
    stored := toString amount
    raw := .parsed (.num amount)
    numericDecimal := some { unscaled := amount, scale := 0 } }

/-- The excess row's key `Gamma` resolves to the second operand row, so an account that skipped the
row for want of a partner and one that excludes it for capacity predict different outcomes. -/
private def resolvableExcess : List ClassifiedCellInput := [
  indexCell 1 [1, 1] "Alpha",
  indexCell 1 [1, 2] "Beta",
  indexCell 1 [1, 3] "Gamma",
  indexCell 3 [1] "Alpha",
  indexCell 3 [2] "Gamma",
  operandNumericCell [1] { unscaled := 10, scale := 0 },
  operandNumericCell [2] { unscaled := 30, scale := 0 },
  targetCell [1, 3] 999]

private def preliminary? (cells : List ClassifiedCellInput) :
    Option (CheckedIndexPreliminary model) := do
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption
  let checked ←
    (checkDocument prepared "en_US" { instantiatedRows := rows, cells }).toOption
  checked.applyFullIndexPreliminary.toOption

private def plan? := (checkParallelNumericComputationClearingPlan
  model ["Plan"] 2 operandPath).toOption

private def direct? := (checkIsolatedParallelNumericDirectRun
  model ["Plan"] 2 operandPath).toOption

private def executed? (cells : List ClassifiedCellInput) : Option (List CellAddr) := do
  let preliminary ← preliminary? cells
  let checked ← direct?
  let outcomes ← (checked.execute preliminary).toOption
  pure (outcomes.map ParallelNumericDirectOutcome.address)

private def cleared? (cells : List ClassifiedCellInput) : Option (List CellAddr) := do
  let preliminary ← preliminary? cells
  let checked ← plan?
  let view ← (checked.clearedSourceTargets preliminary).toOption
  pure view.cleared

/- The excess row produces no value even though its join resolves, and its seeded value is cleared.
   Both halves are needed: without the clear the row is merely skipped, and without the execution
   exclusion the 30 it could compute would be written. -/
example :
    executed? resolvableExcess =
        some [{ field := 2, path := [1, 1] }, { field := 2, path := [1, 2] }] ∧
      cleared? resolvableExcess = some [{ field := 2, path := [1, 3] }] := by
  native_decide

/- The clear is not conditioned on an invalid index anywhere in the document: every index column
   here is clean, so a route that reached clearing only through an invalid mark reports nothing. -/
example :
    (do
      let preliminary ← preliminary? resolvableExcess
      let checked ← plan?
      let marks ← (checked.asTargetRoute.invalidIndexMarks preliminary .target).toOption
      let operandMarks ←
        (checked.asTargetRoute.invalidIndexMarks preliminary .operand).toOption
      pure (marks.isEmpty && operandMarks.isEmpty)) = some true := by
  native_decide

/- An **in-capacity** row whose key matches no operand row computes the kind's empty value rather
   than clearing, so a cleared row reports capacity exclusion and not an unresolved partner. Row 2
   keys `Beta`, which no operand row carries. -/
example :
    (do
      let preliminary ← preliminary? resolvableExcess
      let checked ← direct?
      let outcomes ← (checked.execute preliminary).toOption
      pure (outcomes.filter fun outcome : ParallelNumericDirectOutcome =>
        outcome.address == ({ field := 2, path := [1, 2] } : CellAddr))).map
      (List.map ParallelNumericDirectOutcome.outcome) =
      some [.accepted { unscaled := 0, scale := 0 }] := by
  native_decide

end A12Kernel.Conformance.ParallelOverLimitTarget
