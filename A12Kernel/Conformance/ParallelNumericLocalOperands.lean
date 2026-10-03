import A12Kernel.Conformance.ParallelComputationClearingPlan
import A12Kernel.Elaboration.ParallelNumericAlternativeTable

/-! # Bound and joined operands in one parallel Number expression

The retained staffing computation mixes its own row with a key-matched sibling row. This framed
fixture also distinguishes the target environment from the matched environment and a missing key.
-/

namespace A12Kernel.Conformance.ParallelNumericLocalOperands
open A12Kernel A12Kernel.Conformance.ParallelComputationClearingPlan

private def peerPath : SurfaceFieldPath := {
  base := .absolute, groups := ["Plan", "Frame", "Target"], field := "Peer" }
private def expression : AuthoredNumericExpr SurfaceNumericAtom :=
  .binary .add (.atom (.field operandPath)) (.atom (.field peerPath))
private def operation (guard : Option (CheckedComputationCondition model) := none) :=
  (checkIsolatedParallelNumericExpressionRunWithGuard model ["Plan"] 2
    operandPath expression guard).toOption
private def peerCell (path : List Nat) (value : Int) : ClassifiedCellInput := {
  address := { field := 5, path }, stored := toString value
  raw := .parsed (.num value) }
private def cells : List ClassifiedCellInput := cleanIndexCells ++ [
  operandNumericCell [1] { unscaled := 10, scale := 0 },
  operandNumericCell [2] { unscaled := 20, scale := 0 },
  peerCell [1, 1] 1, peerCell [1, 2] 2, peerCell [2, 1] 3]
private def outcomes (guard : Option (CheckedComputationCondition model) := none)
    (input : List ClassifiedCellInput := cells) : Option (List NumericTargetOutcome) := do
  let checked ← operation guard
  let preliminary ← preliminaryFor input
  pure ((← checked.execute preliminary |>.toOption).map (·.outcome))

example : outcomes = some [.accepted { unscaled := 11, scale := 0 },
    .accepted { unscaled := 3, scale := 0 }, .accepted { unscaled := 22, scale := 0 }] := by native_decide

example : outcomes (some (.fieldFilled 5)) = outcomes ∧
    outcomes (some (.fieldNotFilled 5)) = some [.noValue, .noValue, .noValue] := by native_decide

example : (do
    let first ← operation (some (.fieldNotFilled 5))
    let second ← operation (some (.fieldFilled 5))
    let table ← (certifyParallelNumericAlternativeTable [first, second]).toOption
    let preliminary ← preliminaryFor cells
    pure ((← table.execute preliminary |>.toOption).map (·.outcome))) =
    some [.accepted { unscaled := 11, scale := 0 }, .accepted { unscaled := 3, scale := 0 },
      .accepted { unscaled := 22, scale := 0 }] := by native_decide

example : (checkIsolatedParallelNumericExpressionRunWithGuard model ["Plan"] 2 operandPath
    (.binary .add (.atom (.field operandPath))
      (.atom (.field { peerPath with field := "Result" }))) none).isOk = false := by native_decide

example : (match checkIsolatedParallelNumericExpressionRunWithGuard model ["Plan"] 2 operandPath
    (.binary .add (.atom (.field operandPath))
      (.atom (.field { base := .absolute, groups := ["Plan"], field := "Operand" }))) none with
    | .error (.expressionResolve (.groupInFieldValueRead _ _ _)) => true
    | _ => false) = true := by native_decide

private def enclosingModel : FlatModel := { model with fields := model.fields ++ [
  { id := 7, name := "Outer", groupPath := ["Plan", "Frame"], repeatableScope := [50]
    policy := { kind := .number { scale := 0, signed := false } } }] }

private def enclosingOutcomes : Option (List NumericTargetOutcome) := do
  let checked ← (checkIsolatedParallelNumericExpressionRunWithGuard enclosingModel ["Plan"] 2 operandPath
    (.binary .add (.atom (.field operandPath))
      (.atom (.field { base := .absolute, groups := ["Plan", "Frame"], field := "Outer" }))) none).toOption
  let source ← preliminaryFor cells
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler enclosingModel).toOption
  let document ← (checkDocument prepared "en_US" {
    instantiatedRows := source.base.source.instantiatedRows
    cells := cells ++ [
      { address := { field := 7, path := [1] }, stored := "5", raw := .parsed (.num 5) },
      { address := { field := 7, path := [2] }, stored := "9", raw := .parsed (.num 9) }] }).toOption
  let preliminary ← document.applyFullIndexPreliminary.toOption
  pure ((← checked.execute preliminary |>.toOption).map (·.outcome))

example : enclosingOutcomes = some [.accepted { unscaled := 15, scale := 0 },
    .accepted { unscaled := 9, scale := 0 }, .accepted { unscaled := 25, scale := 0 }] := by native_decide

end A12Kernel.Conformance.ParallelNumericLocalOperands
