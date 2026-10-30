import A12Kernel.Reference.Dm.Validate
import A12Kernel.Reference.Dm.Document

/-! # A scalar rule's condition verdict before the root content gate

Full validation evaluates a scalar-plan rule's condition only where the root has content or the
condition can fire on an empty root (spec/03 §A.4). `scalarConditionVerdict` exposes the verdict the
condition reaches in the context `runRuleAt` evaluates it in, before that gate, so an analysis can
tell a dead condition from a gated one without rebuilding the context. The locks separate the two:
on an empty root `[A] < 3` reads the absent `A` as `0` and fires as an omission, while the rule
itself stays silent there.
-/

namespace A12Kernel.Dm.ScalarVerdictLocks
open Lean

private def model : FlatModel := {
  fields := [{ id := 1, name := "A", groupPath := ["Form"], policy := { kind := .number { scale := 0, signed := true } } }] }

private def dm : DmModel := { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }

private def world : World := { now := { epochMillis := 0 } }

private def rule : DmRule := {
  group := ["Form"], name := "Low", errorEntityRelPath := "../A", errorCode := "LOW", condition := "[A] < 3",
  severity := "ERROR" }

private def checked (cells : List (String × Json)) : Option (CheckedDocument model) := do
  let input ← (readDocument dm (Json.mkObj [("Form", Json.mkObj cells)])).toOption
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  (checkDocument prepared "en_US" input.data).toOption

/-- The pre-gate verdict and the rule's message count on one document. -/
private def observe (cells : List (String × Json)) : Option (Except String (Sum ScalarTemporalEvaluationFault Verdict) × Nat) := do
  let document ← checked cells
  let checkedRule ← (checkRule dm .english rule).toOption
  let messages ← (runRule world document checkedRule).toOption
  pure (scalarConditionVerdict world document checkedRule, messages.length)

private def verdictIs (expected : Verdict) (observed : Option (Except String (Sum ScalarTemporalEvaluationFault Verdict) × Nat))
    (count : Nat) : Bool :=
  match observed with
  | some (.ok (.inr verdict), messages) => verdict == expected && messages == count
  | _ => false

-- The empty root: the condition fires, the closed gate keeps the rule silent. With content the
-- gate opens and the rule fires exactly as its verdict does.
example : verdictIs (.fired .omission) (observe []) 0 = true := by native_decide
example : verdictIs (.fired .value) (observe [("A", "1")]) 1 = true := by native_decide
example : verdictIs .notFired (observe [("A", "5")]) 0 = true := by native_decide

end A12Kernel.Dm.ScalarVerdictLocks
