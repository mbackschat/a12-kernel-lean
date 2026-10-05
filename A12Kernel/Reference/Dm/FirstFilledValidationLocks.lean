import A12Kernel.Reference.Dm.Replay
import A12Kernel.Reference.Dm.LowerDocument

namespace A12Kernel.Dm.FirstFilledValidationLocks

open Lean A12Kernel A12Kernel.Dm

private def run (prototype : FlatFieldDecl) (condition : String)
    (first second : Option String) (fallback : Option String := none)
    (rows : List (Option String × Option String) := []) (bound : Bool := false) : Option Verdict := do
  let model : FlatModel := {
    timeZoneId := "Europe/Berlin"
    fields := [
      { id := 1, groupPath := ["Form"], name := "Error", policy := { kind := .string } },
      { prototype with id := 2, groupPath := ["Form", "Values"], name := "A" },
      { prototype with id := 3, groupPath := ["Form", "Values"], name := "B" },
      { prototype with id := 4, groupPath := ["Form"], name := "Fallback" },
      { prototype with id := 5, groupPath := ["Form", "Rows"], name := "A", repeatableScope := [10] },
      { prototype with id := 6, groupPath := ["Form", "Rows"], name := "B", repeatableScope := [10] }]
    repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 2 }] }
  let dm : DmModel := {
    flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let pair := fun (a b : Option String) => Json.mkObj (
    a.toList.map (fun value => ("A", Json.str value)) ++
    b.toList.map (fun value => ("B", Json.str value)))
  let input ← (readDocument dm (Json.mkObj [("Form", Json.mkObj (
    [("Error", Json.str "ready"), ("Values", pair first second),
      ("Rows", Json.arr (rows.map (fun (a, b) => pair a b)).toArray)] ++
    fallback.toList.map (fun value => ("Fallback", Json.str value))))])).toOption
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let document ← (checkDocument prepared "en_US" input.data).toOption
  let rule ← (checkRule dm .english {
    group := if bound then ["Form", "Rows"] else ["Form"], name := "Selected", errorCode := "SELECTED",
    errorEntityRelPath := if bound then "../B" else "../Error",
    condition := (if bound then "FieldFilled(B) And (" else "FieldFilled(Error) And (") ++ condition ++ ")", severity := "ERROR" }).toOption
  let context : AddressedValidationEvaluationContext model := {
    scalar := { fields := document.flatContext.withWorld world, groups := GroupPresenceContext.unavailable }
    outer := [], input := .checked document }
  match rule.ordinaryIterationPlan with
  | .scalar => pure (← (rule.evalAddressedFull context true).toOption).verdict
  | .once _ => pure (← (rule.evalOrdinaryOnceFull document (some world)).toOption).2.verdict
  | .rows _ => pure (← (← (rule.evalOrdinaryRepeatableFull document (some world)).toOption).head?).2.verdict

private def number : FlatFieldDecl := {
  id := 0, groupPath := ["Form"], name := "N", policy := { kind := .number { scale := 0, signed := true } } }

private def text : FlatFieldDecl := {
  id := 0, groupPath := ["Form"], name := "T", policy := { kind := .string } }

example : run number "FirstFilledValue(Values) == 7" (some "7") (some "bad") =
      some (.fired .value) ∧
    run number "FirstFilledValue(Values, Fallback) == 9" none none (some "9") =
      some (.fired .omission) ∧
    run number "FirstFilledValue(Values) == 0" (some "bad") none = some .unknown := by native_decide

example : run text "FirstFilledValue(Values) == \"first\"" (some "first") (some "later") =
      some (.fired .value) ∧
    run text "FirstFilledValue(Values, Rows*, Fallback) == \"last\"" none none (some "last") =
      some (.fired .omission) := by native_decide

example : run text "FirstFilledValue(Rows*) == \"selected\"" none none none
      [(none, some "selected"), (some "later", none)] = some .notFired ∧
    run number "FirstFilledValue(Rows*) == 3" none none none
      [(none, some "3"), (some "2", none)] = some .notFired := by native_decide

example : run text "FirstFilledValue(A, B) == \"selected\"" none none none
      [(none, some "selected")] true = some (.fired .omission) ∧
    run text "FirstFilledValue(A, B) == \"selected\"" none none none
      [(some "selected", some "other")] true = some (.fired .value) := by native_decide

end A12Kernel.Dm.FirstFilledValidationLocks
