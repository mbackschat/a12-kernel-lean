import A12Kernel.Reference.Dm.Validate
import A12Kernel.Reference.Dm.Document

namespace A12Kernel.Dm.PartialValueListExtentLocks
open Lean A12Kernel

private def model (number : Bool) (capacity : Nat) : FlatModel :=
  let field (id : Nat) (name : String) (groupPath : GroupPath) (repeatableScope : List Nat) : FlatFieldDecl :=
    { id, name, groupPath, repeatableScope,
      policy := { kind := if number then .number { scale := 0, signed := true } else .string } }
  { fields := [{ field 1 "Anchor" ["Form"] [] with policy := { kind := .string } },
      field 2 "Needle" ["Form"] [], field 3 "Value" ["Form", "Rows"] [10]]
    repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some capacity }] }

private def run (number group : Bool) (capacity : Nat) (values : List String)
    (covered : List Nat) (wildcard : Bool := false) : Option (List Bool) := do
  let model := model number capacity
  let dm : DmModel := { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let input ← (readDocument dm (Json.mkObj [("Form", Json.mkObj [
    ("Anchor", .str "on"), ("Needle", .str "100"),
    ("Rows", Json.arr (values.map fun value => Json.mkObj [("Value", .str value)]).toArray)])])).toOption
  if !input.refusals.isEmpty then none
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let document ← (checkDocument prepared "en_US" input.data).toOption
  let scope : ValidationRelevanceScope := .partialSet (
    [{ path := ["Form", "Anchor"], indices := [.all, .all] },
     { path := ["Form", "Needle"], indices := [.all, .all] }] ++
    if wildcard then [{ path := ["Form", "Rows"], indices := [.concrete 1, .all] }]
    else covered.map fun row => { path := ["Form", "Rows"], indices := [.concrete 1, .concrete row] })
  let operand := if group then "Rows*" else "Rows*/Value"
  [true, false].flatMapM fun fieldsSide =>
    ["AtLeastOneFieldValueIncludedInValueList", "NoFieldValueIncludedInValueList", "NotAllFieldValuesIncludedInValueList"].mapM fun operator => do
      let pair := if fieldsSide then operand ++ " In Needle" else "Needle In " ++ operand
      let rule ← (checkRule dm .english {
        name := "CHECK", group := ["Form"], errorCode := "CHECK",
        errorEntityRelPath := "../Anchor", severity := "ERROR",
        condition := "FieldFilled(Anchor) And " ++ operator ++ "(" ++ pair ++ ")" }).toOption
      match rule.ordinaryIterationPlan with
      | .once _ =>
          match ← (rule.evalOrdinaryOncePartial document scope (some world)).toOption with
          | .skipped => none
          | .evaluated _ outcome => pure outcome.message?.isSome
      | .scalar =>
          match ← (rule.evalAddressedPartial document scope (some world)).toOption with
          | .skipped => none
          | .evaluated outcome => pure outcome.message?.isSome
      | .rows _ => none

private def allForms (capacity : Nat) (values : List String) (covered : List Nat)
    (expected : List Bool) (wildcard : Bool := false) : Bool :=
  [false, true].all fun number => [false, true].all fun group =>
    run number group capacity values covered wildcard == some expected

example : allForms 2 ["5", ""] [1, 2] [false, true, true, false, true, true] = true := by native_decide
example : allForms 3 ["5", ""] [1, 2] [false, false, true, false, false, false] = true := by native_decide
example : allForms 3 ["5", ""] [] [false, true, true, false, true, true] true = true := by native_decide
example : allForms 2 ["5", ""] [1] [false, false, true, false, false, false] = true := by native_decide
example : allForms 2 ["5"] [1] [false, false, true, false, false, false] = true := by native_decide
example : allForms 2 [] [1] [false, false, false, false, false, false] = true := by native_decide
example : allForms 2 ["5"] [] [false, false, false, false, false, false] = true := by native_decide
example : allForms 2 ["5", "100"] [2] [true, false, false, true, false, false] = true := by native_decide
example : allForms 2 ["5", "100"] [1] [false, false, true, false, false, false] = true := by native_decide
example : allForms 2 ["5", "100"] [1, 2] [true, false, true, true, false, false] = true := by native_decide
example : allForms 2 [] [1, 2] [false, true, false, false, true, true] = true := by native_decide
example : allForms 3 [] [1, 2] [false, false, false, false, false, false] = true := by native_decide
example : allForms 2 ["5", "", "100"] [1, 2] [false, true, true, false, true, true] = true := by native_decide

end A12Kernel.Dm.PartialValueListExtentLocks
