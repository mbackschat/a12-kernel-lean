import A12Kernel.Reference.Dm.Validate
import A12Kernel.Reference.Dm.Document

/-! # Declaring paths and error-field iteration binding

The peer cart rule calibrates a root-declared coordinate read at a row error field. Distinct
same-named fields make replacing lexical scope with the target group observably wrong.
-/
namespace A12Kernel.Dm.ValidationBindingLocks
open A12Kernel A12Kernel.Dm Lean

private def number (id : FieldId) (group : GroupPath) (name : String)
    (scope : List RepeatableLevel := []) : FlatFieldDecl := {
  id, name, groupPath := group, repeatableScope := scope
  policy := { kind := .number { scale := 0, signed := true } } }
private def model : FlatModel := {
  fields := [number 1 ["Form"] "Qty", number 2 ["Form", "Rows"] "Qty" [10],
    number 4 ["Form", "Side"] "SideQty",
    { id := 3, name := "Key", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .string } }]
  repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 3 }] }
private def dm : DmModel := {
  flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
private def rule (text : String) : DmRule := {
  group := ["Form"], name := "Rule", errorCode := "R", errorEntityRelPath := "../Rows/Qty"
  condition := text, severity := "ERROR" }
private def row (qty key : String) : Json := Json.mkObj [("Qty", Json.str qty), ("Key", Json.str key)]
private def run (text : String) (rows : List Json) : Option (List String) := do
  let checkedRule ← (checkRule dm .english (rule text)).toOption
  let input ← (readDocument dm (Json.mkObj [("Form", Json.mkObj [
    ("Qty", "9"), ("Rows", Json.arr rows.toArray)])])).toOption
  if !input.refusals.isEmpty then none
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let document ← (checkDocument prepared "en_US" input.data).toOption
  pure ((← (runRule world document checkedRule).toOption).map fun message => (observe model message).pointer)

example : run "FieldFilled(Rows/Qty) And CurrentRepetition(Rows) > 1"
    [row "5" "A", row "5" "B"] = some ["Form/Rows[2]/Qty"] ∧
    run "FieldFilled(Rows/Qty) And CurrentRepetition(Rows) > 1" [row "5" "A"] = some [] := by native_decide

example : run "FieldFilled(Rows/Qty) And [Qty] + [Rows/Qty] > 10"
    [row "2" "A", row "1" "B"] = some ["Form/Rows/Qty"] := by native_decide

example : run "FieldFilled(Rows/Qty) And CurrentRepetition(Rows) > 1 And [Qty] + 1 > 0"
    [row "5" "A", row "5" "B"] = some ["Form/Rows[2]/Qty"] := by native_decide

example : run "AllFieldsFilled(Rows/Qty, Rows/Key)"
    [row "2" "A", row "1" ""] = some ["Form/Rows/Qty"] ∧
    run "AllFieldsFilled(Rows/Qty, Rows/Key)" [row "2" "", row "1" "B"] =
      some ["Form/Rows[2]/Qty"] ∧
    run "AllFieldsFilled(Rows/Qty, Rows/Key)" [] = some [] := by native_decide

example : (do
    let checked ← (checkRule dm .english
      (rule "FieldFilled(Rows/Qty) And CurrentRepetition(Rows) > 1")).toOption
    pure (checked.condition.declaringGroup, checked.condition.rowGroup, checked.iterationScope)) =
    some (["Form"], ["Form", "Rows"], some [10]) := by native_decide

example : (do
    let root ← (checkRule dm .english (rule "AllFieldsFilled(Rows/Qty, Rows/Key)")).toOption
    let localRule ← (checkRule dm .english { (rule "AllFieldsFilled(Qty, Key)") with
      group := ["Form", "Rows"]
      errorEntityRelPath := "../Qty" }).toOption
    match root.condition.and localRule.condition with
    | .error (.declaringGroupMismatch left right) => some (left, right)
    | _ => none) = some (["Form"], ["Form", "Rows"]) := by native_decide

example :
    (checkRule dm .english
      (rule "FieldFilled(/Form/Rows/Qty) And CurrentRepetition(/Form/Rows) > 1")).isOk = true ∧
    (checkRule dm .english {
      (rule "FieldFilled(/Form/Rows/Qty) And CurrentRepetition(/Form/Rows) > 1") with
      group := ["Form", "Side"]
      errorEntityRelPath := "../../Rows/Qty" }).isOk = false := by native_decide

end A12Kernel.Dm.ValidationBindingLocks
