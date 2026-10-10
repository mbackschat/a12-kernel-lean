import A12Kernel.Reference.Dm.Validate
import A12Kernel.Reference.Dm.Document

namespace A12Kernel.Dm.FirstFilledPrefixLocks
open Lean A12Kernel

private def model : FlatModel := {
  fields := [
    { id := 1, name := "Anchor", groupPath := ["Form"], policy := { kind := .string } },
    { id := 2, name := "Text", groupPath := ["Form", "Parents", "Rows"], repeatableScope := [10, 20], policy := { kind := .string } },
    { id := 3, name := "Keep", groupPath := ["Form", "Parents", "Rows"], repeatableScope := [10, 20], policy := { kind := .number { scale := 0, signed := true } } },
    { id := 4, name := "Flag", groupPath := ["Form", "Parents", "Rows"], repeatableScope := [10, 20], policy := { kind := .boolean } }]
  repeatableGroups := [
    { level := 10, path := ["Form", "Parents"], repeatability := some 3 },
    { level := 20, path := ["Form", "Parents", "Rows"], repeatability := some 3 }] }

private def cell (text number flag : String) : Json :=
  Json.mkObj [("Text", .str text), ("Keep", .str number), ("Flag", .str flag)]
private def a := cell "A" "1" "true"
private def b := cell "B" "2" "false"
private def parent (rows : List Json) := Json.mkObj [("Rows", .arr rows.toArray)]

private def run (parents : List Json) : Option (List (String × String × String)) := do
  let dm : DmModel := { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let input ← (readDocument dm (Json.mkObj [("Form", Json.mkObj [
    ("Anchor", .str "ON"), ("Parents", .arr parents.toArray)])])).toOption
  if !input.refusals.isEmpty then none
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let document ← (checkDocument prepared "en_US" input.data).toOption
  let profiles := [("BARE", "Text", "\"A\""), ("BOOLEAN", "Flag", "True"),
    ("FILTERED", "Text Having [/Form/Parents/Rows/Keep] > 0", "\"A\""), ("NUMBER", "Keep", "1")]
  let messages ← profiles.mapM fun (code, source, value) => do
    let rule ← (checkRule dm .english {
      name := code, group := ["Form"], errorCode := code, errorEntityRelPath := "../Anchor", severity := "ERROR",
      condition := "FieldFilled(Anchor) And FirstFilledValue(/Form/Parents*/Rows*/" ++ source ++ ") == " ++ value }).toOption
    pure ((← (runRule world document rule).toOption).map fun message =>
      let result := observe model message
      (code, result.pointer, result.messageType))
  pure messages.flatten

private def expected (unfiltered : String) : List (String × String × String) :=
  [("BARE", "Form/Anchor", unfiltered), ("BOOLEAN", "Form/Anchor", unfiltered),
   ("FILTERED", "Form/Anchor", "OMISSION_ERROR"), ("NUMBER", "Form/Anchor", unfiltered)]

example : run [parent [], parent [a]] = some (expected "OMISSION_ERROR") := by native_decide
example : run [Json.mkObj [], parent [a]] = some (expected "OMISSION_ERROR") := by native_decide
example : run [parent [a], parent []] = some (expected "VALUE_ERROR") := by native_decide
example : run [parent [a], Json.mkObj []] = some (expected "VALUE_ERROR") := by native_decide
example : run [parent [a], parent [b]] = some (expected "VALUE_ERROR") := by native_decide
example : run [parent [Json.mkObj []], parent [a]] = some (expected "OMISSION_ERROR") := by native_decide
example : run [parent [a, Json.mkObj []], parent [b]] = some (expected "VALUE_ERROR") := by native_decide
example : run [parent [], parent []] = some [] := by native_decide
example : run [] = some [] := by native_decide
example : run [parent [b], parent [a]] = some [] := by native_decide
example : run [parent [cell "B" "bad" "bad"], parent [a]] =
    some [("FILTERED", "Form/Anchor", "OMISSION_ERROR")] := by native_decide

end A12Kernel.Dm.FirstFilledPrefixLocks
