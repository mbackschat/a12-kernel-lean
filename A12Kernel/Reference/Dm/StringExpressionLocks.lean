import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Document
import A12Kernel.Reference.Dm.Validate

namespace A12Kernel.Dm.StringExpressionLocks

private def model : FlatModel := {
  fields := [
    { id := 0, groupPath := ["Form"], name := "S", policy := { kind := .string } },
    { id := 1, groupPath := ["Form"], name := "T", policy := { kind := .string } },
    { id := 2, groupPath := ["Form"], name := "N", policy := { kind := .number { scale := 2, signed := true } } } ] }

private def admitted (source : String) : Bool :=
  match parseText .english source with
  | .ok parsed => (lowerCondition model ["Form"] false parsed.body).isOk
  | .error _ => false

example : ["[S] + \"x\" == [T]", "RangeAsString(S,1,2) != \"x\"",
    "FieldValueAsString(N) + [S] == [T]"].all admitted := by native_decide

private def checkedStored (text : String) : Option CheckedCell := do
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption
  let checked ← (checkDocument prepared "en" { instantiatedRows := [], cells := [
    { address := { field := 0, path := [] }, stored := text, raw := .parsed (.str text) }] }).toOption
  (← (checked.read { field := 0, path := [] }).toOption)

example : (checkedStored "😀b").map (·.findings) = some [.unsupportedCharacter] := by native_decide
example : (checkedStored "𝄞x").map (·.findings) = some [.unsupportedCharacter] := by native_decide

open Lean

private def execute (operation : String) (s n : String) (repeated : Bool := false)
    (condition : Option String := none) : Option (List String) := do
  let group := if repeated then ["Form", "Rows"] else ["Form"]
  let scope := if repeated then [10] else []
  let model : FlatModel := { model with
    fields := model.fields.map (fun f => { f with groupPath := group, repeatableScope := scope }) ++
      [{ id := 3, groupPath := group, name := "Out", repeatableScope := scope, policy := { kind := .string } }]
    repeatableGroups := if repeated then [{ level := 10, path := group, repeatability := some 2 }] else [] }
  let dm : DmModel := { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let row := Json.mkObj [("S", toJson s), ("T", "x"), ("N", toJson n), ("Out", "old")]
  let input := Json.mkObj [("Form", if repeated then Json.mkObj [("Rows", Json.arr #[row, row])] else row)]
  let data ← (readDocument dm input).toOption
  if !data.refusals.isEmpty then none
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let checked ← (checkDocument prepared "en_US" data.data).toOption
  let computation : DmComputation := {
    group, name := "Compute", targetRelPath := "../Out"
    commonPrecondition := condition, alternatives := [{ precondition := none, operation }], errorCodesToSuppress := [] }
  let (_, step) ← (lowerComputation model .english computation).toOption
  pure ((← (runComputations world prepared checked [step]).toOption).map (·.outcome))

example : [false, true].all (fun repeated =>
    let expected value := some (List.replicate (if repeated then 2 else 1) value)
    execute "[S] + FieldValueAsString(N)" "ab" "01.50" repeated == expected "value ab1.5" &&
    execute "RangeAsString(S,1,6) + \"x\"" "ab" "1.50" repeated == expected "value x" &&
    execute "[S] + \"x\"" "" "1.50" repeated == expected "value x" &&
    execute "[S] + \"x\"" "😀b" "1.50" repeated == expected "cleared" &&
    execute "\"😀b\"" "ab" "1.50" repeated == expected "value 😀b" &&
    execute "\"yes\"" "ab" "1.50" repeated (some "[S] + \"x\" == \"abx\"") == expected "value yes" &&
    execute "\"yes\"" "ab" "1.50" repeated (some "[S] + \"x\" != \"\"") == expected "cleared") := by native_decide

private def messages (condition : String) (repeated : Bool := false) : Option Nat := do
  let group := if repeated then ["Form", "Rows"] else ["Form"]
  let model : FlatModel := { model with
    fields := model.fields.map fun f => { f with groupPath := group, repeatableScope := if repeated then [10] else [] }
    repeatableGroups := if repeated then [{ level := 10, path := group, repeatability := some 2 }] else [] }
  let dm : DmModel := { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let row := Json.mkObj [("S", "ab"), ("T", "x"), ("N", "1.50")]
  let input ← (readDocument dm (Json.mkObj [("Form", if repeated then Json.mkObj [("Rows", Json.arr #[row, row])] else row)])).toOption
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  let rule ← (checkRule dm .english {
    group, name := "Rule", errorEntityRelPath := "../S",
    errorCode := "STR", condition, severity := "ERROR" }).toOption
  pure (← (runRule world checked rule).toOption).length

example : messages "RangeAsString(S,1,2) + FieldValueAsString(N) == \"ab1.5\"" true = none := by native_decide
example : messages "[S] + \"x\" != \"\"" true = none := by native_decide

example : messages "RangeAsString(S,1,2) + FieldValueAsString(N) == \"ab1.5\"" = some 1 := by native_decide
example : messages "[S] + \"x\" != \"\"" = some 0 := by native_decide

end A12Kernel.Dm.StringExpressionLocks
