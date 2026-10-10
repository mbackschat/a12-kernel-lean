import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Document

namespace A12Kernel.Dm.SelectedGroupGuardLocks

private structure Scenario where
  key : String := "P1"
  payload : String := ""
  source : String := "7"
  duplicate : Bool := false
  gate : String := "1"
  keyProducer : Bool := false
  payloadProducer : Bool := false
  rows : Bool := true

private def model : FlatModel := {
  fields := [
    { id := 1, name := "Code", groupPath := ["Form", "Packages"], repeatableScope := [10], policy.kind := .string },
    { id := 2, name := "Value", groupPath := ["Form", "Packages", "Items", "Box"], repeatableScope := [10,20], policy.kind := .number { scale := 0, signed := true } },
    { id := 3, name := "Source", groupPath := ["Form", "Packages", "Items"], repeatableScope := [10,20], policy.kind := .number { scale := 0, signed := true } },
    { id := 4, name := "Key", groupPath := ["Form"], policy.kind := .string },
    { id := 5, name := "Gate", groupPath := ["Form"], policy.kind := .number { scale := 0, signed := true } },
    { id := 6, name := "Out", groupPath := ["Form"], policy.kind := .number { scale := 0, signed := true } },
    { id := 7, name := "After", groupPath := ["Form"], policy.kind := .number { scale := 0, signed := true } }]
  repeatableGroups := [
    { level := 10, path := ["Form", "Packages"], repeatability := some 2, indexField := some 1 },
    { level := 20, path := ["Form", "Packages", "Items"], repeatability := some 2 }] }

private def run (guard : String) (scenario : Scenario := {}) : Option (String × String) := do
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let package (code value : String) := Lean.Json.mkObj [
    ("Code", .str code), ("Items", .arr (if scenario.rows then #[.mkObj [
      ("Source", .str scenario.source), ("Box", .mkObj [("Value", .str value)])]] else #[]))]
  let data := Lean.Json.mkObj [("Form", .mkObj [
    ("Key", .str scenario.key), ("Gate", .str scenario.gate),
    ("Out", .str "99"), ("After", .str "99"),
    ("Packages", .arr #[package "P1" scenario.payload,
      package (if scenario.duplicate then "P1" else "P2") "3"])])]
  let dm : DmModel := { flat := model, computations := [], rules := [], conditionLanguage := "en_US", refusals := [] }
  let input ← (readDocument dm data).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  let computation (name target operation : String) (condition : Option String := none) : DmComputation := {
    name, group := ["Form"], targetRelPath := "../" ++ target, commonPrecondition := condition,
    alternatives := [{ precondition := none, operation }], errorCodesToSuppress := [] }
  let declarations := [
    computation "After" "After" "1" (some "FieldFilled(Out) Or FieldNotFilled(Out)"),
    computation "Consumer" "Out" "1" (some guard)] ++
    (if scenario.keyProducer then [computation "KeyProducer" "Key" "\"P1\""] else []) ++
    (if scenario.payloadProducer then [computation "PayloadProducer" "Packages/Items/Box/Value" "[Packages/Items/Source]"] else [])
  let lowered ← declarations.mapM fun declaration => (lowerComputation model .english declaration).toOption
  let results ← (runComputations world prepared checked (lowered.map (·.2))).toOption
  let outcome (suffix : String) := ((results.filter (·.pointer.endsWith suffix)).head?).map (·.outcome)
  pure (← outcome "/Out", ← outcome "/After")

private def selected := "Packages/Items*/Box For Key"
private def positive := "AtLeastOneGroupFilled(" ++ selected ++ ")"
private def negative := "NoGroupFilled(" ++ selected ++ ")"

example : run positive { payload := "2" } = some ("value 1", "value 1") ∧
    run positive = some ("cleared", "value 1") ∧
    run negative = some ("value 1", "value 1") ∧
    run negative { payload := "2" } = some ("cleared", "value 1") := by native_decide

example : run positive { key := "missing", payload := "2", keyProducer := true } = some ("value 1", "value 1") ∧
    run positive { payloadProducer := true } = some ("value 1", "value 1") ∧
    run positive { key := "missing", keyProducer := true, payloadProducer := true } = some ("value 1", "value 1") := by native_decide

example : run positive { key := "missing" } = some ("cleared", "value 1") ∧
    run negative { key := "missing" } = some ("value 1", "value 1") ∧
    run positive { duplicate := true } = some ("cleared", "cleared") ∧
    run negative { duplicate := true } = some ("cleared", "cleared") := by native_decide

example : run positive { payload := "bad" } = some ("value 1", "value 1") ∧
    run positive { payload := "bad", source := "bad", payloadProducer := true } = some ("cleared", "value 1") ∧
    run negative { payload := "bad", source := "bad", payloadProducer := true } = some ("value 1", "value 1") := by native_decide

example : run ("AtLeastOneGroupFilled(Gate," ++ selected ++ ")") { duplicate := true } = some ("value 1", "value 1") ∧
    run ("AtLeastOneGroupFilled(" ++ selected ++ ",Gate)") { duplicate := true } = some ("cleared", "cleared") ∧
    run ("NoGroupFilled(Gate," ++ selected ++ ")") { duplicate := true } = some ("cleared", "value 1") ∧
    run ("NoGroupFilled(" ++ selected ++ ",Gate)") { duplicate := true } = some ("cleared", "cleared") := by native_decide

example : run positive { key := "P2" } = some ("value 1", "value 1") ∧
    run positive { rows := false, payloadProducer := true } = some ("cleared", "value 1") ∧
    run negative { rows := false, payloadProducer := true } = some ("value 1", "value 1") ∧
    run negative { key := "missing", keyProducer := true, payloadProducer := true } = some ("cleared", "value 1") := by native_decide

example : run ("AtLeastOneGroupFilled(Gate," ++ selected ++ ")") { payload := "2", gate := "bad" } = some ("cleared", "cleared") ∧
    run ("AtLeastOneGroupFilled(" ++ selected ++ ",Gate)") { payload := "2", gate := "bad" } = some ("value 1", "value 1") ∧
    run ("NoGroupFilled(Gate," ++ selected ++ ")") { payload := "2", gate := "bad" } = some ("cleared", "cleared") ∧
    run ("NoGroupFilled(" ++ selected ++ ",Gate)") { payload := "2", gate := "bad" } = some ("cleared", "value 1") := by native_decide

end A12Kernel.Dm.SelectedGroupGuardLocks
