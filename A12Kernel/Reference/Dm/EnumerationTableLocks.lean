import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Document

namespace A12Kernel.Dm.EnumerationTableLocks

private def run (repeated : Bool) (operation : String) (gate : String := "on") :
    Option (List String × List String) := do
  let group := if repeated then ["Form", "Rows"] else ["Form"]
  let scope := if repeated then [10] else []
  let model : FlatModel := {
    fields := [
      { id := 1, name := "Source", groupPath := group, repeatableScope := scope,
        policy.kind := .enumeration, enumeration := some { storedTokens := ["A", "B"] } },
      { id := 2, name := "Out", groupPath := group, repeatableScope := scope,
        policy.kind := .enumeration, enumeration := some { storedTokens := ["A", "B"] } },
      { id := 3, name := "Gate", groupPath := group, repeatableScope := scope, policy.kind := .string },
      { id := 4, name := "After", groupPath := group, repeatableScope := scope,
        policy.kind := .number { scale := 0, signed := true } }]
    repeatableGroups := if repeated then [{ level := 10, path := group, repeatability := some 2 }] else [] }
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let row := Lean.Json.mkObj [("Source", .str "B"), ("Out", .str "A"),
    ("Gate", .str gate), ("After", .str "99")]
  let data := Lean.Json.mkObj [("Form", if repeated then .mkObj [("Rows", .arr #[row, row])] else row)]
  let dm : DmModel := { flat := model, computations := [], rules := [], conditionLanguage := "en_US", refusals := [] }
  let input ← (readDocument dm data).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  let definitions : List DmComputation := [
    { name := "AfterComp", group, targetRelPath := "../After", commonPrecondition := some "[Out] == \"B\"",
      alternatives := [{ precondition := none, operation := "1" }], errorCodesToSuppress := [] },
    { name := "OutComp", group, targetRelPath := "../Out", commonPrecondition := some "FieldFilled(Gate)",
      alternatives := [{ precondition := none, operation }], errorCodesToSuppress := [] }]
  let lowered ← definitions.mapM fun computation => (lowerComputation model .english computation).toOption
  let results ← (runComputations world prepared checked (lowered.map (·.2))).toOption
  let values (suffix : String) := (results.filter (·.pointer.endsWith suffix)).map (·.outcome)
  pure (values "/Out", values "/After")

example : ["\"B\"", "[Source]"].all (fun operation =>
    run false operation == some (["value B"], ["value 1"]) &&
    run true operation == some (["value B", "value B"], ["value 1", "value 1"])) = true := by native_decide

example : ["\"B\"", "[Source]"].all (fun operation =>
    run false operation "" == some (["cleared"], ["cleared"]) &&
    run true operation "" == some (["cleared", "cleared"], ["cleared", "cleared"])) = true := by native_decide

example : run false "\"C\"" = none ∧ run true "\"C\"" = none := by native_decide

end A12Kernel.Dm.EnumerationTableLocks
