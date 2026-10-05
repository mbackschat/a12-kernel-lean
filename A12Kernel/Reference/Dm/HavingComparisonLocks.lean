import A12Kernel.Reference.Dm.Replay
import A12Kernel.Reference.Dm.LowerDocument
import A12Kernel.Reference.Dm.Compute

namespace A12Kernel.Dm.HavingComparisonLocks
open Lean A12Kernel

private def model : FlatModel := {
  fields := [
    { id := 1, groupPath := ["Form"], name := "Error", policy := { kind := .string } },
    { id := 2, groupPath := ["Form"], name := "Expected", policy := { kind := .string } },
    { id := 3, groupPath := ["Form", "Rows"], name := "Tag", policy := { kind := .string }, repeatableScope := [10] },
    { id := 4, groupPath := ["Form", "Rows"], name := "N", policy := { kind := .number { scale := 0, signed := true } }, repeatableScope := [10] },
    { id := 5, groupPath := ["Form"], name := "Out", policy := { kind := .number { scale := 0, signed := true } } }]
  repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 3 }] }

private def run (filter : String) (fresh : Bool := false)
    (kind : FieldKind := .string) (expected : String := "keep")
    (first : String := "keep") (second : String := "drop")
    (enumeration : Option EnumerationDeclaration := none) : Option (Verdict × List String) := do
  let model := { model with fields := model.fields.map fun field =>
    if field.id == 2 || field.id == 3 then { field with policy := { kind }, enumeration } else field }
  let dm : DmModel := {
    flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let row := fun (tag n : String) => Json.mkObj [("Tag", Json.str tag), ("N", Json.str n)]
  let input ← (readDocument dm (Json.mkObj [("Form", Json.mkObj [
    ("Error", Json.str "ready"), ("Expected", Json.str expected),
    ("Rows", Json.arr #[row first "2", row second "5", row first "7"])])])).toOption
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let document ← (checkDocument prepared "en_US" input.data).toOption
  let operation := "Sum(Rows*/N Having " ++ filter ++ ")"
  let rule ← (checkRule dm .english {
    group := ["Form"], name := "Selected", errorCode := "SELECTED", errorEntityRelPath := "../Error",
    condition := "FieldFilled(Error) And " ++ operation ++ " == 9", severity := "ERROR" }).toOption
  let context : AddressedValidationEvaluationContext model := {
    scalar := { fields := document.flatContext.withWorld world, groups := GroupPresenceContext.unavailable }
    outer := [], input := .checked document }
  let verdict := (← (rule.evalAddressedFull context true).toOption).verdict
  let (_, computation) ← (lowerComputation model .english {
    group := ["Form"], name := "Total", targetRelPath := "../Out", commonPrecondition := none,
    alternatives := [{ precondition := none, operation }], errorCodesToSuppress := [] }).toOption
  let computations ← if fresh then do
      let (_, producer) ← (lowerComputation model .english {
        group := ["Form"], name := "Expected", targetRelPath := "../Expected", commonPrecondition := none,
        alternatives := [{ precondition := none, operation := "\"drop\"" }], errorCodesToSuppress := [] }).toOption
      pure [computation, producer]
    else pure [computation]
  let outcomes ← (runComputations world prepared document computations).toOption
  pure (verdict, outcomes.map (·.outcome))

example : run "[Rows/Tag] == [$Expected]" = some (.fired .omission, ["value 9"]) ∧
    run "[$Expected] == [Rows/Tag]" = some (.fired .omission, ["value 9"]) ∧
    run "[Rows/Tag] != [$Expected]" = some (.notFired, ["value 5"]) := by native_decide

example : (run "[Rows/Tag] == [$Expected]" true).map (·.2) = some ["value drop", "value 5"] := by native_decide

example : run "[Rows/Tag] == [$Expected]" false .boolean "false" "false" "true" =
      some (.fired .omission, ["value 9"]) ∧
    run "[Rows/Tag] == False" false .boolean "true" "false" "true" =
      some (.fired .omission, ["value 9"]) ∧
    run "True != [Rows/Tag]" false .confirm "true" "" "true" =
      some (.fired .omission, ["value 9"]) := by native_decide

private def domain : EnumerationDeclaration := {
  storedTokens := ["keep", "drop"], categories := [{ name := "Swap", tokens := ["drop", "keep"] }] }

example : run "[Rows/Tag] == [$Expected]" false .enumeration "keep" "keep" "drop" (some domain) =
      some (.fired .omission, ["value 9"]) ∧
    run "[Rows/Tag -> Swap] == [$Expected]" false .enumeration "keep" "keep" "drop" (some domain) =
      some (.notFired, ["value 5"]) ∧
    run "[Rows/Tag -> Swap] == [$Expected -> Swap]" false .enumeration "keep" "keep" "drop" (some domain) =
      some (.fired .omission, ["value 9"]) := by native_decide


example : run "[Rows/Tag] == False" false .confirm "true" "true" "" = none ∧
    run "[Rows/Tag] == [$Expected]" false .confirm "true" "true" "" = none ∧
    run "[Rows/Tag] != [$Expected]" false .confirm "true" "" "true" =
      some (.fired .omission, ["value 9"]) ∧
    run "[Rows/Tag] == False" false .boolean "false" "bad" "false" =
      some (.notFired, []) := by native_decide

private def references : Option (Bool × Bool) := do
  let parsed ← (parseText .english
    "FieldValuesNotUnique(/Form/Rows*/Tag Having [/Form/Rows/Tag] == [$/Form/Rows/Tag])").toOption
  let checked ← (lowerCondition model ["Form", "Rows"] false parsed.body).toOption
  let pointers ← (checked.core.referencePointers [(10, 2)]).toOption
  pure (pointers.contains { field := 3, coordinates := [.wildcard] },
    pointers.contains { field := 3, coordinates := [.concrete 2] })

example : references = some (true, true) := by native_decide

end A12Kernel.Dm.HavingComparisonLocks
