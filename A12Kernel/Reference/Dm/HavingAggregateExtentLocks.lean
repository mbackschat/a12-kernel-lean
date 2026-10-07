import A12Kernel.Reference.Dm.HavingFixture

namespace A12Kernel.Dm.HavingAggregateExtentLocks
open Lean A12Kernel

private def model : FlatModel := { HavingFixture.model with
  fields := HavingFixture.model.fields ++ [
    { id := 6, groupPath := ["Form", "Rows", "Pair"], name := "A", repeatableScope := [10],
      policy := { kind := .number { scale := 0, signed := true } } },
    { id := 7, groupPath := ["Form", "Rows", "Pair"], name := "B", repeatableScope := [10],
      policy := { kind := .number { scale := 0, signed := false } } },
    { id := 8, groupPath := ["Form", "Allowed"], name := "Value",
      policy := { kind := .number { scale := 0, signed := true } } },
    { id := 9, groupPath := ["Form", "Choices"], name := "V", repeatableScope := [30],
      policy := { kind := .number { scale := 0, signed := true } } }]
  repeatableGroups := HavingFixture.model.repeatableGroups ++ [
    { level := 30, path := ["Form", "Choices"], repeatability := some 2 }] }
private def row (n a b : String) := Json.mkObj [
  ("N", .str n), ("Tag", .str "x"), ("Pair", Json.mkObj [("A", .str a), ("B", .str b)])]
private def rows := #[row "2" "1" "2", row "5" "4" "5", row "7" "3" "4"]
private def extra := [
  ("Allowed", Json.mkObj [("Value", .str "2")]),
  ("Choices", .arr #[Json.mkObj [("V", .str "2")], Json.mkObj [("V", .str "4")]])]
private def run (filter expected : String) :=
  HavingFixture.runModel model (filter ++ " And FieldFilled(Rows/N)") false "" "unused" "unused"
    (ruleExpected := expected) (extra := extra)
    (rowsOverride := some rows)

example : run "Sum(Rows/Pair) == 3" "2" = some (.fired .omission, ["value 2"]) ∧
    run "Sum(Rows*/Pair) == 19" "14" = some (.fired .omission, ["value 14"]) := by native_decide

private def operators := ["Sum", "MinValue", "MaxValue", "NumberOfDifferentValues"]
private def matrix (operand : String) (amounts selected : List String) : Bool :=
  amounts.length == operators.length && selected.length == operators.length &&
    ((operators.zip amounts).zip selected).all fun ((operator, amount), result) =>
      decide (run (operator ++ "(" ++ operand ++ ") == " ++ amount) result =
        some (.fired .omission, ["value " ++ result]))

example : matrix "Rows/Pair/A, Rows/Pair/B" ["3", "1", "2", "2"] ["2", "2", "2", "14"] = true ∧
    matrix "Rows/Pair" ["3", "1", "2", "2"] ["2", "2", "2", "14"] = true ∧
    matrix "Rows/Pair, Allowed" ["5", "1", "2", "2"] ["2", "2", "2", "2"] = true ∧
    matrix "Allowed" ["2", "2", "2", "1"] ["14", "14", "14", "14"] = true ∧
    matrix "Rows*/Pair" ["19", "1", "5", "5"] ["14", "14", "14", "14"] = true ∧
    matrix "Rows*/Pair/A" ["8", "1", "4", "3"] ["14", "14", "14", "14"] = true ∧
    matrix "Choices*" ["6", "2", "4", "2"] ["14", "14", "14", "14"] = true := by native_decide

private def accepted (filter : String) (fixture : FlatModel := model) : Bool :=
  ((parseText .english ("Sum(Rows*/N Having " ++ filter ++ " And FieldFilled(Rows/N)) > 0")).toOption.bind fun parsed =>
    (lowerCondition fixture ["Form"] false parsed.body).toOption).isSome

example : ["Sum(Rows/Pair/A) == 1", "Sum(Rows/Pair/A, Rows/Pair/A) == 1",
      "Sum(Rows/Pair, Rows/Pair/A) == 1", "Sum(/Form) == 1", "Sum(Rows) == 1",
      "Sum($Rows/Pair) == 1", "Sum(Rows/Pair/A[1], Rows/Pair/B) == 1",
      "Sum(Rows*/Pair Having FieldFilled(Rows/N)) == 1"].all (fun filter => !accepted filter) = true := by
  native_decide

private def scaleModel : FlatModel := { model with fields := model.fields.map fun field =>
  if field.id == 7 then { field with policy := { kind := .number { scale := 2, signed := false } } } else field }
example : ["Sum", "MinValue", "MaxValue"].all (fun operator =>
    accepted (operator ++ "(Rows/Pair) == 1.01") scaleModel) = true ∧
    accepted "NumberOfDifferentValues(Rows/Pair) == 1.01" scaleModel = false := by native_decide

private def categoryModel : FlatModel := { model with fields := model.fields.map fun field =>
  if field.id == 6 then { field with policy := { kind := .enumeration }, enumeration := some {
    storedTokens := ["1"], categories := [{ name := "Label", tokens := ["2"] }] } } else field }
example : accepted "Sum(Rows/Pair/A -> Label, Rows/Pair/B) == 1" categoryModel = false := by native_decide

private def raw (operator operand : String) (input : Array Json) : Option (K × ComputationConditionResult) := do
  let world : World := { now := { epochMillis := 0 } }
  let dm : DmModel := { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let input ← (readDocument dm (Json.mkObj [("Form", Json.mkObj (("Rows", .arr input) :: extra))])).toOption
  if !input.refusals.isEmpty then none
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let document ← (checkDocument prepared "en_US" input.data).toOption
  let parsed ← (parseText .english (operator ++ "(" ++ operand ++ ") == 0 And FieldFilled(Rows/N)")).toOption
  let authored ← (lowerHaving parsed.body).toOption
  let path ← (elaborateStarFieldPath model ["Form"] {
    base := .relative 0, groups := [{ name := "Rows", starred := true }], field := "N" }).toOption
  let checked ← (elaborateStarHavingCore model ["Form"] path authored).toOption
  let .and (.leaf leaf) _ := checked.condition | none
  let context := document.resolvingCorrelationContext
  let frame : CorrelationFrame := { innerEnv := [(10, 1)], outerEnv := [] }
  let truth ← (leaf.evalTruthInResolving context frame).toOption
  pure (truth, ← (leaf.evalComputationInResolving context frame).toOption)

example : operators.all (fun operator => decide (
    raw operator "Rows*/Pair" #[row "2" "bad" ""] = some (.unknown, .poison .malformed) ∧
    raw operator "Rows*/Pair" #[row "2" "" ""] = some (.tru, .holds) ∧
    raw operator "Rows*/Pair" #[row "2" "" "", row "5" "" "", row "7" "" "", row "9" "bad" "bad"] =
      some (.tru, .holds))) = true := by native_decide

private def nestedModel : FlatModel := { model with
  fields := (model.fields.map fun field => if field.id == 5 then
    { field with groupPath := ["Form", "Rows"], repeatableScope := [10] } else field) ++ [{
      id := 11, groupPath := ["Form", "Rows", "Bucket", "Items"], name := "C", repeatableScope := [10, 20],
      policy := { kind := .number { scale := 0, signed := true } } }]
  repeatableGroups := model.repeatableGroups ++ [{
    level := 20, path := ["Form", "Rows", "Bucket", "Items"], repeatability := some 2 }] }
private def nestedFilter (operand : String) := "Sum(" ++ operand ++ ") == 2 And FieldFilled(N)"
private def nestedRun (captured : Bool) (operand : String) : Option (List Bool × List String) := do
  let world : World := { now := { epochMillis := 0 } }
  let dm : DmModel := { flat := nestedModel, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let row (n : String) (values : List String) := Json.mkObj [
    ("N", .str n), ("Tag", .str "x"), ("Out", .str "99"), ("Bucket", Json.mkObj [
      ("Items", .arr ((values.map fun value => Json.mkObj [("C", .str value)]).toArray))])]
  let input ← (readDocument dm (Json.mkObj [("Form", Json.mkObj (
    ("Rows", .arr #[row "2" ["1", "1"], row "5" ["3"], row "7" []]) :: extra))])).toOption
  if !input.refusals.isEmpty then none
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler nestedModel).toOption
  let document ← (checkDocument prepared "en_US" input.data).toOption
  let operation := "Sum(/Form/Rows*/N Having " ++ nestedFilter ((if captured then "$" else "") ++ operand) ++ ")"
  let rule ← (checkRule dm .english {
    group := ["Form", "Rows"], name := "Nested", errorCode := "NESTED", errorEntityRelPath := "../N",
    condition := "FieldFilled(N) And " ++ operation ++ " > 0", severity := "ERROR" } world).toOption
  let verdicts ← (rule.evalOrdinaryRepeatableFull document (some world)).toOption
  let (_, computation) ← (lowerComputation nestedModel .english {
    group := ["Form", "Rows"], name := "Nested", targetRelPath := "../Out", commonPrecondition := none,
    alternatives := [{ precondition := none, operation }], errorCodesToSuppress := [] }).toOption
  let outcomes ← (runComputations world prepared document [computation]).toOption
  pure (verdicts.map (fun result => result.2.verdict.keepsHaving), outcomes.map (·.outcome))

example : ["Bucket", "Bucket/Items*", "Bucket/Items*/C"].all (fun operand => decide (
    nestedRun false operand = some ([true, true, true], ["value 2", "value 2", "value 2"]) ∧
    nestedRun true operand = some ([true, false, false], ["value 14", "value 0", "value 0"]))) = true := by
  native_decide

private def nestedReferences (operand : String) : Option (Option (List RepeatableLevel) × Bool × Bool) := do
  let parsed ← (parseText .english ("FieldValuesNotUnique(/Form/Rows*/Tag Having " ++ nestedFilter operand ++ ")")).toOption
  let checked ← (lowerCondition nestedModel ["Form", "Rows"] false parsed.body).toOption
  let numeric ← (parseText .english ("Sum(/Form/Rows*/N Having " ++ nestedFilter operand ++ ") > 0")).toOption
  let numericChecked ← (lowerCondition nestedModel ["Form", "Rows"] false numeric.body).toOption
  let scope ← numericChecked.core.ordinaryIterationScope.toOption
  let pointers ← (checked.core.referencePointers [(10, 2)]).toOption
  pure (scope, pointers.contains { field := 11, coordinates := [.wildcard, .wildcard] },
    pointers.contains { field := 11, coordinates := [.concrete 2, .wildcard] })

example : ["Bucket", "Bucket/Items*", "Bucket/Items*/C"].all (fun operand => decide (
    nestedReferences operand = some (none, true, false) ∧
    nestedReferences ("$" ++ operand) = some (some [10], false, true))) = true := by native_decide

private def fresh : Option (Verdict × List String) := do
  let world : World := { now := { epochMillis := 0 } }
  let dm : DmModel := { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let input ← (readDocument dm (Json.mkObj [("Form", Json.mkObj (("Error", .str "ready") ::
    ("Rows", .arr rows) :: extra))])).toOption
  if !input.refusals.isEmpty then none
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let document ← (checkDocument prepared "en_US" input.data).toOption
  let operation := "Sum(Rows*/N Having Sum($Allowed) == 2 And FieldFilled(Rows/N))"
  let rule ← (checkRule dm .english {
    group := ["Form"], name := "Fresh", errorCode := "FRESH", errorEntityRelPath := "../Error",
    condition := "FieldFilled(Error) And " ++ operation ++ " == 14", severity := "ERROR" } world).toOption
  let context : AddressedValidationEvaluationContext model := {
    scalar := { fields := document.flatContext.withWorld world, groups := GroupPresenceContext.unavailable }
    outer := [], input := .checked document }
  let verdict := (← (rule.evalAddressedFull context true).toOption).verdict
  let computation (name target operation : String) := lowerComputation model .english {
    group := ["Form"], name, targetRelPath := target, commonPrecondition := none,
    alternatives := [{ precondition := none, operation }], errorCodesToSuppress := [] }
  let (_, consumer) ← (computation "Consumer" "../Out" operation).toOption
  let (_, producer) ← (computation "Producer" "../Allowed/Value" "5").toOption
  let outcomes ← (runComputations world prepared document [consumer, producer]).toOption
  pure (verdict, outcomes.map (·.outcome))

example : fresh = some (.fired .omission, ["value 5", "value 0"]) := by native_decide

end A12Kernel.Dm.HavingAggregateExtentLocks
