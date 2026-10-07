import A12Kernel.Reference.Dm.HavingFixture

namespace A12Kernel.Dm.HavingFieldFillLocks
open Lean A12Kernel

private def operators := ["AllFieldsFilled", "NoFieldFilled", "AtLeastOneFieldFilled",
  "MoreThanOneFieldFilled", "NotAllFieldsFilled", "NotExactlyOneFieldFilled", "FieldsNotCollectivelyFilled"]
private def model : FlatModel := { HavingFixture.model with fields := HavingFixture.model.fields ++ [
  { id := 6, groupPath := ["Form", "Rows", "Pair"], name := "A", repeatableScope := [10],
    policy := { kind := .number { scale := 0, signed := true } } },
  { id := 7, groupPath := ["Form", "Rows", "Pair"], name := "B", repeatableScope := [10],
    policy := { kind := .number { scale := 0, signed := true } } }] }
private def row (n a b : String) := Json.mkObj [
  ("N", .str n), ("Tag", .str "x"), ("Pair", Json.mkObj [("A", .str a), ("B", .str b)])]
private def rows := #[row "2" "1" "1", row "5" "2" "", row "7" "" ""]
private def run (filter : String) (input : Array Json := rows) : Option (List String) :=
  (HavingFixture.runModel model filter false "" "unused" "unused"
    (rowsOverride := some input)).map (·.2)
private def matrix (operand : String) (expected : List String) (input : Array Json := rows) : Bool :=
  expected.length == operators.length && (operators.zip expected).all fun (operator, value) =>
    decide (HavingFixture.runModel model (operator ++ "(" ++ operand ++ ") And FieldFilled(Rows/N)")
      false "" "unused" "unused" (rowsOverride := some input) (ruleExpected := value) =
      some (.fired .omission, ["value " ++ value]))

example : run "AllFieldsFilled(Rows/Pair/A, Rows/Pair/B)" = some ["value 2"] := by native_decide

example : matrix "Rows/Pair" ["2", "7", "7", "2", "12", "9", "5"] = true := by native_decide

example : ["Rows*", "Rows*/Pair", "Rows*/Pair/A"].all (fun operand =>
    matrix operand ["0", "0", "14", "14", "14", "14", "14"]) = true := by native_decide

example : matrix "Rows*/Pair" ["0", "0", "7", "7", "7", "7", "7"]
      #[row "2" "1" "1", row "5" "2" "2"] = true ∧
    run "AllFieldsFilled(Rows*/Pair) And FieldFilled(Rows/N)"
      #[row "2" "1" "1", row "5" "2" "2", row "7" "3" "3", row "11" "bad" "bad"] =
      some ["value 14"] := by native_decide

private def excludedOuterRow (extra : Bool) :=
  let nested : FlatModel := { HavingFixture.model with
    fields := HavingFixture.model.fields ++ [{
      id := 6, groupPath := ["Form", "Rows", "Items"], name := "C", repeatableScope := [10, 20], policy := { kind := .number { scale := 0, signed := true } } }]
    repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 2 },
      { level := 20, path := ["Form", "Rows", "Items"], repeatability := some 2 }] }
  let row (n : String) := Json.mkObj [("N", .str n), ("Items", .arr #[
    Json.mkObj [("C", .str "1")], Json.mkObj [("C", .str "2")]])]
  HavingFixture.runModel nested "AllFieldsFilled(Rows*/Items*) And FieldFilled(Rows/N)"
    false "" "unused" "unused" (ruleExpected := "7")
    (rowsOverride := some (#[row "2", row "5"] ++ if extra then #[Json.mkObj [("N", .str "11")]] else #[]))

example : [false, true].all (fun extra => decide (
    excludedOuterRow extra = some (.fired .omission, ["value 7"]))) = true := by native_decide

private def fresh (seed produced expected : String) :=
  HavingFixture.runModel model "NoFieldFilled(Rows/Pair, $Expected)" true seed "unused" "unused"
    (producerOperation := "\"" ++ produced ++ "\"") (rowsOverride := some rows) (ruleExpected := expected)

example : fresh "" "drop" "7" = some (.fired .omission, ["value drop", "value 0"]) ∧
    fresh "drop" "" "0" = some (.fired .omission, ["cleared", "value 7"]) := by native_decide

private def nestedModel : FlatModel := { HavingFixture.model with
  fields := (HavingFixture.model.fields.map fun field =>
    if field.id == 5 then { field with groupPath := ["Form", "Rows"], repeatableScope := [10] } else field) ++ [{
      id := 6, groupPath := ["Form", "Rows", "Pair", "Items"], name := "C", repeatableScope := [10, 20],
      policy := { kind := .number { scale := 0, signed := true } } }]
  repeatableGroups := HavingFixture.model.repeatableGroups ++ [{
    level := 20, path := ["Form", "Rows", "Pair", "Items"], repeatability := some 2 }] }

private def nestedRun (captured : Bool) (operand : String := "Pair/Items*/C") : Option (List Bool × List String) := do
  let world : World := { now := { epochMillis := 0 } }
  let dm : DmModel := { flat := nestedModel, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let row (n : String) (values : List String) := Json.mkObj [
    ("N", .str n), ("Tag", .str "x"), ("Out", .str "99"), ("Pair", Json.mkObj [
      ("Items", .arr ((values.map fun value => Json.mkObj [("C", .str value)]).toArray))])]
  let input ← (readDocument dm (Json.mkObj [("Form", Json.mkObj [
    ("Rows", .arr #[row "2" ["1", "1"], row "5" ["2"], row "7" []])])])).toOption
  if !input.refusals.isEmpty then none
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler nestedModel).toOption
  let document ← (checkDocument prepared "en_US" input.data).toOption
  let operation := "Sum(/Form/Rows*/N Having AllFieldsFilled(" ++ (if captured then "$" else "") ++
    operand ++ ") And FieldFilled(N))"
  let rule ← (checkRule dm .english {
    group := ["Form", "Rows"], name := "Nested", errorCode := "NESTED", errorEntityRelPath := "../N",
    condition := "FieldFilled(N) And " ++ operation ++ " > 0", severity := "ERROR" } world).toOption
  let verdicts ← (rule.evalOrdinaryRepeatableFull document (some world)).toOption
  let (_, computation) ← (lowerComputation nestedModel .english {
    group := ["Form", "Rows"], name := "Nested", targetRelPath := "../Out", commonPrecondition := none,
    alternatives := [{ precondition := none, operation }], errorCodesToSuppress := [] }).toOption
  let outcomes ← (runComputations world prepared document [computation]).toOption
  pure (verdicts.map (fun result => result.2.verdict.keepsHaving), outcomes.map (·.outcome))

example : ["Pair/Items*/C", "Pair"].all (fun operand => decide (
    nestedRun false operand = some ([true, true, true], ["value 2", "value 2", "value 2"]) ∧
    nestedRun true operand = some ([true, false, false], ["value 14", "value 0", "value 0"]))) = true := by native_decide

private def nestedReferences (operand : String) : Option (Option (List RepeatableLevel) × Bool × Bool) := do
  let parsed ← (parseText .english ("FieldValuesNotUnique(/Form/Rows*/Tag Having AllFieldsFilled(" ++
    operand ++ ") And FieldFilled(N))")).toOption
  let checked ← (lowerCondition nestedModel ["Form", "Rows"] false parsed.body).toOption
  let numeric ← (parseText .english ("Sum(/Form/Rows*/N Having AllFieldsFilled(" ++
    operand ++ ") And FieldFilled(N)) > 0")).toOption
  let numericChecked ← (lowerCondition nestedModel ["Form", "Rows"] false numeric.body).toOption
  let scope ← numericChecked.core.ordinaryIterationScope.toOption
  let pointers ← (checked.core.referencePointers [(10, 2)]).toOption
  pure (scope, pointers.contains { field := 6, coordinates := [.wildcard, .wildcard] },
    pointers.contains { field := 6, coordinates := [.concrete 2, .wildcard] })

example : ["Pair/Items*/C", "Pair"].all (fun operand => decide (
    nestedReferences operand = some (none, true, false) ∧
    nestedReferences ("$" ++ operand) = some (some [10], false, true))) = true := by native_decide

private def admitted (operand : String) : Bool :=
  ((parseText .english ("Sum(Rows*/N Having AllFieldsFilled(" ++ operand ++
    ") And FieldFilled(Rows/N)) > 0")).toOption.bind fun parsed =>
      (lowerCondition model ["Form"] false parsed.body).toOption).isSome

example : ["Rows/Pair", "Rows*/Pair", "Rows*/Pair/A", "Rows*/Pair, Rows*/Pair"].all admitted = true ∧
    ["Rows/Pair/A", "Rows/Pair, Rows/Pair", "Rows/Pair, Rows/Pair/A", "/Form", "Rows/Pair/A[1]"].all (fun operand => !admitted operand) = true := by native_decide

private def booleanModel : FlatModel := { model with fields := model.fields.map fun field =>
  if field.id == 6 || field.id == 7 then { field with policy := { kind := .boolean } } else field }

example : (HavingFixture.runModel booleanModel "AllFieldsFilled(Rows/Pair)" false "" "unused" "unused"
    (rowsOverride := some #[row "2" "false" "false", row "5" "false" "", row "7" "" ""])).map (·.2) = some ["value 2"] ∧
    run "MoreThanOneFieldFilled(Rows/Pair, Rows/Pair/A)" = none := by native_decide

private def carrier (operation : String) (guard : Option String := none) :=
  (HavingFixture.runModel model "AllFieldsFilled(Rows/Pair)" false "" "unused" "unused"
    (rowsOverride := some rows) (operationOverride := some operation) (computationPrecondition := guard)
    (ruleCondition := if guard.isSome then some "FieldFilled(Error)" else none)).map (·.2)
example : carrier "FirstFilledValue(Rows*/N Having AllFieldsFilled(Rows/Pair))" = some ["value 2"] ∧
    carrier "77" (some "AtLeastOneFieldFilled(Rows*/N Having AllFieldsFilled(Rows/Pair))") =
      some ["value 77"] := by native_decide

private def poisonMatrix (full : Bool) := operators.map fun operator =>
  (HavingFixture.runModel model (operator ++ "(Rows*/Pair) And FieldFilled(Rows/N)") false "" "unused" "unused"
    (extra := [("Out", .str "99")])
    (rowsOverride := some (if full then #[row "2" "1" "bad", row "5" "2" "bad", row "7" "3" "bad"]
      else #[row "2" "1" "bad", row "5" "2" "bad"]))).map (·.2)
example : poisonMatrix false = [some ["value 0"], some ["value 0"], some ["value 7"], some ["value 7"],
      some ["value 7"], some ["value 7"], some ["value 7"]] ∧
    poisonMatrix true = [some ["cleared"], some ["value 0"], some ["value 14"], some ["value 14"],
      some ["cleared"], some ["value 14"], some ["cleared"]] := by native_decide

private def declaredOuterRows (operand : String) : Option (List Bool) := do
  let world : World := { now := { epochMillis := 0 } }
  let dm : DmModel := { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let input ← (readDocument dm (Json.mkObj [("Form", Json.mkObj [
    ("Rows", .arr #[row "2" "1" "1", row "5" "2" "2"])])])).toOption
  if !input.refusals.isEmpty then none
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let document ← (checkDocument prepared "en_US" input.data).toOption
  let rule ← (checkRule dm .english {
    group := ["Form", "Rows"], name := "Declared", errorCode := "DECLARED", errorEntityRelPath := "../N",
    condition := "Sum(/Form/Rows*/N Having AllFieldsFilled(" ++ operand ++ ") And FieldFilled(N)) > 0",
    severity := "ERROR" } world).toOption
  let results ← (rule.evalOrdinaryRepeatableFull document (some world)).toOption
  pure (results.map fun result => result.2.verdict.keepsHaving)

example : ["$Pair/A, $Pair/B", "$Pair", "$/Form/Rows"].map declaredOuterRows =
    List.replicate 3 (some [true, true, false]) := by native_decide

end A12Kernel.Dm.HavingFieldFillLocks
