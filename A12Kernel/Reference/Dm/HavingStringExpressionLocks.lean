import A12Kernel.Reference.Dm.HavingFixture

namespace A12Kernel.Dm.HavingStringExpressionLocks
open Lean A12Kernel

example : HavingFixture.run "[Rows/Tag] == [$Expected]" =
    some (.fired .omission, ["value 9"]) := by native_decide

example : HavingFixture.run "[Rows/Tag] + [$Expected] == \"ab\""
    (expected := "b") (first := "a") (second := "c") =
    some (.fired .omission, ["value 9"]) := by native_decide

example : HavingFixture.run "RangeAsString(Rows/Tag,1,1) == \"k\"" =
    some (.fired .omission, ["value 9"]) := by native_decide

example : HavingFixture.runModel HavingFixture.model
    "FieldValueAsString(Rows/N) == \"2\"" false "keep" "keep" "drop"
    (ruleExpected := "2") = some (.fired .omission, ["value 2"]) := by native_decide

private def numericExpected : FlatModel := { HavingFixture.model with
  fields := HavingFixture.model.fields.map fun field => if field.id == 2 then
    { field with policy := { kind := .number { scale := 2, signed := true } } } else field }

example : HavingFixture.runModel numericExpected
    "[Rows/Tag] + FieldValueAsString($Expected) == \"keep1.5\"" true "9" "keep" "drop"
    (producerOperation := "1.5") (ruleExpected := "0") =
    some (.fired .omission, ["value 1.5", "value 9"]) := by native_decide

example : HavingFixture.runModel HavingFixture.model
    "[Rows/N] + [Rows/N] == 4" false "keep" "keep" "drop" (ruleExpected := "2") =
    some (.fired .omission, ["value 2"]) := by native_decide

private def run (filter selected : String) (expected : String := "keep")
    (first : String := "keep") (second : String := "drop") (fixture : FlatModel := HavingFixture.model) :=
  HavingFixture.runModel fixture filter false expected first second (ruleExpected := selected)

private def enumeration (display : Bool) : EnumerationDeclaration := {
  storedTokens := ["keep", "drop"]
  displayFacts := if display then [{ locale := "en_US", stored := "keep", display := "KEPT" },
    { locale := "en_US", stored := "drop", display := "DROPPED" }] else []
  categories := [{ name := "Label", tokens := ["KEEP", "DROP"] }] }
private def enumerationModel (display : Bool) : FlatModel := { HavingFixture.model with
  fields := HavingFixture.model.fields.map fun field => if field.id == 2 || field.id == 3 then
    { field with policy := { kind := .enumeration }, enumeration := some (enumeration display) } else field }
private def customModel : FlatModel := { HavingFixture.model with
  fields := HavingFixture.model.fields.map fun field => if field.id == 3 then
    { field with customType := some { name := "SelectorToken" } } else field }
private def customValidator (name : String) : Option RegisteredCustomFieldValidator :=
  if name == "SelectorToken" then some fun value _ =>
    if value == "bad" then some { projectCode := "TOKEN_REJECTED" } else none
  else none
private def namedTypeModel : FlatModel := { HavingFixture.model with
  fields := HavingFixture.model.fields.map fun field => if field.id == 3 then
    { field with stringPatternSource := some "[0-9]+", stringPolicy := { maxLength := some 2 } } else field }
private def rawModel : FlatModel := { HavingFixture.model with
  fields := HavingFixture.model.fields.map fun field => if field.id == 3 then
    { field with stringValueMode := .raw } else field }

example : ["{[Rows/Tag] + {[$Expected] + \"!\"}} == \"ab!\"",
    "\"ab!\" == {[Rows/Tag] + {[$Expected] + \"!\"}}"].all (fun source =>
      run source "9" "b" "a" "c" == some (.fired .omission, ["value 9"])) = true ∧
    HavingFixture.run "[Rows/Tag] + [$Expected] == \"ab\"" true
      (expected := "b") (first := "a") (second := "c") =
      some (.fired .omission, ["value drop", "value 0"]) := by native_decide

example : ["RangeAsString(Rows/Tag,2,3) == \"bc\"",
    "RangeAsString(Rows/Tag,1,3) == \"abc\""].all (fun source =>
      run source "9" "abc" "abc" "d" == some (.fired .omission, ["value 9"])) = true ∧
    run "RangeAsString(Rows/Tag,1,4) + \"x\" == \"x\"" "14" "abc" "abc" "d" =
      some (.fired .omission, ["value 14"]) ∧
    run "RangeAsString(Rows/Tag,1,1) + \"x\" == \"x\"" "9" "unused" "" "d" =
      some (.fired .omission, ["value 9"]) ∧
    run "RangeAsString(Rows/Tag,2,2) == \"́\"" "9" "unused" "éx" "yx" =
      some (.fired .omission, ["value 9"]) ∧
    run "RangeAsString($Expected,2,3) + [Rows/Tag] == \"bca\"" "9" "abc" "a" "d" =
      some (.fired .omission, ["value 9"]) := by native_decide

example : run "[Rows/Tag] + FieldValueAsString($Expected) == \"keep1.5\""
      "9" "01.50" "keep" "drop" numericExpected = some (.fired .omission, ["value 9"]) ∧
    run "FieldValueAsString($Expected) + [Rows/Tag] == \"keep\""
      "9" "" "keep" "drop" numericExpected = some (.fired .omission, ["value 9"]) ∧
    HavingFixture.runModel numericExpected "FieldValueAsString($Expected) + [Rows/Tag] == \"keep\""
      false "bad" "keep" "drop" (extra := [("Out", .str "99")]) (ruleExpected := "0") =
      some (.fired .omission, ["cleared"]) := by native_decide

example : ["[Rows/Tag] + [$Expected] == \"x\"", "[$Expected] + [Rows/Tag] == \"x\""].all (fun source =>
      run source "9" "x" "" "drop" == some (.fired .omission, ["value 9"])) = true ∧
    ["==", "!="].all (fun op =>
      run ("[Rows/Tag] + [$Expected] " ++ op ++ " \"\"") "0" "" "" "" ==
        some (.fired .omission, ["value 0"]) &&
      run ("[Rows/Tag] + [$Expected] " ++ op ++ " \"\"") "0" "" "keep" "drop" ==
        some (.fired .omission, ["value 0"]) &&
      run ("[Rows/Tag] + [$Expected] " ++ op ++ " \"x\"") "0" "" "" "" ==
        some (.fired .omission, ["value 0"])) = true := by native_decide

example : ["[Rows/Tag] + \"x\" == \"keepx\"", "\"x\" + [Rows/Tag] == \"xkeep\"",
    "RangeAsString(Rows/Tag,1,1) + \"x\" == \"kx\""].all (fun source =>
      HavingFixture.runModel HavingFixture.model source false "keep" "😀b" "keep"
        (extra := [("Out", .str "99")]) (ruleExpected := "5") ==
        some (.fired .omission, ["cleared"])) = true ∧
    HavingFixture.runModel HavingFixture.model "[Rows/Tag] + \"x\" == \"keepx\" Or [Rows/N] > 0"
      false "keep" "😀b" "keep" (extra := [("Out", .str "99")]) (ruleExpected := "14") =
      some (.fired .omission, ["cleared"]) := by native_decide

example : [false, true].all (fun display =>
    run "[Rows/Tag -> Label] + [$Expected -> Label] == \"KEEPKEEP\""
      "9" "keep" "keep" "drop" (enumerationModel display) ==
      some (.fired .omission, ["value 9"])) = true ∧
    run "[Rows/Tag] + \"!\" == \"keep!\"" "9" "keep" "keep" "drop" (enumerationModel false) =
      some (.fired .omission, ["value 9"]) ∧
    HavingFixture.admissions (enumerationModel true) "[Rows/Tag] + \"!\" == \"keep!\"" = (false, false) ∧
    [false, true].all (fun display => HavingFixture.admissions (enumerationModel display)
      "RangeAsString(Rows/Tag,1,1) + \"!\" == \"k!\"" == (false, false)) = true := by native_decide

example : ["[Rows/Tag] + \"!\" == \"keep!\"", "RangeAsString(Rows/Tag,1,1) + \"!\" == \"k!\""].all
    (fun source => HavingFixture.runModel customModel source false "keep" "keep" "drop"
      (customFieldValidator? := customValidator) == some (.fired .omission, ["value 9"])) = true ∧
    HavingFixture.runModel customModel "[Rows/Tag] + \"!\" == \"keep!\"" false "keep" "bad" "keep"
      (extra := [("Out", .str "99")]) (ruleExpected := "5") (customFieldValidator? := customValidator) =
      some (.fired .omission, ["cleared"]) ∧
    run "[Rows/Tag] + \"!\" == \"12!\"" "9" "12" "12" "34" namedTypeModel =
      some (.fired .omission, ["value 9"]) := by native_decide

example : run "FirstFilledValue(Rows/Tag,$Expected) + \"!\" == \"keep!\"" "9" =
      some (.fired .omission, ["value 9"]) ∧
    run "FirstFilledValue(Rows/Tag,$Expected) + \"!\" == \"keep!\"" "9" "keep" "" "drop" =
      some (.fired .omission, ["value 9"]) ∧
    run "FirstFilledValue(Rows*/Tag,$Expected) + \"!\" == \"keep!\" And FieldFilled(Rows/N)" "14" =
      some (.fired .omission, ["value 14"]) ∧
    HavingFixture.runModel HavingFixture.model "FirstFilledValue(Rows/Tag,$Expected) + \"!\" == \"keep!\""
      true "keep" "" "drop" "\"drop\"" = some (.fired .omission, ["value drop", "value 0"]) := by native_decide

example : ["[Rows/Tag] + \"x\" < \"keepx\"", "[Rows/Tag] + [Rows/N] == \"keep2\"",
    "RangeAsString([Rows/Tag],1,1) == \"k\"", "RangeAsString(Rows/N,1,1) == \"2\"",
    "RangeAsString(Rows/Tag,0,1) == \"k\"", "RangeAsString(Rows/Tag,2,1) == \"k\"",
    "RangeAsString(Rows/Tag,1.5,2) == \"k\"", "RangeAsString(\"keep\",1,1) == \"k\"",
    "FieldValueAsString([Rows/N]) == \"2\"", "FieldValueAsString(Rows/Tag) == \"keep\"",
    "FieldValueAsString(1) == \"1\"", "FieldValueAsString(FirstFilledValue(Rows/N,$Out)) == \"2\"",
    "RangeAsString(FirstFilledValue(Rows/Tag,$Expected),1,1) == \"k\""].all (fun source =>
      HavingFixture.admissions HavingFixture.model source == (false, false)) = true ∧
    ["[Rows/Tag] + \"!\" == \"keep!\"", "RangeAsString(Rows/Tag,1,1) + \"!\" == \"k!\""].all
      (fun source => HavingFixture.admissions rawModel source == (false, false)) = true := by native_decide

private def pointerModel : FlatModel := { HavingFixture.model with fields := HavingFixture.model.fields ++ [
  { id := 6, groupPath := ["Form", "Rows"], name := "Other", policy := { kind := .string }, repeatableScope := [10] }] }

example : ["[/Form/Rows/Tag] + [$/Form/Rows/Tag] == \"keepkeep\"",
    "RangeAsString(/Form/Rows/Tag,1,1) + RangeAsString($/Form/Rows/Tag,1,1) == \"kk\"",
    "FirstFilledValue(/Form/Rows*/Tag,$/Form/Rows/Tag) + \"!\" == \"keep!\" And FieldFilled(/Form/Rows/N)"].all
    (fun source => HavingFixture.referencesFor source pointerModel "Other" == some (true, true)) = true ∧
    HavingFixture.referencesFor "[N] > 0 And [$/Form/Rows/Tag] + \"!\" == \"keep!\""
      pointerModel "Other" = some (false, true) ∧
    HavingFixture.referencesFor "[/Form/Rows/Tag] + [$/Form/Expected] == \"keepkeep\""
      pointerModel "Other" = some (true, false) ∧
    HavingFixture.referencesFor "FieldValueAsString(/Form/Rows/N) + [/Form/Rows/Tag] == \"2keep\""
      pointerModel "Other" = some (true, false) := by native_decide

private def temporalPlanModel : FlatModel := { HavingFixture.model with fields := HavingFixture.model.fields.map fun field =>
  if field.id == 2 then { field with policy := { kind := .number { scale := 0, signed := true } } }
  else if field.id == 3 then { field with policy := { kind := .temporal .date TemporalComponents.fullDate }, temporalTargetPolicy := some { format := "yyyy-MM-dd" } }
  else field }

private def temporalPlan (filter : String) (fresh : Bool) : Except String (List (Option String)) := do
  let dm : DmModel := { flat := temporalPlanModel, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let input ← (readDocument dm (Json.mkObj [("Form", Json.mkObj [("Expected", .str "9"),
    ("Rows", .arr #[Json.mkObj [("Tag", .str "2024-01-01"), ("N", .str "2")]])])])).mapError reprStr
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler temporalPlanModel).mapError reprStr
  let document ← (checkDocument prepared "en_US" input.data).mapError reprStr
  let lower (target operation : String) (precondition : Option String) :
      Except String (CheckedNumericComputationTable temporalPlanModel) := do
    let (_, .number table _) ← (lowerComputation temporalPlanModel .english {
      group := ["Form"], name := target, targetRelPath := "../" ++ target, commonPrecondition := none,
      alternatives := [{ precondition, operation }], errorCodesToSuppress := [] }).mapError reprStr | throw "not numeric"
    pure table
  let consumer ← lower "Out" "1" (some ("MinValue(Rows*/Tag Having " ++ filter ++ ") == \"01.01.2024\""))
  let producer ← lower "Expected" "2" none
  let plan ← (certifyRepeatableNumberPlan (if fresh then [consumer, producer] else [consumer])).mapError reprStr
  let outputs ← (plan.execute world document).mapError reprStr
  pure (outputs.map fun result => match result.outcome with | .accepted stored => some stored.render | _ => none)

example : (temporalPlan "[Rows/N] == [$Expected]" true).toOption = some [some "2", some "1"] ∧
    (temporalPlan "FieldValueAsString(Rows/N) == \"2\"" false).toOption = some [some "1"] := by native_decide

example : (temporalPlan "FieldValueAsString(Rows/N) == FieldValueAsString($Expected)" true).toOption =
    some [some "2", some "1"] := by native_decide

end A12Kernel.Dm.HavingStringExpressionLocks
