import A12Kernel.Reference.Dm.HavingFixture

namespace A12Kernel.Dm.HavingComparisonAdmissionLocks
open A12Kernel

private def enumeration (label : Option String := none) : EnumerationDeclaration := {
  storedTokens := ["a"], categories := [{ name := "Label", tokens := ["category"] }]
  displayFacts := label.map (fun display => [{ locale := "en_US", stored := "a", display }]) |>.getD [] }

private def model : FlatModel := { HavingFixture.model with
  fields := HavingFixture.model.fields ++ [
    { id := 6, name := "RowOut", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .number { scale := 0, signed := true } } },
    { id := 7, name := "Flag", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .boolean } },
    { id := 8, name := "OtherFlag", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .boolean } },
    { id := 9, name := "Yes", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .confirm } },
    { id := 10, name := "OtherYes", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .confirm } },
    { id := 11, name := "Choice", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .enumeration }, enumeration := some enumeration },
    { id := 12, name := "Labelled", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .enumeration }, enumeration := some (enumeration (some "A")) },
    { id := 13, name := "Conflict", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .enumeration }, enumeration := some (enumeration (some "B")) },
    { id := 14, name := "Identity", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .enumeration }, enumeration := some (enumeration (some "a")) }]
  repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 3, indexField := some 3 }] }

private def result (body : String) (row : Bool) : String × String :=
  HavingFixture.readerResults ("Sum(Rows*/N Having " ++ body ++ ")") model row

example : model.validate.isOk = true := by native_decide

private def admitted (index : String) : List String := [
  "[Rows/Flag" ++ index ++ "] == True",
  "{[Rows/Flag" ++ index ++ "]} == {True}", "{[Rows/Flag" ++ index ++ "]} == {[Rows/OtherFlag]}",
  "{[Rows/Yes" ++ index ++ "]} != {[Rows/OtherYes]}", "False != [Rows/Flag" ++ index ++ "]",
  "[Rows/Flag" ++ index ++ "] == [Rows/OtherFlag]", "[Rows/Yes" ++ index ++ "] == True",
  "[Rows/Yes" ++ index ++ "] != [Rows/OtherYes]",
  "FirstFilledValue(Rows/Flag" ++ index ++ ",Rows/OtherFlag) == True",
  "[Rows/Choice" ++ index ++ "] == \"a\"", "{\"a\"} == {[Rows/Choice" ++ index ++ "]}",
  "[Rows/Labelled->Label" ++ index ++ "] == \"category\"",
  "[Rows/Choice" ++ index ++ "] == [Rows/Identity]",
  "FirstFilledValue(Rows/Choice" ++ index ++ ",Rows/Identity) == \"missing\"",
  "[Rows/Labelled" ++ index ++ "] == {[Rows/Tag]}",
  "[Rows/Labelled" ++ index ++ "] == FirstFilledValue(Rows/Tag,Rows/Choice)",
  "[Rows/Choice->Label" ++ index ++ "] == [Rows/Labelled]",
  "{[Rows/Labelled" ++ index ++ "]} + \"x\" == \"not-a-token\""]

example : [false, true].all (fun row => (admitted "").all fun body =>
    result body row == ("admitted", "admitted")) = true := by native_decide

example : [false, true].all (fun row => (admitted " For \"keep\"").all fun body =>
    result body row == ("MVK_SEMANTIC_INDEX_NOT_ALLOWED", "MVK_SEMANTIC_INDEX_NOT_ALLOWED")) = true := by native_decide

private def refused (index : String) : List (String × String) := [
  ("[Rows/Yes" ++ index ++ "] == False", "MVK_INVALID_COMPARE_TO_YES"),
  ("[Rows/Yes" ++ index ++ "] == [Rows/OtherYes]", "MVK_INVALID_COMPARE_TO_YES"),
  ("[Rows/Yes" ++ index ++ "] != [Rows/Flag]", "MVK_INVALID_COMPARE_TO_YES"),
  ("[Rows/Flag" ++ index ++ "] == [Rows/N]", "MVK_INVALID_COMPARE_TO_YESNO"),
  ("[Rows/Flag" ++ index ++ "] > True", "MVK_INVALID_TYPE_FOR_COMPARISON"),
  ("[Rows/Choice" ++ index ++ "] == \"missing\"", "MVK_INVALID_STRING_CONSTANT_FOR_ENUM_COMPARISON"),
  ("{\"missing\"} == {[Rows/Labelled" ++ index ++ "]}", "MVK_INVALID_STRING_CONSTANT_FOR_ENUM_COMPARISON"),
  ("[Rows/Labelled->Label" ++ index ++ "] == \"a\"", "MVK_INVALID_STRING_CONSTANT_FOR_ENUM_COMPARISON"),
  ("[Rows/Labelled" ++ index ++ "] == [Rows/Tag]", "MVK_INVALID_COMPARE_ENUM_TO_STRING"),
  ("[Rows/Labelled" ++ index ++ "] == [Rows/Identity]", "MVK_INVALID_COMPARE_ENUM_TO_STRING"),
  ("[Rows/Labelled" ++ index ++ "] == [Rows/Conflict]", "MVK_INVALID_COMPARE_ENUM_TO_ENUM"),
  ("[Rows/Choice" ++ index ++ "] == [Rows/N]", "MVK_INVALID_COMPARE_TO_ENUM_OR_STRING"),
  ("[Rows/Tag] == {[Rows/Labelled" ++ index ++ "]}", "MVK_INVALID_COMPARE_ENUM_TO_STRING"),
  ("[Rows/Conflict] == {[Rows/Labelled" ++ index ++ "]}", "MVK_INVALID_COMPARE_ENUM_TO_ENUM"),
  ("[Rows/N] == [Rows/Flag" ++ index ++ "]", "MVK_INVALID_COMPARE_TO_YESNO"),
  ("False == {[Rows/Yes" ++ index ++ "]}", "MVK_INVALID_COMPARE_TO_YES"),
  ("True == [Rows/N" ++ index ++ "]", "MVK_INCONSISTENT_TYPES_COMPARED")]

example : [false, true].all (fun row => (refused " For \"keep\"").all fun (body, diagnostic) =>
    result body row == (diagnostic, diagnostic)) = true := by native_decide

example : [false, true].all (fun row =>
    ["[Rows/Flag For \"keep\"] == [Missing]", "[Rows/Choice For \"keep\"] == [Missing]",
      "[Rows/Labelled For \"keep\"] == [Missing]"].all fun body =>
        result body row == ("MVK_INVALID_ENTITY", "MVK_INVALID_ENTITY")) = true := by native_decide

example : [false, true].all (fun row => (refused "").all fun (body, diagnostic) =>
    result body row == (diagnostic, diagnostic)) = true := by native_decide

example : [false, true].all (fun row =>
    let preceding := "AtLeastOneFieldFilled(Rows*/N Having FieldFilled(Rows/N)) And "
    ["[Rows/Flag] == True", "[Rows/Choice] == \"a\""].all (fun body =>
      result (preceding ++ body) row ==
        (if row then ("MVK_DISALLOWED_CONSTRUCT_IN_FILTER_CONDITION", "MVK_DISALLOWED_CONSTRUCT_IN_FILTER_CONDITION")
         else ("MVK_NO_WILDCARD", "MVK_NO_WILDCARD"))) &&
    ["[$Rows/Flag] == True", "[$Rows/Choice] == \"a\""].all (fun body =>
      result (preceding ++ body) row == ("MVK_INVALID_OUTER_ITERATION", "MVK_INVALID_OUTER_ITERATION"))) = true := by native_decide

example : [false, true].all (fun row =>
    ["[Rows/Flag For \"keep\"] == True", "[Rows/Choice For \"keep\"] == \"a\""].all fun body =>
      result (body ++ " And FieldFilled(Missing)") row == ("MVK_INVALID_ENTITY", "MVK_INVALID_ENTITY")) = true := by native_decide

example : HavingFixture.run "{[Rows/Tag]} == {\"keep\"}" false .enumeration "keep" "keep" "drop"
    (some { storedTokens := ["keep", "drop"] }) = some (.fired .omission, ["value 9"]) ∧
    HavingFixture.run "{[Rows/Tag]} == {\"missing\"}" false .enumeration "keep" "keep" "drop"
    (some { storedTokens := ["keep", "drop"] }) = none := by native_decide


private def scopeModel : FlatModel := { model with
  fields := model.fields ++ [
    { id := 15, name := "N", groupPath := ["Form", "Other"], repeatableScope := [20], policy := { kind := .number { scale := 0, signed := true } } },
    { id := 16, name := "Scaled", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .number { scale := 2, signed := true } } },
    { id := 17, name := "Due", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .temporal .date .fullDate }, temporalTargetPolicy := some { format := "yyyy-MM-dd" } },
    { id := 18, name := "RootFlag", groupPath := ["Form"], policy := { kind := .boolean } }]
  repeatableGroups := model.repeatableGroups ++ [{ level := 20, path := ["Form", "Other"], repeatability := some 3 }] }

private def scopeCases : List (String × String × String) := [
  ("[Rows/N] < 1", "admitted", "admitted"),
  ("[Rows/Due] < [Rows/N]", "MVK_INVALID_COMPARE_TO_DATE", "MVK_INVALID_COMPARE_TO_DATE"),
  ("[Rows/N] < [Rows/Due]", "MVK_INVALID_COMPARE_TO_DATE", "MVK_INVALID_COMPARE_TO_DATE"),
  ("[Rows/Due] < [Rows/Due]", "admitted", "admitted"),
  ("[Rows/N] == [Rows/Scaled]", "MVK_INVALID_COMPARE_DEC_PLACES", "MVK_INVALID_COMPARE_DEC_PLACES"),
  ("[Rows/N] < [Rows/Scaled]", "admitted", "admitted"),
  ("[Other/N] > 0", "MVK_INVALID_ITERATION_IN_FILTER_CONDITION", "MVK_INVALID_ITERATION_IN_FILTER_CONDITION"),
  ("[$Other/N] > 0", "MVK_NO_WILDCARD", "MVK_NO_WILDCARD"),
  ("[$Rows/N] > 0", "MVK_NO_WILDCARD", "MVK_NO_ITERATION_FOR_WILDCARD"),
  ("[$Rows/N] == [Rows/Scaled]", "MVK_NO_WILDCARD", "MVK_INVALID_COMPARE_DEC_PLACES"),
  ("[$Other/N] == \"x\"", "MVK_NO_WILDCARD", "MVK_NO_WILDCARD"),
  ("[$Other/N] < [Rows/Due]", "MVK_NO_WILDCARD", "MVK_NO_WILDCARD"),
  ("[RootFlag] == True", "MVK_NO_ITERATION_FOR_WILDCARD", "MVK_NO_ITERATION_FOR_WILDCARD"),
  ("[RootFlag] == True And CurrentRepetition(Rows) > 0", "admitted", "admitted"),
  ("[Other/N] > 0 And [Rows/N] == 1.5", "MVK_INVALID_COMPARE_DEC_PLACES", "MVK_INVALID_COMPARE_DEC_PLACES"),
  ("[Rows/N] == 1.5 And [Other/N] > 0", "MVK_INVALID_COMPARE_DEC_PLACES", "MVK_INVALID_COMPARE_DEC_PLACES"),
  ("[$Other/N] > 0 And [Rows/N] == 1.5", "MVK_NO_WILDCARD", "MVK_NO_WILDCARD"),
  ("[Rows/N] == 1.5 And [$Other/N] > 0", "MVK_INVALID_COMPARE_DEC_PLACES", "MVK_INVALID_COMPARE_DEC_PLACES"),
  ("[Other/N] > 0 Or [Rows/N] == 1.5", "MVK_INVALID_COMPARE_DEC_PLACES", "MVK_INVALID_COMPARE_DEC_PLACES"),
  ("[Rows/N] == 1.5 Or [Other/N] > 0", "MVK_INVALID_COMPARE_DEC_PLACES", "MVK_INVALID_COMPARE_DEC_PLACES"),
  ("[$Other/N] > 0 Or [Rows/N] == 1.5", "MVK_NO_WILDCARD", "MVK_NO_WILDCARD"),
  ("[Rows/N] == 1.5 Or [$Other/N] > 0", "MVK_INVALID_COMPARE_DEC_PLACES", "MVK_INVALID_COMPARE_DEC_PLACES")]

-- Read failures and comparison gates precede filter iteration; the 2026-10-09 H10 admission checkpoint separates both orders.
example : scopeCases.all (fun (body, root, row) =>
    HavingFixture.readerResults ("Sum(Rows*/N Having " ++ body ++ ")") scopeModel false == (root, root) &&
    HavingFixture.readerResults ("Sum(Rows*/N Having " ++ body ++ ")") scopeModel true == (row, row)) = true := by native_decide

end A12Kernel.Dm.HavingComparisonAdmissionLocks
