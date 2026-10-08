import A12Kernel.Reference.Dm.HavingFixture

namespace A12Kernel.Dm.HavingForbiddenLocks
open A12Kernel

private def diagnostic (filter : String) : Option String :=
  (HavingFixture.filterDiagnostic? HavingFixture.model filter).map (·.kernelCode)

private def customs := ["CustomCondition Check", "CustomCondition 'True'", "CustomCondition Own:Check"]

private def combine (left right : String) (operator : String) (reverse : Bool) : String :=
  let (first, second) := if reverse then (right, left) else (left, right)
  "(" ++ first ++ ") " ++ operator ++ " (" ++ second ++ ")"

example : customs.all (fun custom =>
    diagnostic custom == some "MVK_NO_ITERATION_FOR_WILDCARD" &&
    HavingFixture.admissions HavingFixture.model custom == (false, false)) = true := by native_decide

example : customs.all (fun custom => ["And", "Or"].all fun operator => [false, true].all fun reverse =>
    ["FieldFilled(Rows/N)", "FieldNotFilled(Rows/N)"].all fun sibling =>
      let filter := combine custom sibling operator reverse
      diagnostic filter == some "MVK_DISALLOWED_CONSTRUCT_IN_FILTER_CONDITION" &&
      HavingFixture.admissions HavingFixture.model filter == (false, false)) = true := by native_decide

example : customs.all (fun custom => ["And", "Or"].all fun operator => [false, true].all fun reverse =>
    diagnostic (combine custom "[Rows/Tag] > \"keep\"" operator reverse) == some "MVK_INVALID_TYPE_FOR_COMPARISON" &&
    diagnostic (combine custom "FieldFilled(Expected)" operator reverse) == some "MVK_NO_ITERATION_FOR_WILDCARD" &&
    diagnostic (combine custom "FieldFilled($Rows/N)" operator reverse) == some "MVK_NO_WILDCARD") = true := by native_decide

example : ["And", "Or"].all (fun first => ["And", "Or"].all fun second =>
    diagnostic (combine (combine "CustomCondition Check" "FieldFilled(Expected)" first false)
      "FieldFilled(Rows/N)" second false) == some "MVK_DISALLOWED_CONSTRUCT_IN_FILTER_CONDITION" &&
    diagnostic (combine (combine "FieldFilled(Rows/N)" "CustomCondition Check" first false)
      "[Rows/Tag] > \"keep\"" second false) == some "MVK_INVALID_TYPE_FOR_COMPARISON") = true := by native_decide

example : HavingFixture.run "FieldFilled(Rows/N) And [Rows/Tag] == \"keep\"" =
    some (.fired .omission, ["value 9"]) ∧
    HavingFixture.runModel HavingFixture.model "FieldFilled(Rows/N) Or [Rows/Tag] == \"keep\"" false
      "keep" "keep" "drop" (ruleExpected := "14") =
    some (.fired .omission, ["value 14"]) := by native_decide

private def otherGroupModel : FlatModel := { HavingFixture.model with
  fields := HavingFixture.model.fields ++ [{
    id := 6, groupPath := ["Form", "Other"], name := "N"
    policy := { kind := .number { scale := 0, signed := true } }, repeatableScope := [20] }]
  repeatableGroups := HavingFixture.model.repeatableGroups ++ [{ level := 20, path := ["Form", "Other"], repeatability := some 3 }] }

example : ["And", "Or"].all (fun operator => [false, true].all fun reverse =>
    HavingFixture.filterDiagnostic? otherGroupModel
      (combine "CustomCondition Check" "FieldFilled(Other/N) And FieldFilled(Rows/N)" operator reverse) ==
        some .invalidIterationInFilterCondition) = true ∧
    HavingFixture.filterDiagnostic? HavingFixture.model "ApplikationsBedingung Pruefung" .german =
      some .noIterationForWildcard ∧
    HavingFixture.filterDiagnostic? HavingFixture.model
      "FeldAngegeben(Rows/N) Und ApplikationsBedingung 'Wahr'" .german =
        some .disallowedConstructInFilterCondition := by native_decide

end A12Kernel.Dm.HavingForbiddenLocks
