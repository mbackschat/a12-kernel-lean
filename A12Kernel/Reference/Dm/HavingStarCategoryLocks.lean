import A12Kernel.Reference.Dm.HavingFixture

namespace A12Kernel.Dm.HavingStarCategoryLocks
open A12Kernel

private def model : FlatModel := { HavingFixture.model with
  fields := HavingFixture.model.fields.map fun field => if field.id == 3 then
    { field with policy := { kind := .enumeration }, enumeration := some {
      storedTokens := ["keep", "drop"], categories := [{ name := "Label", tokens := ["K", "D"] }] } }
    else field }

private def diagnostic (text : String) := HavingFixture.filterDiagnostic? model text

example : model.validate.isOk = true := by native_decide

example : diagnostic "AllFieldsFilled(Rows*/N->Label)" = some .noEnumeration ∧
    diagnostic "RepetitionNotUnique(Rows*/N->Label)" = some .noEnumeration ∧
    diagnostic "FirstFilledValue(Rows*/N->Label) == \"K\"" = some .noEnumeration := by native_decide

example : diagnostic "FirstFilledValue(Rows/N->Label, Rows/N) == \"K\"" = some .noEnumeration ∧
    diagnostic "FirstFilledValue(Rows*/Tag->Missing) > \"K\"" = some .categoryUnknown ∧
    diagnostic "FirstFilledValue(Rows*/Tag->Label) > \"K\"" = some .invalidTypeForComparison := by native_decide

example : [
    "AllFieldsFilled(Rows*/Tag->Missing)",
    "RepetitionNotUnique(Rows*/Tag->Missing)",
    "FirstFilledValue(Rows*/Tag->Missing) == \"K\"",
    "NumberOfValueInFields(\"K\" In Rows*/Tag->Missing) == 2",
    "NoFieldValueIncludedInValueList(Rows*/Tag->Missing In Rows/Tag)"].all
    (fun text => diagnostic text == some .categoryUnknown &&
      HavingFixture.admissions model text == (false, false)) = true := by native_decide

example : [
    "AllFieldsFilled(Rows*->Label)",
    "RepetitionNotUnique(Rows*->Label)",
    "FirstFilledValue(Rows*->Label) == \"K\"",
    "NumberOfValueInFields(\"K\" In Rows*->Label) == 2"].all
    (fun text => diagnostic text == some .noGroupsAllowed) = true := by native_decide

example : diagnostic "RepetitionNotUnique(Rows*/Tag->Label, Rows/N, Rows/N)" = some .duplicateParam1 ∧
    diagnostic "RepetitionNotUnique(Rows/N, Rows/N, Rows*/Tag->Label)" = some .duplicateParam1 ∧
    diagnostic "RepetitionNotUnique(Rows*/Tag->Label)" = some .categoryNotAllowed ∧
    diagnostic "AllFieldsFilled(Rows*/Tag->Label)" = some .categoryNotAllowed := by native_decide

example : ["AllFieldsFilled", "NoFieldFilled", "AtLeastOneFieldFilled", "NotAllFieldsFilled",
    "FieldsNotCollectivelyFilled", "NotExactlyOneFieldFilled", "MoreThanOneFieldFilled",
    "AllGroupsFilled", "NoGroupFilled", "AtLeastOneGroupFilled", "NotAllGroupsFilled",
    "GroupsNotCollectivelyFilled", "FieldValuesNotUnique"].all
    (fun op => diagnostic (op ++ "(Rows*/Tag->Missing)") == some .categoryUnknown) = true ∧
    ["Sum", "MinValue", "MaxValue", "NumberOfDifferentValues", "NumberOfFilledFields"].all
    (fun op => diagnostic (op ++ "(Rows*/Tag->Missing) > 0") == some .categoryUnknown) = true ∧
    diagnostic "SumOfProducts(Rows*/Tag->Missing, Rows*/N) > 0" = some .categoryUnknown ∧
    diagnostic "DateRangesOverlap(Rows*/Tag->Missing, Rows/N)" = some .categoryUnknown := by native_decide

private def run (text : String) :=
  HavingFixture.runModel model (text ++ " And [Rows/N] > 0") false "keep" "keep" "drop"
    (ruleExpected := "14")

example : run "FirstFilledValue(Rows*/Tag->Label) == \"K\"" =
    some (.fired .omission, ["value 14"]) ∧
    run "NumberOfValueInFields(\"K\" In Rows*/Tag->Label) == 2" =
    some (.fired .omission, ["value 14"]) := by native_decide

example : run "NoFieldValueIncludedInValueList(Rows*/Tag->Label In Rows/Tag)" =
    some (.fired .omission, ["value 14"]) ∧
    run "AtLeastOneFieldValueIncludedInValueList(Rows*/Tag->Label In \"K\")" =
    some (.fired .omission, ["value 14"]) := by native_decide

private def nestedModel : FlatModel := { model with fields := model.fields.map fun field =>
  if field.id == 3 then { field with groupPath := ["Form", "Rows", "Labels"], name := "E" } else field }

private def nestedRows : Array Lean.Json := #[ ("keep", "2"), ("drop", "5"), ("keep", "7") ].map fun (tag, n) =>
  Lean.Json.mkObj [("N", Lean.Json.str n), ("Labels", Lean.Json.mkObj [("E", Lean.Json.str tag)])]

private def nestedRun (filter expected : String) :=
  HavingFixture.runModel nestedModel filter false "keep" "keep" "drop"
    (ruleExpected := expected) (rowsOverride := some nestedRows)

example : nestedModel.validate.isOk = true ∧
    nestedRun "FirstFilledValue(Rows/Labels, Rows*/Labels/E->Label) == \"keep\"" "9" =
      some (.fired .omission, ["value 9"]) ∧
    nestedRun "FirstFilledValue(Rows*/Labels/E->Label, Rows/Labels) == \"K\"" "14" =
      some (.fired .omission, ["value 14"]) ∧
    HavingFixture.filterDiagnostic? nestedModel
      "FirstFilledValue(Rows/Labels, Rows*/Labels/E) == \"keep\"" = some .duplicateParam2 := by native_decide

end A12Kernel.Dm.HavingStarCategoryLocks
