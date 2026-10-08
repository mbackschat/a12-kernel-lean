import A12Kernel.Reference.Dm.HavingFixture

namespace A12Kernel.Dm.HavingSelectedComparisonLocks
open Lean A12Kernel

example : HavingFixture.run "FirstFilledValue(Rows/Tag,$Expected) == \"keep\"" =
      some (.fired .omission, ["value 9"]) ∧
    HavingFixture.run "FirstFilledValue(Rows/Tag,$Expected) == False" (kind := .boolean)
      (expected := "true") (first := "false") (second := "true") =
      some (.fired .omission, ["value 9"]) := by native_decide

private def run (filter : String) (expected first second selected : String)
    (model : FlatModel := HavingFixture.model) :=
  HavingFixture.runModel model filter false expected first second (ruleExpected := selected)

example : ["FirstFilledValue(Rows/Tag,$Expected) == \"keep\"", "\"keep\" == FirstFilledValue(Rows/Tag,$Expected)",
    "FirstFilledValue(Rows/Tag,$Expected) == [$Expected]",
    "FirstFilledValue(Rows/Tag,$Expected) == FirstFilledValue($Expected,Rows/Tag)"].all (fun filter =>
      run filter "keep" "keep" "drop" "9" == some (.fired .omission, ["value 9"]) &&
      run filter "keep" "" "drop" "9" == some (.fired .omission, ["value 9"])) = true ∧
    run "FirstFilledValue(Rows/Tag,$Expected) == \"keep\"" "" "" "" "0" =
      some (.fired .omission, ["value 0"]) ∧
    run "FirstFilledValue(Rows/Tag,$Expected) != \"\"" "keep" "keep" "drop" "0" =
      some (.fired .omission, ["value 0"]) ∧
    HavingFixture.runModel HavingFixture.model "FirstFilledValue(Rows/Tag,$Expected) == \"keep\"" true
      "keep" "" "drop" "\"drop\"" = some (.fired .omission, ["value drop", "value 0"]) := by native_decide

private def booleanModel : FlatModel := { HavingFixture.model with
  fields := HavingFixture.model.fields.map fun field => if field.id == 2 || field.id == 3 then
    { field with policy := { kind := .boolean } } else field }
example : run "FirstFilledValue(Rows/Tag,$Expected) == False" "true" "false" "true" "9" booleanModel =
      some (.fired .omission, ["value 9"]) ∧
    run "False == FirstFilledValue(Rows/Tag,$Expected)" "false" "" "true" "9" booleanModel =
      some (.fired .omission, ["value 9"]) ∧
    run "FirstFilledValue(Rows/Tag,$Expected) == True" "true" "bad" "true" "5" booleanModel =
      some (.fired .omission, []) ∧
    run "FirstFilledValue(Rows/Tag,$Expected) == [Rows/Tag]" "bad" "false" "true" "14" booleanModel =
      some (.fired .omission, ["value 14"]) := by native_decide

private def enumeration : EnumerationDeclaration := {
  storedTokens := ["keep", "drop"], categories := [{ name := "Label", tokens := ["KEEP", "DROP"] }] }
private def enumerationModel : FlatModel := { HavingFixture.model with
  fields := HavingFixture.model.fields.map fun field => if field.id == 2 || field.id == 3 then
    { field with policy := { kind := .enumeration }, enumeration := some enumeration } else field }
example : run "FirstFilledValue(Rows/Tag -> Label,$Expected -> Label) == \"KEEP\""
      "keep" "keep" "drop" "9" enumerationModel = some (.fired .omission, ["value 9"]) ∧
    run "FirstFilledValue(Rows*/Tag -> Label,$Expected -> Label) == \"KEEP\" And FieldFilled(Rows/N)"
      "keep" "keep" "drop" "14" enumerationModel = some (.fired .omission, ["value 14"]) ∧
    run "FirstFilledValue(Rows/Tag -> Label,Rows/Tag) == \"KEEP\""
      "keep" "keep" "drop" "9" enumerationModel = some (.fired .omission, ["value 9"]) ∧
    run "FirstFilledValue(Rows/Tag,$Expected) == \"outside\""
      "keep" "keep" "drop" "0" enumerationModel = some (.fired .omission, ["value 0"]) := by native_decide

private def rangeModel : FlatModel := { HavingFixture.model with
  fields := HavingFixture.model.fields.map fun field => if field.id == 2 || field.id == 3 then
    { field with
      policy := { kind := .dateRange }
      dateRangePolicy := some { format := "yyyy-MM-dd", separator := "/" } } else field }
example : ["FirstFilledValue(Rows/Tag,$Expected) == [$Expected]", "[$Expected] == FirstFilledValue(Rows/Tag,$Expected)"].all
    (fun filter => run filter "2024-01-01/2024-02-01" "2024-01-01/2024-02-01" "2024-01-01/2024-03-01" "9" rangeModel ==
      some (.fired .omission, ["value 9"]) &&
      run filter "2024-01-01/2024-02-01" "" "2024-01-01/2024-03-01" "9" rangeModel ==
        some (.fired .omission, ["value 9"])) = true := by native_decide

private def mixedRangeModel : FlatModel := { rangeModel with
  fields := rangeModel.fields.map fun field => if field.id == 3 then
    { field with dateRangePolicy := some { format := "dd.MM.yyyy", separator := "-" } } else field }
private def confirmModel : FlatModel := { booleanModel with
  fields := booleanModel.fields.map fun field => if field.id == 2 then
    { field with policy := { kind := .confirm } } else field }
example : HavingFixture.admissions rangeModel "FirstFilledValue(Rows/Tag,$Expected) == [$Expected]" = (true, true) ∧
    HavingFixture.admissions mixedRangeModel "FirstFilledValue(Rows/Tag,$Expected) == [$Expected]" = (false, false) ∧
    HavingFixture.admissions confirmModel "FirstFilledValue(Rows/Tag,$Expected) == True" = (false, false) ∧
    HavingFixture.admissions HavingFixture.model "FirstFilledValue(Rows/Tag,$Expected) < \"keep\"" = (false, false) ∧
    HavingFixture.admissions HavingFixture.model "FirstFilledValue(Rows/Tag,$Expected) == \"12:30:00\"" = (false, false) := by native_decide

private def mixedTextModel : FlatModel := { enumerationModel with
  fields := enumerationModel.fields.map fun field => if field.id == 2 then
    { field with policy := { kind := .string }, enumeration := none } else field }
example : run "FirstFilledValue(Rows/Tag -> Label,$Expected) == \"KEEP\""
      "KEEP" "" "drop" "9" mixedTextModel = some (.fired .omission, ["value 9"]) ∧
    HavingFixture.referencesFor "FirstFilledValue(/Form/Rows/Tag,$/Form/Rows/Tag) == \"keep\"" = some (true, true) ∧
    HavingFixture.referencesFor
      "FirstFilledValue(/Form/Rows*/Tag,$/Form/Rows/Tag) == \"keep\" And FieldFilled(/Form/Rows/N)" =
      some (true, true) ∧
    HavingFixture.referencesFor "FirstFilledValue(/Form/Rows/Tag,$/Form/Expected) == \"keep\"" =
      some (true, false) := by native_decide

private def rangeProfiles : List (String × String × String × String) := [
  ("dd.MM.yyyy", "-", "01.01.2024-01.02.2024", "01.01.2024-01.03.2024"),
  ("yyyy", "/", "2024/2025", "2024/2026"),
  ("yyyy-MM", "/", "2024-01/2024-02", "2024-01/2024-03"),
  ("MM", "/", "01/02", "01/03"),
  ("MM-dd", "/", "01-01/02-01", "01-01/03-01"),
  ("MM", "", "0102", "0103"),
  ("dd.MM", "-", "01.01-01.02", "01.01-01.03")]
example : rangeProfiles.all (fun (format, separator, first, second) =>
    let fixture := { rangeModel with fields := rangeModel.fields.map fun field =>
      if field.id == 2 || field.id == 3 then
        { field with dateRangePolicy := some { format, separator } } else field }
    run "FirstFilledValue(Rows/Tag,$Expected) == [$Expected]" first first second "9" fixture ==
      some (.fired .omission, ["value 9"])) = true := by native_decide

example : HavingFixture.admissions rangeModel
    "StartOfDateRange(FirstFilledValue(Rows/Tag,$Expected)) == \"01.01.2024\"" = (false, false) := by native_decide

private def customModel : FlatModel := { HavingFixture.model with
  fields := HavingFixture.model.fields.map fun field => if field.id == 3 then
    { field with customType := some { name := "SelectorToken" } } else field }
private def customValidator (name : String) : Option RegisteredCustomFieldValidator :=
  if name == "SelectorToken" then some fun value _ =>
    if value == "bad" then some { projectCode := "TOKEN_REJECTED" } else none
  else none
example : HavingFixture.runModel customModel "FirstFilledValue(Rows/Tag,$Expected) == \"keep\"" false
      "keep" "keep" "drop" (customFieldValidator? := customValidator) =
      some (.fired .omission, ["value 9"]) ∧
    HavingFixture.runModel customModel "FirstFilledValue(Rows/Tag,$Expected) == \"keep\"" false
      "keep" "bad" "keep" (ruleExpected := "5") (customFieldValidator? := customValidator) =
      some (.fired .omission, []) := by native_decide

private def ordered (left operator right : String) (reverse : Bool) : String :=
  if reverse then right ++ " " ++ operator ++ " " ++ left else left ++ " " ++ operator ++ " " ++ right

private def selectionEntries : List (FlatModel × String × String) := [
  (HavingFixture.model, "FirstFilledValue(Rows/Tag,$Expected)", "\"keep\""),
  (enumerationModel, "FirstFilledValue(Rows/Tag -> Label,$Expected -> Label)", "\"KEEP\""),
  (booleanModel, "FirstFilledValue(Rows/Tag,$Expected)", "True"),
  (rangeModel, "FirstFilledValue(Rows/Tag,$Expected)", "[$Expected]")]

example : selectionEntries.all (fun (fixture, left, right) =>
    ["<", "<=", ">", ">="].all fun operator => [false, true].all fun reverse =>
      let filter := ordered left operator right reverse
      HavingFixture.filterDiagnostic? fixture filter == some .invalidTypeForComparison &&
      HavingFixture.admissions fixture filter == (false, false)) = true := by native_decide

example : ["<", "<=", ">", ">="].all (fun operator => [false, true].all fun reverse =>
    HavingFixture.filterDiagnostic? enumerationModel
      (ordered "FirstFilledValue(Rows/Tag -> Missing,$Expected -> Label)" operator "\"KEEP\"" reverse) ==
        some .categoryUnknown) = true := by native_decide

example : (HavingFixture.filterDiagnostic? HavingFixture.model
    "FirstFilledValue($Expected,$Expected) == \"keep\"").any (fun diagnostic =>
      diagnostic != .invalidTypeForComparison &&
      ["<", "<=", ">", ">="].all fun operator => [false, true].all fun reverse =>
        HavingFixture.filterDiagnostic? HavingFixture.model
          (ordered "FirstFilledValue($Expected,$Expected)" operator "\"keep\"" reverse) == some diagnostic) = true := by native_decide

example : selectionEntries.all (fun (fixture, left, right) =>
    ["==", "!="].all fun operator => [false, true].all fun reverse =>
      HavingFixture.admissions fixture (ordered left operator right reverse) == (true, true)) = true := by native_decide

end A12Kernel.Dm.HavingSelectedComparisonLocks
