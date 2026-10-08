import A12Kernel.Reference.Dm.HavingFixture

namespace A12Kernel.Dm.HavingCollectionCountLocks
open Lean A12Kernel

private def numberModel : FlatModel := { HavingFixture.model with fields := HavingFixture.model.fields.map fun field =>
  if field.id == 2 || field.id == 3 then { field with policy := { kind := .number { scale := 0, signed := false } } } else field }
private def run (filter selected : String) : Option (Verdict × List String) :=
  HavingFixture.runModel numberModel filter false "8" "8" "9" (ruleExpected := selected)

example : run "NumberOfFilledFields(Rows/Tag,Rows/N) == 2" "14" =
    some (.fired .omission, ["value 14"]) := by native_decide

example : run "NumberOfValueInFields(8 In Rows/Tag,Rows/N) == 1" "9" =
    some (.fired .omission, ["value 9"]) := by native_decide

example : HavingFixture.run "NumberOfDifferentValues(Rows/Tag,$Expected) == 1" =
    some (.fired .omission, ["value 9"]) := by native_decide

example : run "NumberOfFilledGroups(Rows*) == 3 And FieldFilled(Rows/N)" "14" =
    some (.fired .omission, ["value 14"]) := by native_decide

example : run "SumOfProducts(Rows*/Tag,Rows*/N) == 117 And FieldFilled(Rows/N)" "14" =
    some (.fired .omission, ["value 14"]) := by native_decide

example : HavingFixture.run "NumberOfValueInFields(\"keep\" In Rows/Tag,$Expected) == 2" =
    some (.fired .omission, ["value 9"]) := by native_decide

example : HavingFixture.run "NumberOfValueInFields(True In Rows/Tag,$Expected) == 2"
    (kind := .boolean) (expected := "true") (first := "true") (second := "false") =
    some (.fired .omission, ["value 9"]) := by native_decide

example : HavingFixture.run "NumberOfValueInFields(False In Rows/Tag,$Expected) == 0"
    (kind := .boolean) (expected := "true") (first := "true") (second := "false") =
    some (.fired .omission, ["value 9"]) := by native_decide

private def dateModel : FlatModel := { HavingFixture.model with fields := HavingFixture.model.fields.map fun field =>
  if field.id == 2 || field.id == 3 then { field with
    policy := { kind := .temporal .date .fullDate }, temporalTargetPolicy := some { format := "yyyy-MM-dd" } } else field }

example : HavingFixture.runModel dateModel "[Rows/Tag] == [$Expected]" false
    "2024-03-01" "2024-03-01" "2024-03-02" = some (.fired .omission, ["value 9"]) := by native_decide

example : HavingFixture.runModel dateModel "NumberOfDifferentValues(Rows/Tag,$Expected) == 1" false
    "2024-03-01" "2024-03-01" "2024-03-02" = some (.fired .omission, ["value 9"]) := by native_decide

example : run "Min(Max(NumberOfFilledFields(Rows/Tag,Rows/N) + 1,2),3) == 3" "14" =
      some (.fired .omission, ["value 14"]) ∧
    run "NumberOfDifferentValues(Rows/Tag,$Expected) == 1" "9" =
      some (.fired .omission, ["value 9"]) ∧
    HavingFixture.runModel numberModel "NumberOfValueInFields(8 In Rows/Tag,$Expected) == 1" true
      "8" "8" "9" "9" (ruleExpected := "5") =
        some (.fired .omission, ["value 9", "value 9"]) ∧
    HavingFixture.runModel HavingFixture.model "NumberOfValueInFields(\"keep\" In Rows/Tag,$Expected) == 1" true
      "keep" "keep" "drop" "\"drop\"" (ruleExpected := "5") =
        some (.fired .omission, ["value drop", "value 9"]) := by native_decide

private def extentModel : FlatModel := { numberModel with
  fields := numberModel.fields ++ [
    { id := 6, name := "A", groupPath := ["Form", "Rows", "Pair"], repeatableScope := [10]
      policy := { kind := .number { scale := 0, signed := false } } },
    { id := 7, name := "B", groupPath := ["Form", "Rows", "Pair"], repeatableScope := [10]
      policy := { kind := .number { scale := 0, signed := false } } },
    { id := 8, name := "Value", groupPath := ["Form", "Allowed"]
      policy := { kind := .number { scale := 0, signed := false } } }] }
private def extentRun (filter selected : String) (fixture : FlatModel := extentModel)
    (overflow : Bool := false) :=
  let row (n tag a b : String) := Json.mkObj [("N", .str n), ("Tag", .str tag),
    ("Pair", Json.mkObj [("A", .str a), ("B", .str b)])]
  let rows := #[row "2" "8" "8" "9", row "5" "9" "9" "9", row "7" "8" "8" "8"]
  HavingFixture.runModel fixture (filter ++ " And FieldFilled(Rows/N)") false "8" "" ""
    (ruleExpected := selected) (extra := [("Allowed", Json.mkObj [("Value", .str "8")])])
    (rowsOverride := some (if overflow then rows.push (row "11" "bad" "bad" "bad") else rows))
example : ["NumberOfFilledFields(Rows/Pair) == 2", "NumberOfFilledFields($Allowed) == 1",
    "NumberOfFilledFields(Rows*/Pair) == 6", "NumberOfFilledFields(Rows*/Pair/A) == 3"].all
      (fun filter => extentRun filter "14" == some (.fired .omission, ["value 14"])) = true ∧
    extentRun "NumberOfValueInFields(8 In Rows/Pair) == 1" "2" = some (.fired .omission, ["value 2"]) ∧
    extentRun "NumberOfValueInFields(8 In Rows/Pair,$Expected) == 2" "2" = some (.fired .omission, ["value 2"]) ∧
    ["NumberOfValueInFields(8 In Rows*/Pair) == 3", "NumberOfValueInFields(8 In Rows*/Pair/A) == 2",
      "NumberOfValueInFields(8 In $Allowed) == 1"].all
      (fun filter => extentRun filter "14" == some (.fired .omission, ["value 14"])) = true ∧
    extentRun "NumberOfFilledFields(Rows*/Pair) == 6" "14" (overflow := true) =
      some (.fired .omission, ["value 14"]) := by native_decide

private def tokenExtentModel : FlatModel := { extentModel with
  fields := extentModel.fields.map fun field => if field.id >= 6 then
    { field with policy := { kind := .string } } else field }
example : extentRun "NumberOfValueInFields(\"8\" In Rows/Pair) == 1" "2" tokenExtentModel =
      some (.fired .omission, ["value 2"]) ∧
    ["NumberOfValueInFields(\"8\" In Rows*/Pair) == 3", "NumberOfValueInFields(\"8\" In $Allowed) == 1",
      "NumberOfDifferentValues(Rows*/Pair) == 2"].all (fun filter =>
      extentRun filter "14" tokenExtentModel == some (.fired .omission, ["value 14"])) = true := by native_decide

private def tokenModel (mixed : Bool := false) : FlatModel := { HavingFixture.model with
  fields := HavingFixture.model.fields.map fun field => if field.id == 3 || (!mixed && field.id == 2) then
    { field with policy := { kind := .enumeration }, enumeration := some {
      storedTokens := ["keep", "drop"], categories := [{ name := "Label", tokens := ["K", "D"] }] } } else field }
private def accepted (filter : String) (fixture : FlatModel := numberModel) : Bool :=
  ((parseText .english ("Sum(Rows*/N Having " ++ filter ++ ") > 0")).toOption.bind fun parsed =>
    (lowerCondition fixture ["Form"] false parsed.body).toOption).isSome
example : [false, true].all (fun mixed =>
    ["NumberOfValueInFields(\"keep\" In Rows/Tag,$Expected) == 2",
      "NumberOfDifferentValues(Rows/Tag,$Expected) == 1"].all fun filter =>
        HavingFixture.runModel (tokenModel mixed) filter false "keep" "keep" "drop" ==
          some (.fired .omission, ["value 9"])) = true ∧
    accepted "NumberOfValueInFields(\"other\" In Rows/Tag,$Expected) == 0" (tokenModel) = false ∧
    HavingFixture.runModel HavingFixture.model "NumberOfValueInFields(\"other\" In Rows/Tag,$Expected) == 0" false
      "keep" "keep" "drop" (ruleExpected := "14") = some (.fired .omission, ["value 14"]) ∧
    accepted "NumberOfDifferentValues(Rows/Tag -> Label,$Expected) == 1" (tokenModel) = false := by native_decide

private def booleanModel (confirm : Bool := false) (mixed : Bool := false) : FlatModel := { HavingFixture.model with
  fields := HavingFixture.model.fields.map fun field => if field.id == 2 || field.id == 3 then
    { field with policy := { kind := if confirm && (!mixed || field.id == 2) then .confirm else .boolean } } else field }
example : [booleanModel, booleanModel true true].all (fun fixture =>
    HavingFixture.runModel fixture "NumberOfValueInFields(True In Rows/Tag,$Expected) == 2" false
      "true" "true" "false" == some (.fired .omission, ["value 9"])) = true ∧
    HavingFixture.runModel (booleanModel true) "NumberOfValueInFields(True In Rows/Tag,$Expected) == 2" false
      "true" "true" "" = some (.fired .omission, ["value 9"]) ∧
    HavingFixture.runModel (booleanModel) "NumberOfValueInFields(False In Rows/Tag,$Expected) == 1" false
      "true" "true" "false" (ruleExpected := "5") = some (.fired .omission, ["value 5"]) ∧
    HavingFixture.runModel (booleanModel) "NumberOfFilledFields(Rows/Tag,Rows/N) == 2" false
      "true" "true" "false" (ruleExpected := "14") = some (.fired .omission, ["value 14"]) ∧
    accepted "NumberOfValueInFields(False In Rows/Tag,$Expected) == 0" (booleanModel true) = false ∧
    accepted "NumberOfValueInFields(True In Rows/Tag,$Expected) == 2" HavingFixture.model = false ∧
    accepted "NumberOfDifferentValues(Rows/Tag,$Expected) == 1" (booleanModel) = false := by native_decide

private def temporalModel (rowFormat outerFormat : String) (baseYear : Option Int := none)
    (rowKind : TemporalKind := .date) (outerKind : TemporalKind := .date) : FlatModel := { dateModel with
  baseYear, timeZoneId := "UTC"
  fields := dateModel.fields.map fun field => if field.id == 2 || field.id == 3 then
    let format := if field.id == 2 then outerFormat else rowFormat
    { field with
      policy := { kind := .temporal (if field.id == 2 then outerKind else rowKind) (TemporalComponents.ofFormat format) }
      temporalTargetPolicy := some { format } } else field }
private def temporalRun (fixture : FlatModel) (outer first second : String)
    (filter : String := "NumberOfDifferentValues(Rows/Tag,$Expected) == 1") :=
  HavingFixture.runModel fixture filter false outer first second
example : temporalRun (temporalModel "yyyy-MM-dd" "dd.MM.yyyy") "01.03.2024" "2024-03-01" "2024-03-02" =
      some (.fired .omission, ["value 9"]) ∧
    temporalRun (temporalModel "HH:mm:ss" "HH:mm:ss" (rowKind := .time) (outerKind := .dateTime))
      "08:30:00" "08:30:00" "08:31:00" = some (.fired .omission, ["value 9"]) ∧
    temporalRun (temporalModel "yyyy-MM-dd'T'HH:mm:ss" "yyyy-MM-dd'T'HH:mm:ss" (rowKind := .dateTime) (outerKind := .dateTime))
      "2024-03-01T08:30:00" "2024-03-01T08:30:00" "2024-03-01T08:31:00" = some (.fired .omission, ["value 9"]) ∧
    temporalRun (temporalModel "yyyy-MM" "yyyyMM") "202403" "2024-03" "2024-04" =
      some (.fired .omission, ["value 9"]) ∧
    temporalRun (temporalModel "MM-dd" "dd.MM.") "01.03." "03-01" "03-02" =
      some (.fired .omission, ["value 9"]) := by native_decide

example : ["NumberOfDifferentValues(Rows/Tag,$Expected) == 1", "NumberOfDifferentValues($Expected,Rows/Tag) == 1"].all
    (fun filter => temporalRun (temporalModel "MM" "yyyy-MM" (some 2024)) "2024-03" "03" "04" filter ==
      some (.fired .omission, ["value 9"]) &&
      temporalRun (temporalModel "MM-dd" "yyyy-MM-dd" (some 2024)) "2024-03-01" "03-01" "03-02" filter ==
        some (.fired .omission, ["value 9"])) = true ∧
    accepted "NumberOfDifferentValues(Rows/Tag,$Expected) == 1" (temporalModel "MM" "yyyy-MM") = false ∧
    accepted "NumberOfDifferentValues(Rows/Tag,$Expected) == 1" (temporalModel "MM-dd" "yyyy-MM" (some 2024)) = false ∧
    accepted "NumberOfDifferentValues(Rows/Tag,$Expected) == 1" (temporalModel "HH:mm" "HH:mm:ss" (rowKind := .time) (outerKind := .time)) = false ∧
    accepted "NumberOfDifferentValues(Rows/Tag,$Expected) == 1" { dateModel with
      fields := dateModel.fields.map fun field => if field.id == 3 then { field with
        temporalTargetPolicy := some { format := "yyyy-MM-dd", partialMode := .dayOptional } } else field } = false := by native_decide

example : ["NumberOfFilledGroups(Rows/Pair,$Allowed) == 2",
    "NumberOfFilledGroups(Rows*/Pair) == 3",
    "NumberOfFilledGroups(Rows*,Rows*) == 6"].all (fun filter =>
      extentRun filter "14" == some (.fired .omission, ["value 14"])) = true ∧
    extentRun "NumberOfFilledGroups(Rows*) == 3" "14" (overflow := true) =
      some (.fired .omission, ["value 14"]) ∧
    ["NumberOfFilledGroups(Rows) == 1", "NumberOfFilledGroups(Rows,Rows) == 2",
      "NumberOfFilledGroups(Rows,Rows/Pair) == 2", "NumberOfFilledGroups(/Form,Rows) == 2"].all
      (fun filter => !accepted filter extentModel) = true := by native_decide

example : HavingFixture.runModel (tokenModel)
    "NumberOfValueInFields(\"K\" In Rows/Tag -> Label,$Expected -> Label) == 2" false
    "keep" "keep" "drop" = some (.fired .omission, ["value 9"]) ∧
    HavingFixture.runModel (tokenModel)
      "NumberOfValueInFields(\"K\" In Rows*/Tag -> Label) == 2 And FieldFilled(Rows/N)" false
      "keep" "keep" "drop" (ruleExpected := "14") = some (.fired .omission, ["value 14"]) := by native_decide

example : ["NumberOfValueInFields(\"keep\" In Rows*/Tag -> Label) == 0",
    "NumberOfValueInFields(\"K\" In Rows/Tag -> Label,Rows/Tag -> Label) == 2",
    "NumberOfFilledFields(Rows*/Tag -> Label) == 3",
    "NumberOfDifferentValues(Rows*/Tag -> Label) == 2",
    "NumberOfValueInFields(\"K\" In Rows*/Tag -> Missing) == 2"].all
    (fun filter => !accepted filter tokenModel) = true := by native_decide

private def fieldlessModel : FlatModel := { extentModel with
  repeatableGroups := extentModel.repeatableGroups ++ [
    { level := 20, path := ["Form", "Rows", "Empty", "Nested"], repeatability := some 2 }] }
example : ["NumberOfFilledGroups(Rows*/Empty) == 0 And FieldFilled(Rows/N)",
    "NumberOfFilledGroups(Rows*/Empty/Nested*) == 0 And FieldFilled(Rows/N)"].all
    (fun filter => !accepted filter fieldlessModel) = true := by native_decide

private def phaseGroupRows : Array Json :=
  [("2", "3"), ("5", ""), ("7", "bad")].toArray.map fun (n, value) => Json.mkObj [
    ("N", .str n), ("Pair", Json.mkObj [("A", .str value), ("B", .str "")])]
example : HavingFixture.runModel extentModel "NumberOfFilledGroups(Rows/Pair,$Allowed) == 2" false
    "8" "" "" (ruleExpected := "2") (extra := [("Allowed", Json.mkObj [("Value", .str "8")])])
    (rowsOverride := some phaseGroupRows) = some (.fired .omission, ["value 9"]) := by native_decide

example : ["SumOfProducts(Rows*/N,Rows*/N) == 78",
    "SumOfProducts(Rows*/N,$Rows*/N) == 78",
    "SumOfProducts(Rows*/Pair/A,Rows*/Pair/B) == 217"].all (fun filter =>
      extentRun filter "14" == some (.fired .omission, ["value 14"])) = true ∧
    ["SumOfProducts(Rows/Tag,Rows/N) == 16", "SumOfProducts(Rows*/N) == 78",
      "SumOfProducts(Rows*/N,Rows*/Pair/A) == 0",
      "SumOfProducts(Rows*/Tag -> Label,Rows*/N) == 0"].all
      (fun filter => !accepted filter extentModel) = true := by native_decide

private def temporalExtentModel : FlatModel := { extentModel with
  fields := extentModel.fields.map fun field => if field.id == 6 || field.id == 7 || field.id == 8 then
    { field with
      policy := { kind := .temporal .date .fullDate }
      temporalTargetPolicy := some { format := "yyyy-MM-dd" } } else field }
private def temporalExtentRows : Array Json :=
  [("2", "2024-03-01"), ("5", "2024-03-02"), ("7", "2024-03-01")].toArray.map fun (n, date) =>
    Json.mkObj [("N", .str n), ("Pair", Json.mkObj [("A", .str date), ("B", .str "2024-03-01")])]
example : (["NumberOfDifferentValues(Rows/Pair) == 1", "NumberOfDifferentValues(Rows*/Pair) == 2",
    "NumberOfDifferentValues(Rows*/Pair/A,$Allowed) == 2"].zip ["9", "14", "14"] |>.all
    (fun (filter, selected) => HavingFixture.runModel temporalExtentModel (filter ++ " And FieldFilled(Rows/N)") false
      "8" "" "" (ruleExpected := selected)
      (extra := [("Allowed", Json.mkObj [("Value", .str "2024-03-01")])])
      (rowsOverride := some temporalExtentRows) == some (.fired .omission, ["value " ++ selected]))) = true := by native_decide

example : ["01.03.2024", "08:30:00", "01.03.", "01.03.2024T08:30:00"].all
    (fun value => HavingFixture.run
      ("NumberOfValueInFields(\"" ++ value ++ "\" In Rows/Tag,$Expected) == 2")
      (expected := value) (first := value) (second := "drop") == none) = true := by native_decide

example : ["keep", "2024-03-01", "32.01.2024", "29.02.2023", "29.02."].all
    (fun value => HavingFixture.run
      ("NumberOfValueInFields(\"" ++ value ++ "\" In Rows/Tag,$Expected) == 2")
      (expected := value) (first := value) (second := "drop") ==
        some (.fired .omission, ["value 9"])) = true := by native_decide

example : ["01.03.2024", "08:30:00", "01.03.", "01.03.2024T08:30:00"].all
    (fun value => HavingFixture.runModel HavingFixture.model "" false value value "drop"
      (operationOverride := some ("NumberOfValueInFields(\"" ++ value ++ "\" In Expected,Rows*/Tag)"))
      (ruleExpected := "3") == none) = true := by native_decide

example : ["keep", "2024-03-01", "32.01.2024", "29.02.2023", "29.02."].all
    (fun value => HavingFixture.runModel HavingFixture.model "" false value value "drop"
      (operationOverride := some ("NumberOfValueInFields(\"" ++ value ++ "\" In Expected,Rows*/Tag)"))
      (ruleExpected := "3") == some (.fired .value, ["value 3"])) = true := by native_decide

private def ordinaryTokenAdmission (value : String) : Bool × Bool :=
  let operation := "NumberOfValueInFields(\"" ++ value ++ "\" In Expected,Rows*/Tag)"
  let validation := ((parseText .english (operation ++ " == 3")).toOption.bind fun parsed =>
    (lowerCondition HavingFixture.model ["Form"] false parsed.body).toOption).isSome
  let computation := (lowerComputation HavingFixture.model .english {
    group := ["Form"], name := "Count", targetRelPath := "../Out", commonPrecondition := none
    alternatives := [{ precondition := none, operation }], errorCodesToSuppress := [] }).isOk
  (validation, computation)
example : ["01.03.2024", "08:30:00", "01.03.", "01.03.2024T08:30:00"].all
    (fun value => ordinaryTokenAdmission value == (false, false)) = true ∧
    ["keep", "2024-03-01", "32.01.2024", "29.02.2023", "29.02."].all
    (fun value => ordinaryTokenAdmission value == (true, true)) = true := by native_decide

end A12Kernel.Dm.HavingCollectionCountLocks
