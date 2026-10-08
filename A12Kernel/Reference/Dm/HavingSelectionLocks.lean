import A12Kernel.Reference.Dm.HavingFixture

namespace A12Kernel.Dm.HavingSelectionLocks
open Lean A12Kernel

private def numberModel : FlatModel := { HavingFixture.model with
  fields := HavingFixture.model.fields.map fun field => if field.id == 2 || field.id == 3 then
    { field with policy := { kind := .number { scale := 0, signed := false } } } else field }

example : HavingFixture.runModel numberModel "FirstFilledValue(Rows/Tag,$Expected) == 8" false
    "8" "8" "9" = some (.fired .omission, ["value 9"]) ∧
    HavingFixture.runModel numberModel "FirstFilledValue(Rows/Tag,$Expected) + 1 == 9" false
      "8" "" "9" = some (.fired .omission, ["value 9"]) ∧
    HavingFixture.runModel numberModel
      "FirstFilledValue(Rows*/Tag,$Expected) == 8 And FieldFilled(Rows/N)" false
      "8" "8" "9" (ruleExpected := "14") = some (.fired .omission, ["value 14"]) := by native_decide

private def timeModel : FlatModel := { HavingFixture.model with
  fields := HavingFixture.model.fields.map fun field => if field.id == 2 || field.id == 3 then
    { field with
      policy := { kind := .temporal .time TemporalComponents.time }
      temporalTargetPolicy := some { format := "HH:mm:ss" } } else field }

example : ["FirstFilledValue", "MinValue", "MaxValue"].all (fun operator =>
    HavingFixture.runModel timeModel (operator ++ "(Rows/Tag,$Expected) == \"12:30:00\"") false
      "12:30:00" "12:30:00" "12:30:00" (ruleExpected := "14") == some (.fired .omission, ["value 14"]) &&
    HavingFixture.admissions timeModel ("HoursFromTime(" ++ operator ++ "(Rows/Tag,$Expected)) == 12") == (false, false)) = true := by native_decide

private def run (filter selected : String) (fixture : FlatModel := timeModel)
    (outer : String := "12:30:00") (first : String := "11:30:00") (second : String := "12:30:00")
    (fresh : Bool := false) (producer : String := "\"11:30:00\"") :=
  HavingFixture.runModel fixture filter fresh outer first second producer (ruleExpected := selected)
private def selections := [("FirstFilledValue", "5"), ("MinValue", "5"), ("MaxValue", "14")]
example : selections.all (fun (operator, selected) => [false, true].all fun reverse =>
    let source := operator ++ "(Rows/Tag,$Expected)"
    let filter := if reverse then "\"12:30:00\" == " ++ source else source ++ " == \"12:30:00\""
    run filter selected == some (.fired .omission, ["value " ++ selected])) = true ∧
    run "FirstFilledValue(Rows/Tag,$Expected) == MaxValue(Rows/Tag,$Expected)" "5" =
      some (.fired .omission, ["value 5"]) ∧
    run "MinValue(Rows/Tag,$Expected) == FirstFilledValue(Rows/Tag,$Expected)" "14" =
      some (.fired .omission, ["value 14"]) ∧
    run "MaxValue(Rows/Tag,$Expected) == MinValue(Rows/Tag,$Expected)" "5" =
      some (.fired .omission, ["value 5"]) := by native_decide

example : selections.all (fun (operator, _) =>
    run (operator ++ "(Rows/Tag,$Expected) == \"12:30:00\"") "14" (first := "") ==
      some (.fired .omission, ["value 14"]) &&
    run (operator ++ "(Rows/Tag,$Expected) == \"12:30:00\"") "5" (first := "bad") ==
      some (.fired .omission, []) &&
    run (operator ++ "(Rows/Tag,$Expected) == \"12:30:00\"") "0" (outer := "") (first := "") (second := "") ==
      some (.fired .omission, ["value 0"])) = true ∧
    run "FirstFilledValue(Rows/Tag,$Expected) == [Rows/Tag]" "14" (outer := "bad") =
      some (.fired .omission, ["value 14"]) ∧
    ["MinValue", "MaxValue"].all (fun operator =>
      run (operator ++ "(Rows/Tag,$Expected) == \"12:30:00\"") "0" (outer := "bad") ==
        some (.fired .omission, [])) = true := by native_decide

example : [("FirstFilledValue", "0"), ("MinValue", "0"), ("MaxValue", "14")].all (fun (operator, selected) =>
    run (operator ++ "(Rows*/Tag,$Expected) == \"12:30:00\" And FieldFilled(Rows/N)") selected ==
      some (.fired .omission, ["value " ++ selected])) = true ∧
    run "FirstFilledValue($Expected,Rows*/Tag) == \"12:30:00\" And FieldFilled(Rows/N)" "14" (first := "bad") =
      some (.fired .omission, ["value 14"]) ∧
    ["MinValue", "MaxValue"].all (fun operator =>
      run (operator ++ "($Expected,Rows*/Tag) == \"12:30:00\" And FieldFilled(Rows/N)") "0" (first := "bad") ==
        some (.fired .omission, [])) = true := by native_decide

private def temporalModel (kind : TemporalKind) (rowFormat outerFormat : String) : FlatModel := { timeModel with
  fields := timeModel.fields.map fun field => if field.id == 2 || field.id == 3 then
    let format := if field.id == 2 then outerFormat else rowFormat
    { field with
      policy := { kind := .temporal kind (TemporalComponents.ofFormat format) }
      temporalTargetPolicy := some { format } } else field }
private def dateModel := temporalModel .date "yyyy-MM-dd" "yyyy-MM-dd"
private def stampModel := temporalModel .dateTime "yyyy-MM-dd'T'HH:mm:ss" "yyyy-MM-dd'T'HH:mm:ss"
example : selections.all (fun (operator, selected) => [false, true].all fun reverse =>
    let source := operator ++ "(Rows/Tag,$Expected)"
    let dateFilter := if reverse then "\"12.04.2024\" == " ++ source else source ++ " == \"12.04.2024\""
    let stampFilter := if reverse then "\"12.04.2024T12:30:00\" == " ++ source else source ++ " == \"12.04.2024T12:30:00\""
    run dateFilter selected dateModel "2024-04-12" "2024-04-11" "2024-04-12" ==
      some (.fired .omission, ["value " ++ selected]) &&
    run stampFilter selected stampModel "2024-04-12T12:30:00" "2024-04-12T11:30:00" "2024-04-12T12:30:00" ==
      some (.fired .omission, ["value " ++ selected])) = true := by native_decide

example : run "FirstFilledValue(Rows/Tag,$Expected) == \"12:30:00\"" "14" (first := "") (fresh := true) =
      some (.fired .omission, ["value 11:30:00", "value 5"]) ∧
    run "MinValue(Rows/Tag,$Expected) == \"12:30:00\"" "5" (fresh := true) =
      some (.fired .omission, ["value 11:30:00", "value 0"]) := by native_decide

private def pointerModel : FlatModel := { timeModel with
  fields := timeModel.fields ++ [{
    id := 6, name := "Token", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .string } }] }
example : selections.all (fun (operator, _) =>
    HavingFixture.referencesFor (operator ++ "(/Form/Rows/Tag,$/Form/Rows/Tag) == \"12:30:00\"")
      pointerModel "Token" == some (true, true)) = true ∧
    HavingFixture.referencesFor "FirstFilledValue(/Form/Rows*/Tag,$/Form/Rows/Tag) == \"12:30:00\" And FieldFilled(/Form/Rows/N)"
      pointerModel "Token" = some (true, true) ∧
    HavingFixture.referencesFor "FirstFilledValue(/Form/Rows/Tag,$/Form/Expected) == \"12:30:00\""
      pointerModel "Token" = some (true, false) := by native_decide

private def mixedDateModel := temporalModel .date "dd.MM.yyyy" "yyyy-MM-dd"
example : HavingFixture.admissions dateModel "FirstFilledValue(Rows/Tag,$Expected) == \"12.04.2024\"" = (true, true) ∧
    HavingFixture.admissions mixedDateModel "FirstFilledValue(Rows/Tag,$Expected) == \"12.04.2024\"" = (false, false) ∧
    [("MinValue", "5"), ("MaxValue", "14")].all (fun (operator, selected) =>
      let filter := operator ++ "(Rows/Tag,$Expected) == \"12.04.2024\""
      HavingFixture.admissions mixedDateModel filter == (true, true) &&
        run filter selected mixedDateModel "2024-04-12" "11.04.2024" "12.04.2024" ==
          some (.fired .omission, ["value " ++ selected])) = true := by native_decide

example : [("Min", "5"), ("Max", "14")].all (fun (operator, selected) =>
    run (operator ++ "([Rows/Tag],[$Expected]) == \"12:30:00\"") selected ==
      some (.fired .omission, ["value " ++ selected]) &&
    HavingFixture.admissions timeModel
      ("HoursFromTime(" ++ operator ++ "(FirstFilledValue(Rows/Tag,$Expected),[$Expected])) == 12") == (false, false)) = true := by native_decide

example : run "Min(MinValue(Rows/Tag,$Expected),FirstFilledValue(Rows/Tag,$Expected)) == \"12:30:00\"" "5" =
      some (.fired .omission, ["value 5"]) ∧
    run "Max([Rows/Tag],[$Expected]) == \"12:30:00\"" "5" (first := "bad") =
      some (.fired .omission, []) ∧
    HavingFixture.admissions timeModel "Min([Rows/Tag],\"12:30:00\") == \"12:30:00\"" = (true, true) ∧
    HavingFixture.admissions timeModel "Min([Rows/Tag],\"12:30:00\",\"11:30:00\") == \"12:30:00\"" = (false, false) ∧
    HavingFixture.admissions timeModel "Min(\"12:30:00\",[Rows/Tag],\"11:30:00\") == \"12:30:00\"" = (false, false) ∧
    HavingFixture.admissions timeModel "Min([Rows/Tag],1) == \"12:30:00\"" = (false, false) ∧
    HavingFixture.admissions numberModel "Min([Rows/Tag],[$Expected]) == 8" = (true, true) := by native_decide

example : ["FirstFilledValue(Rows/Tag,$Expected)", "MinValue(Rows/Tag,$Expected)",
    "MaxValue(Rows/Tag,$Expected)", "Min([Rows/Tag],[$Expected])", "Max([Rows/Tag],[$Expected])"].all
    (fun source => ["DateFromDateTime", "TimeFromDateTime"].all fun operator =>
      HavingFixture.admissions stampModel (operator ++ "(" ++ source ++ ") == " ++ operator ++ "($Expected)") == (false, false)) = true := by native_decide

end A12Kernel.Dm.HavingSelectionLocks
