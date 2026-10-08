import A12Kernel.Reference.Dm.HavingFixture

namespace A12Kernel.Dm.HavingSelectionProfilesLocks
open A12Kernel

private def model (format : String) (partialMode : TemporalPartialMode := .full)
    (baseYear : Option Int := none) : FlatModel := {
  HavingFixture.model with
  baseYear
  fields := HavingFixture.model.fields.map fun field => if field.id == 2 || field.id == 3 then
    { field with
      policy := { kind := .temporal .date (TemporalComponents.ofFormat format) }
      temporalTargetPolicy := some { format, partialMode := if field.id == 3 then partialMode else .full } } else field }
private def run (fixture : FlatModel) (filter outer first second selected : String) :=
  HavingFixture.runModel fixture filter false outer first second (ruleExpected := selected)

example : [("yyyy", "2024", "2023"), ("yyyy-MM", "2024-03", "2024-02"),
    ("MM", "03", "02"), ("MM-dd", "03-12", "03-11")].all (fun (format, outer, earlier) =>
      [none, some 2024].all fun baseYear =>
        [("FirstFilledValue", "5"), ("MinValue", "5"), ("MaxValue", "14")].all fun (operator, selected) =>
          run (model format .full baseYear) (operator ++ "(Rows/Tag,$Expected) == [$Expected]")
            outer earlier outer selected == some (.fired .omission, ["value " ++ selected])) = true := by native_decide

example : [(TemporalPartialMode.dayOptional, "2024-06-00", "2024-06-01"),
    (.monthOptional, "2024-00-00", "2024-01-01"), (.monthOptional, "2024-03-00", "2024-03-01"),
    (.yearOptional, "2024-00-00", "2024-01-01")].all (fun (mode, stored, completed) =>
      [("FirstFilledValue(Rows/Tag,$Expected) == [$Expected]", "9"),
       ("[$Expected] == FirstFilledValue(Rows/Tag,$Expected)", "9"),
       ("Min(FirstFilledValue(Rows/Tag,$Expected),[$Expected]) == [$Expected]", "14")].all fun (filter, selected) =>
        run (model "yyyy-MM-dd" mode) filter completed stored "2024-12-31" selected ==
          some (.fired .omission, ["value " ++ selected])) = true := by native_decide

example : run (model "dd.MM.yyyy" .dayOptional)
      "FirstFilledValue(Rows/Tag,$Expected) == [$Expected]" "01.06.2024" "00.06.2024" "15.06.2024" "9" =
      some (.fired .omission, ["value 9"]) ∧
    run (model "yyyy-MM-dd" .yearOptional) "FirstFilledValue(Rows/Tag,$Expected) == [$Expected]"
      "2024-06-15" "0000-00-00" "2024-06-15" "5" = some (.fired .omission, ["value 5"]) ∧
    run (model "yyyy-MM-dd" .dayOptional) "FirstFilledValue(Rows/Tag,$Expected) == [$Expected]"
      "2024-06-15" "2024-00-00" "2024-06-15" "5" = some (.fired .omission, []) ∧
    HavingFixture.admissions (model "yyyy-MM-dd" .dayOptional)
      "MinValue(Rows/Tag,$Expected) == [$Expected]" = (false, false) ∧
    HavingFixture.admissions (model "yyyy-MM-dd" .dayOptional)
      "[Rows/Tag] == [$Expected]" = (false, false) := by native_decide

example : HavingFixture.admissions (model "yyyy-MM-dd" .dayOptional)
      "DateTime(FirstFilledValue(Rows/Tag,$Expected),\"12:30:00\") == \"01.06.2024T12:30:00\"" = (false, false) ∧
    HavingFixture.admissions (model "yyyy-MM-dd" .dayOptional)
      "DayFromDate(FirstFilledValue(Rows/Tag,$Expected)) == 1" = (false, false) ∧
    run (model "yyyy-MM-dd" .dayOptional)
      "FirstFilledValue(Rows*/Tag,$Expected) == [$Expected] And FieldFilled(Rows/N)"
      "2024-06-01" "2024-06-00" "2024-06-15" "14" = some (.fired .omission, ["value 14"]) := by native_decide

end A12Kernel.Dm.HavingSelectionProfilesLocks
