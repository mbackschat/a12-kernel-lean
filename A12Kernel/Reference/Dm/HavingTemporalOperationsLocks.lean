import A12Kernel.Reference.Dm.HavingFixture

namespace A12Kernel.Dm.HavingTemporalOperationsLocks
open Lean A12Kernel

private def model (format : String := "yyyy-MM-dd") (partialMode : TemporalPartialMode := .full) : FlatModel := {
  HavingFixture.model with
  baseYear := some 2024
  fields := HavingFixture.model.fields.map fun field =>
    if field.id == 2 || field.id == 3 then
      { field with
        policy := { kind := .temporal (if format == "yyyy-MM-dd" then .date else .dateTime) (TemporalComponents.ofFormat format) }
        temporalTargetPolicy := some { format, partialMode } }
    else field }

private def ordinary (fixture : FlatModel) (predicate : String) : Bool × Bool :=
  let predicate := predicate.replace "Rows/" "/Form/Rows/"
  let dm : DmModel := { flat := fixture, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  ((checkRule dm .english {
    group := ["Form", "Rows"], name := "Temporal", errorCode := "TEMPORAL", errorEntityRelPath := "../Tag"
    condition := "FieldFilled(/Form/Rows/Tag) And " ++ predicate, severity := "ERROR" }).isOk,
   (lowerComputation fixture .english {
    group := ["Form", "Rows"], name := "Temporal", targetRelPath := "../N", commonPrecondition := none
    alternatives := [{ precondition := some predicate, operation := "1" }], errorCodesToSuppress := [] }).isOk)

private def run (fixture : FlatModel) (predicate first second : String) (selected : String := "9") :=
  HavingFixture.runModel fixture predicate false first first second (ruleExpected := selected)
    (zoneRules := ModelZone.concreteRules)

private def dates : List String := [
  "AddDays(Rows/Tag,1) == \"29.02.2024\"",
  "AddMonths(Rows/Tag,1) == \"28.03.2024\"",
  "AddYears(Rows/Tag,1) == \"28.02.2025\"",
  "DayFromDate(AddDays(Rows/Tag,1)) == 29",
  "AddDays(Rows/Tag,DayFromDate(Date(\"01\",\"01\",\"2024\"))) == \"29.02.2024\"",
  "DifferenceInDays(Date(\"28\",\"02\",\"2024\"),AddDays(Rows/Tag,1)) == 1",
  "DifferenceInMonths(Date(\"28\",\"02\",\"2024\"),AddMonths(Rows/Tag,1)) == 1",
  "DifferenceInYears(Date(\"28\",\"02\",\"2024\"),AddYears(Rows/Tag,1)) == 1"]

private def widerAmounts : List String := [
  "AddDays(Rows/Tag,BaseYear-2023) == \"29.02.2024\"",
  "AddDays(Rows/Tag,DifferenceInDays(\"01.01.2024\",Date(\"02\",\"01\",\"2024\"))) == \"29.02.2024\""]

example : widerAmounts.all (fun predicate =>
    run (model) predicate "2024-02-28" "2024-02-27" == some (.fired .omission, ["value 9"])) = true := by native_decide

example : widerAmounts.all (fun predicate => ordinary (model) predicate == (true, true)) = true := by native_decide

private def stamps : List String := [
  "AddHours(Rows/Tag,1) == \"28.02.2024T09:00:00\"",
  "AddMinutes(Rows/Tag,1) == \"28.02.2024T08:01:00\"",
  "AddSeconds(Rows/Tag,1) == \"28.02.2024T08:00:01\"",
  "HoursFromTime(AddHours(Rows/Tag,1)) == 9",
  "DifferenceInHours(DateTime(\"28.02.2024\",Time(\"08\")),AddHours(Rows/Tag,1)) == 1",
  "DifferenceInMinutes(DateTime(\"28.02.2024\",Time(\"08\")),AddMinutes(Rows/Tag,1)) == 1",
  "DifferenceInSeconds(DateTime(\"28.02.2024\",Time(\"08\")),AddSeconds(Rows/Tag,1)) == 1"]

private def partialDates : List String := [
  "ValueAsDate(Rows/Tag,FirstDay) == \"01.02.2024\"",
  "ValueAsDate(Rows/Tag,LastDay) == \"29.02.2024\"",
  "AddDays(ValueAsDate(Rows/Tag,FirstDay),1) == \"02.02.2024\"",
  "DifferenceInDays(ValueAsDate(Rows/Tag,FirstDay),ValueAsDate(Rows/Tag,LastDay)) == 28"]

example : ["MonthFromDate(Rows/Tag) == 2", "QuarterFromDate(Rows/Tag) == 1",
    "YearFromDate(Rows/Tag) == 2024"].all (fun predicate =>
      run (model) predicate "2024-02-28" "2025-05-01" ==
        some (.fired .omission, ["value 9"])) = true := by native_decide

example : ["MonthFromDate(Rows/Tag) == 2", "QuarterFromDate(Rows/Tag) == 1",
    "YearFromDate(Rows/Tag) == 2024",
    "MonthFromDate(Rows/Tag) == MonthFromDate($Expected)"].all (fun predicate =>
      run (model "yyyy-MM-dd" .dayOptional) predicate "2024-02-00" "2025-05-00" ==
        some (.fired .omission, ["value 9"])) = true ∧
    run (model "yyyy-MM-dd" .monthOptional) "YearFromDate(Rows/Tag) == 2024"
      "2024-00-00" "2025-00-00" == some (.fired .omission, ["value 9"]) := by native_decide

example : dates.all (fun predicate => ordinary (model) predicate == (true, true)) = true ∧
    stamps.all (fun predicate => ordinary (model "yyyy-MM-dd'T'HH:mm:ss") predicate == (true, true)) = true ∧
    partialDates.all (fun predicate => ordinary (model "yyyy-MM-dd" .yearOptional) predicate == (true, true)) = true := by native_decide

example : (dates.take 5).all (fun predicate => run (model) predicate "2024-02-28" "2024-02-27" ==
    some (.fired .omission, ["value 9"])) = true := by native_decide

example : (stamps.take 4).all (fun predicate => run (model "yyyy-MM-dd'T'HH:mm:ss") predicate
    "2024-02-28T08:00:00" "2024-02-28T09:00:00" == some (.fired .omission, ["value 9"])) = true := by native_decide

example : (partialDates.take 3).all (fun predicate => run (model "yyyy-MM-dd" .yearOptional) predicate
    "2024-02-00" "2024-03-00" == some (.fired .omission, ["value 9"])) = true := by native_decide

example : (dates.drop 5).all (fun predicate => run (model) predicate "2024-02-28" "2024-02-27" ==
    some (.fired .omission, ["value 9"])) = true ∧
    (stamps.drop 4).all (fun predicate => run (model "yyyy-MM-dd'T'HH:mm:ss") predicate
      "2024-02-28T08:00:00" "2024-02-28T09:00:00" == some (.fired .omission, ["value 9"])) = true ∧
    (partialDates.drop 3).all (fun predicate => run (model "yyyy-MM-dd" .yearOptional) predicate
      "2024-02-00" "2024-03-00" == some (.fired .omission, ["value 9"])) = true := by native_decide

example : ["UTC", "GMT", "Europe/Berlin"].all (fun zone =>
    run { model with timeZoneId := zone } "AddDays(Rows/Tag,[Rows/N]) == \"01.03.2024\""
      "2024-02-28" "2024-02-27" "2" == some (.fired .omission, ["value 2"])) = true ∧
    run { model "yyyy-MM-dd'T'HH:mm:ss" with timeZoneId := "Europe/Berlin" }
      "AddDays(Rows/Tag,1) == \"31.03.2024T12:00:00\"" "2024-03-30T12:00:00" "2024-03-30T11:00:00" =
      some (.fired .omission, ["value 9"]) ∧
    run { model "yyyy-MM-dd'T'HH:mm:ss" with timeZoneId := "Europe/Berlin" }
      "AddHours(Rows/Tag,24) == \"31.03.2024T13:00:00\"" "2024-03-30T12:00:00" "2024-03-30T11:00:00" =
      some (.fired .omission, ["value 9"]) := by native_decide

example : ["AddDays([Rows/Tag],1)", "AddDays({Rows/Tag},1)", "AddDays(FirstFilledValue(Rows/Tag),1)"].all
      (fun source => HavingFixture.admissions model (source ++ " == \"01.02.2024\"") == (false, false)) = true ∧
    HavingFixture.admissions model "AddHours(Time(\"08\"),1) == \"28.02.2024T09:00:00\"" = (false, false) ∧
    HavingFixture.admissions (model "yyyy-MM-dd" .yearOptional) "YearFromDate(ValueAsDate(Rows/Tag,FirstDay)) == 2024" = (false, false) ∧
    HavingFixture.admissions model "ValueAsDate(Rows/Tag,FirstDay) == \"01.02.2024\"" = (false, false) := by native_decide

private def ordinaryRun (fixture : FlatModel) (predicate first : String) :=
  let predicate := predicate.replace "Rows/Tag" "Expected"
  let operation := (predicate.splitOn " == ").head!
  HavingFixture.runModel fixture "" false first first first (operationOverride := some operation)
    (ruleCondition := some ("FieldFilled(Error) And " ++ predicate)) (zoneRules := ModelZone.concreteRules)

example : (dates.drop 5).all (fun predicate => ordinaryRun model predicate "2024-02-28" ==
    some (.fired .value, ["value 1"])) = true ∧
    (stamps.drop 4).all (fun predicate => ordinaryRun (model "yyyy-MM-dd'T'HH:mm:ss") predicate
      "2024-02-28T08:00:00" == some (.fired .value, ["value 1"])) = true ∧
    ordinaryRun (model "yyyy-MM-dd" .yearOptional) partialDates[3]! "2024-02-00" =
      some (.fired .value, ["value 28"]) := by native_decide

private def pointerModel : FlatModel := { model with fields := model.fields ++ [{
  id := 6, name := "Token", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .string } }] }
example : HavingFixture.referencesFor
      "DifferenceInDays(AddDays(/Form/Rows/Tag,1),AddDays($/Form/Rows/Tag,1)) == 0" pointerModel "Token" = some (true, true) ∧
    HavingFixture.referencesFor
      "AddDays(/Form/Rows/Tag,DayFromDate($/Form/Rows/Tag)) == \"01.03.2024\"" pointerModel "Token" = some (true, true) ∧
    HavingFixture.runModel model "DifferenceInDays(AddDays(Rows/Tag,1),$Expected) == 0" true
      "2024-02-29" "2024-02-28" "2024-02-27" "\"28.02.2024\"" (zoneRules := ModelZone.concreteRules) =
      some (.fired .omission, ["value 2024-02-28", "value 5"]) := by native_decide

example : ["UTC", "GMT", "Europe/Berlin"].all (fun zone =>
    run { model with timeZoneId := zone }
      "DifferenceInDays(AddDays(Rows/Tag,1),Date(\"28\",\"02\",\"2024\")) == -1"
      "2024-02-28" "2024-02-27" == some (.fired .omission, ["value 9"])) = true ∧
    run { model "yyyy-MM-dd'T'HH:mm:ss" with timeZoneId := "Europe/Berlin" }
      "DifferenceInDays(AddHours(Rows/Tag,0),\"31.03.2024T01:45:00\") == 1"
      "2024-03-30T02:30:00" "2024-03-30T04:30:00" = some (.fired .omission, ["value 9"]) ∧
    run { model "yyyy-MM-dd'T'HH:mm:ss" with timeZoneId := "Europe/Berlin" }
      "DifferenceInHours(AddHours(Rows/Tag,0),\"31.03.2024T12:00:00\") == 23"
      "2024-03-30T12:00:00" "2024-03-30T11:00:00" = some (.fired .omission, ["value 9"]) := by native_decide

end A12Kernel.Dm.HavingTemporalOperationsLocks
