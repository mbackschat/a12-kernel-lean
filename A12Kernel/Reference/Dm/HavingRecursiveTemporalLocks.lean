import A12Kernel.Reference.Dm.HavingFixture

namespace A12Kernel.Dm.HavingRecursiveTemporalLocks
open Lean A12Kernel

private def model : FlatModel := {
  HavingFixture.model with
  baseYear := some 2024
  fields := (HavingFixture.model.fields.map fun field => if field.id == 2 || field.id == 3 then
    { field with
      policy := { kind := .number { scale := 0, signed := false } }
      numericTargetConstraints := { maxStoredLength := some 2 } } else field) ++ [
    { id := 6, name := "M", groupPath := ["Form", "Rows"], repeatableScope := [10]
      policy := { kind := .number { scale := 0, signed := false } }
      numericTargetConstraints := { maxStoredLength := some 2 } },
    { id := 7, name := "Y", groupPath := ["Form", "Rows"], repeatableScope := [10]
      policy := { kind := .number { scale := 0, signed := false } }
      numericTargetConstraints := { maxStoredLength := some 4 } },
    { id := 8, name := "Range", groupPath := ["Form", "Rows"], repeatableScope := [10]
      policy := { kind := .dateRange }, dateRangePolicy := some { format := "yyyy-MM-dd", separator := "/" } }] }

private def run (filter selected : String) (first : String := "29") (second : String := "28")
    (fixture : FlatModel := model) (fresh : Bool := false) (producer : String := "9") :=
  let row (tag amount range : String) := Json.mkObj [
    ("Tag", Json.str tag), ("N", Json.str amount), ("M", Json.str "02"),
    ("Y", Json.str "2024"), ("Range", Json.str range)]
  HavingFixture.runModel fixture filter fresh "8" first second producer (ruleExpected := selected)
    (zoneRules := ModelZone.concreteRules) (rowsOverride := some #[
      row first "2" "2024-02-29/2024-03-01", row second "5" "2024-02-28/2024-03-02",
      row first "7" "2024-02-29/2024-03-01"])

private def nestedDate := "Date(DayFromDate(Date(/Form/Rows/Tag,\"02\",\"2024\")),\"02\",\"2024\")"
private def nestedTime := "Time(HoursFromTime(Time(/Form/Rows/Tag)),MinutesFromTime(Time(\"0\",\"30\")),SecondsFromTime(Time(\"0\",\"0\",\"45\")))"
private def rangeDate := "Date(DayFromDate(StartOfDateRange(/Form/Rows/Range)),\"02\",\"2024\")"
private def nestedValidity := "Valid(Date(DayFromDate(Date(/Form/Rows/Tag,\"02\",\"2024\")),/Form/Rows/M,\"2024\"))"

private def ordinaryAdmitted (predicate : String) : Bool × Bool :=
  let dm : DmModel := { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  ((checkRule dm .english {
    group := ["Form", "Rows"], name := "Nested", errorCode := "NESTED", errorEntityRelPath := "../Tag"
    condition := "FieldFilled(/Form/Rows/Tag) And " ++ predicate, severity := "ERROR" }).isOk,
   (lowerComputation model .english {
    group := ["Form", "Rows"], name := "Nested", targetRelPath := "../N", commonPrecondition := none
    alternatives := [{ precondition := some predicate, operation := "1" }], errorCodesToSuppress := [] }).isOk)

example : [nestedDate ++ " == \"29.02.2024\"", nestedTime ++ " == \"08:30:45\"",
    rangeDate ++ " == \"29.02.2024\"", nestedValidity].all (fun source =>
      ordinaryAdmitted source == (true, true)) = true := by native_decide

example : run (nestedDate ++ " == \"29.02.2024\"") "9" = some (.fired .omission, ["value 9"]) ∧
    run ("\"29.02.2024\" == " ++ nestedDate) "9" = some (.fired .omission, ["value 9"]) ∧
    run (nestedTime ++ " == \"08:30:45\"") "9" "8" "9" = some (.fired .omission, ["value 9"]) ∧
    run (rangeDate ++ " == \"29.02.2024\"") "9" = some (.fired .omission, ["value 9"]) ∧
    run nestedValidity "14" = some (.fired .omission, ["value 14"]) := by native_decide

example : HavingFixture.admissions model
      "Valid(Date(DayFromDate(Date(Rows/Tag,\"02\",\"2024\")),\"02\",\"2024\"))" = (false, false) ∧
    HavingFixture.admissions model
      "Time(MinutesFromTime(Time(Rows/Tag))) == \"08:00:00\"" = (false, false) ∧
    HavingFixture.admissions model
      "Date(MonthFromDate(Date(Rows/Tag,\"02\",\"2024\")),\"02\",\"2024\") == \"29.02.2024\"" =
      (false, false) := by native_decide


private def composedDates : List String := [
  "Date(DayFromDate(Date(Rows/Tag,\"02\",\"2024\")),MonthFromDate(Date(\"01\",Rows/M,\"2024\")),YearFromDate(Date(\"01\",\"01\",Rows/Y)))",
  "Date(DayFromDate(Date(Rows/Tag,\"02\",\"2024\")),\"02\")",
  "Date(DayFromDate(Date(Rows/Tag,\"02\",\"2024\")),\"02\",\"20\",\"24\")",
  "Date(DayFromDate(DateTime(Date(Rows/Tag,Rows/M,Rows/Y),Time())),\"02\",\"2024\")",
  "Date(DayFromDate(DateFromDateTime(DateTime(Date(Rows/Tag,Rows/M,Rows/Y),Time()))),\"02\",\"2024\")"]

example : ["UTC", "GMT", "Europe/Berlin"].all (fun zone => composedDates.all fun source =>
    run (source ++ " == \"29.02.2024\"") "9" (fixture := { model with timeZoneId := zone }) ==
      some (.fired .omission, ["value 9"])) = true ∧
    run "Date(DayFromDate(EndOfDateRange(Rows/Range)),\"03\",\"2024\") == \"01.03.2024\"" "9" =
      some (.fired .omission, ["value 9"]) ∧
    run "Time(HoursFromTime(TimeFromDateTime(DateTime(\"29.02.2024\",Time(Rows/Tag))))) == \"08:00:00\"" "9" "8" "9" =
      some (.fired .omission, ["value 9"]) := by native_decide

example : run nestedValidity "5" "30" = some (.fired .omission, ["value 5"]) ∧
    run (nestedValidity.replace "Valid(" "Invalid(") "9" "30" = some (.fired .omission, ["value 9"]) ∧
    run ("DayFromDate(" ++ nestedDate ++ ") == 29") "9" = some (.fired .omission, ["value 9"]) ∧
    run ("MinutesFromTime(" ++ nestedTime ++ ") == 30") "14" "8" "9" = some (.fired .omission, ["value 14"]) := by native_decide

private def pointerModel : FlatModel := { model with fields := model.fields ++ [{
  id := 9, name := "Token", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .string } }] }

example : HavingFixture.referencesFor
      "Date(DayFromDate(Date(/Form/Rows/Tag,\"02\",\"2024\")),\"02\",\"2024\") == Date(DayFromDate(Date($/Form/Rows/Tag,\"02\",\"2024\")),\"02\",\"2024\")"
      pointerModel "Token" = some (true, true) ∧
    HavingFixture.referencesFor
      "Valid(Date(DayFromDate(Date($/Form/Rows/Tag,\"02\",\"2024\")),/Form/Rows/M,\"2024\"))"
      pointerModel "Token" = some (false, true) ∧
    run "Time(HoursFromTime(Time(Rows/Tag))) == Time(HoursFromTime(Time($Expected)))" "9" "8" "9" (fresh := true) =
      some (.fired .omission, ["value 9", "value 5"]) := by native_decide

example : [
    "Date(DayFromDate(FirstFilledValue(Rows/Range)),\"02\",\"2024\") == \"29.02.2024\"",
    "Date(DayFromDate({Date(Rows/Tag,\"02\",\"2024\")}),\"02\",\"2024\") == \"29.02.2024\"",
    "Date(\"29\",\"02\",\"20\",YearFromDate(Date(\"01\",\"01\",Rows/Y))) == \"29.02.2024\"",
    "Date(\"29\",\"02\",MonthFromDate(Date(\"01\",Rows/M,\"2024\"))) == \"29.02.2024\"",
    "Time(HoursFromTime(\"08:00:00\")) == Time(Rows/Tag)",
    "Time(HoursFromTime(Min(Time(Rows/Tag),\"08:00:00\"))) == \"08:00:00\"",
    "Invalid(Date(DayFromDate(Date(Rows/Tag,\"02\",\"2024\")),\"02\",\"2024\"))"].all
      (fun filter => HavingFixture.admissions model filter == (false, false)) = true := by native_decide


private def anchoredTimeYears := [
  "YearFromDate(Time(/Form/Rows/Tag))",
  "YearFromDate(TimeFromDateTime(DateTime(Date(/Form/Rows/Tag,\"02\",\"2024\"),Time())))"]

example : anchoredTimeYears.all (fun source => ordinaryAdmitted (source ++ " == 1970") == (true, true)) = true := by native_decide

example : anchoredTimeYears.all (fun source => run (source ++ " == 1970") "14" "8" "9" ==
      some (.fired .omission, ["value 14"])) = true := by native_decide

example : anchoredTimeYears.all (fun source => run ("Date(\"01\",\"01\"," ++ source ++ ") == \"01.01.1970\"") "14" "8" "9" ==
      some (.fired .omission, ["value 14"])) = true := by native_decide

example : anchoredTimeYears.all (fun source => HavingFixture.admissions { model with baseYear := none }
      (source ++ " == 1970") == (false, false)) = true := by native_decide

example : anchoredTimeYears.all (fun source =>
    let operation := source.replace "/Form/Rows/Tag" "Expected"
    HavingFixture.runModel model "" false "8" "8" "9"
      (operationOverride := some operation)
      (ruleCondition := some ("FieldFilled(Error) And " ++ operation ++ " == 1970"))
      (zoneRules := ModelZone.concreteRules) == some (.fired .value, ["value 1970"])) = true := by native_decide

end A12Kernel.Dm.HavingRecursiveTemporalLocks
