import A12Kernel.Reference.Dm.HavingFixture

namespace A12Kernel.Dm.HavingRangeEndpointLocks
open Lean A12Kernel

private def model : FlatModel := { HavingFixture.model with
  fields := HavingFixture.model.fields.map fun field =>
    if field.id == 2 || field.id == 3 then { field with
      policy := { kind := .dateRange }
      dateRangePolicy := some { format := "yyyy-MM-dd", separator := "/" } } else field }

private def run (filter : String) (selected : String := "5")
    (outer : String := "2024-04-12/2024-04-15")
    (first : String := "2024-04-11/2024-04-14")
    (second : String := "2024-04-12/2024-04-15")
    (fixture : FlatModel := model) (clock : Instant := { epochMillis := 0 }) :=
  HavingFixture.runModel fixture filter false outer first second (ruleExpected := selected) (clock := clock)

example : run "StartOfDateRange(Rows/Tag) == StartOfDateRange($Expected)" =
    some (.fired .omission, ["value 5"]) := by native_decide

private def bounds := ["StartOfDateRange", "EndOfDateRange"]
example : bounds.all (fun bound =>
    [false, true].all fun reverse =>
      let inner := bound ++ "(Rows/Tag)"
      let outer := bound ++ "($Expected)"
      let equal := if reverse then outer ++ " == " ++ inner else inner ++ " == " ++ outer
      let ordered := if reverse then outer ++ " > " ++ inner else inner ++ " < " ++ outer
      run equal == some (.fired .omission, ["value 5"]) &&
        run ordered "9" == some (.fired .omission, ["value 9"])) = true ∧
    run "StartOfDateRange(Rows/Tag) < EndOfDateRange(Rows/Tag)" "14" =
      some (.fired .omission, ["value 14"]) := by native_decide

example : [("StartOfDateRange", "12.04.2024"), ("EndOfDateRange", "15.04.2024")].all
    (fun (bound, literal) => [false, true].all fun reverse =>
      let source := bound ++ "(Rows/Tag)"
      let constant := "\"" ++ literal ++ "\""
      run (if reverse then constant ++ " == " ++ source else source ++ " == " ++ constant) ==
        some (.fired .omission, ["value 5"])) = true := by native_decide

example : bounds.all (fun bound =>
    run ("DateTime(" ++ bound ++ "(Rows/Tag),\"12:30:00\") == DateTime(" ++ bound ++ "($Expected),\"12:30:00\")") ==
      some (.fired .omission, ["value 5"]) &&
    run ("HoursFromTime(TimeFromDateTime(DateTime(" ++ bound ++ "(Rows/Tag),\"12:30:00\"))) + [Rows/N] == 17") ==
      some (.fired .omission, ["value 5"])) = true ∧
    run "DayFromDate(DateFromDateTime(DateTime(EndOfDateRange(Rows/Tag),\"12:30:00\"))) + 1 == 16" =
      some (.fired .omission, ["value 5"]) := by native_decide

example : bounds.all (fun bound =>
    let filter := bound ++ "(Rows/Tag) == " ++ bound ++ "($Expected)"
    run filter (first := "") == some (.fired .omission, ["value 5"]) &&
      run filter (first := "bad") == some (.fired .omission, []) &&
      run filter "0" (outer := "") == some (.fired .omission, ["value 0"]) &&
      run filter "0" (outer := "bad") == some (.fired .omission, [])) = true ∧
    bounds.all (fun bound =>
      let filter := "HoursFromTime(TimeFromDateTime(DateTime(" ++ bound ++ "(Rows/Tag),\"12:30:00\"))) == 0"
      run filter "9" (first := "") == some (.fired .omission, ["value 9"]) &&
        run filter "0" (first := "bad") == some (.fired .omission, [])) = true := by native_decide

private def formatted (outerFormat rowFormat : String) (baseYear : Option Int := none) : FlatModel :=
  { model with baseYear, fields := model.fields.map fun field =>
    if field.id == 2 || field.id == 3 then { field with dateRangePolicy := some {
      format := if field.id == 2 then outerFormat else rowFormat
      separator := "/" } } else field }

example : bounds.all (fun bound => [false, true].all fun reverse =>
    let inner := bound ++ "(Rows/Tag)"
    let outer := bound ++ "($Expected)"
    let filter := if reverse then outer ++ " == " ++ inner else inner ++ " == " ++ outer
    [0, 1672531200000].all fun epochMillis =>
      run filter "5" "02-01/02-29" "03/03" "02/02" (formatted "MM-dd" "MM")
        (clock := { epochMillis }) == some (.fired .omission, ["value 5"])) = true ∧
    run "EndOfDateRange(Rows/Tag) == EndOfDateRange($Expected)" "0"
      "02-01/02-28" "03/03" "02/02" (formatted "MM-dd" "MM") =
        some (.fired .omission, ["value 0"]) ∧
    run "StartOfDateRange(Rows/Tag) == StartOfDateRange($Expected)" "0"
      "02-02/02-29" "03/03" "02/02" (formatted "MM-dd" "MM") =
        some (.fired .omission, ["value 0"]) := by native_decide

private def accepted (filter : String) (fixture : FlatModel := model) : Bool :=
  ((parseText .english ("Sum(Rows*/N Having " ++ filter ++ ") > 0")).toOption.bind fun parsed =>
    (lowerCondition fixture ["Form"] false parsed.body).toOption).isSome

example : bounds.all (fun bound =>
    let filter := bound ++ "(Rows/Tag) == " ++ bound ++ "($Expected)"
    !accepted filter (formatted "yyyy-MM-dd" "MM") &&
      accepted filter (formatted "yyyy-MM-dd" "MM" (some 2024)) &&
      run filter "5" "2024-02-01/2024-02-29" "03/03" "02/02"
        (formatted "yyyy-MM-dd" "MM" (some 2024)) == some (.fired .omission, ["value 5"])) = true ∧
    run "StartOfDateRange(Rows/Tag) == \"01.01.2024\"" "5"
      "2024/2024" "2023/2023" "2024/2024" (formatted "yyyy" "yyyy") =
        some (.fired .omission, ["value 5"]) ∧
    run "EndOfDateRange(Rows/Tag) == \"31.12.2024\"" "5"
      "2024/2024" "2023/2023" "2024/2024" (formatted "yyyy" "yyyy") =
        some (.fired .omission, ["value 5"]) := by native_decide

private def pointerModel : FlatModel := { model with fields := model.fields ++ [{
  id := 6, name := "Token", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .string } }] }
example : bounds.all (fun bound =>
    HavingFixture.referencesFor (bound ++ "(/Form/Rows/Tag) == " ++ bound ++ "($/Form/Rows/Tag)")
      pointerModel "Token" == some (true, true) &&
    HavingFixture.referencesFor (bound ++ "(/Form/Rows/Tag) == \"12.04.2024\"")
      pointerModel "Token" == some (true, false)) = true ∧
    HavingFixture.referencesFor
      "DateTime(StartOfDateRange(/Form/Rows/Tag),\"12:30:00\") == DateTime(EndOfDateRange($/Form/Rows/Tag),\"12:30:00\")"
      pointerModel "Token" = some (true, true) := by native_decide

private def producerModel : FlatModel := { model with
  fields := model.fields ++ [(6, "Start"), (7, "Finish")].map fun (id, name) => {
    id, name, groupPath := ["Form"]
    policy := { kind := .temporal .date TemporalComponents.fullDate }
    temporalTargetPolicy := some { format := "yyyy-MM-dd" } } }
example : bounds.all (fun bound =>
    HavingFixture.runModel producerModel (bound ++ "(Rows/Tag) == " ++ bound ++ "($Expected)") true
      "2024-04-12/2024-04-15" "2024-04-11/2024-04-14" "2024-04-12/2024-04-15"
      "DateRange(Start, Finish)" [("Start", .str "2024-04-11"), ("Finish", .str "2024-04-14")]
      (ruleExpected := "5") ==
        some (.fired .omission, ["value 2024-04-11/2024-04-14", "value 9"])) = true := by native_decide

example : bounds.all (fun bound =>
    let valid := bound ++ "(Rows/Tag) == " ++ bound ++ "($Expected)"
    accepted valid && !accepted valid { model with timeZoneId := "America/New_York" } &&
      ["[Rows/Tag]", "{Rows/Tag}", "Rows/N", "Rows", "Rows*/Tag", "Rows/Tag -> Label",
        "Rows/Tag For \"k\"", "Rows*/Tag Having FieldFilled(Rows/N)",
        "DateRange(\"11.04.2024\",\"14.04.2024\")", "\"12.04.2024\"", ""].all
        (fun source => !accepted (bound ++ "(" ++ source ++ ") == " ++ bound ++ "($Expected)")) &&
      !accepted (bound ++ "(Rows/Tag,$Expected) == " ++ bound ++ "($Expected)") &&
      !accepted (bound ++ "($Rows/Tag) == " ++ bound ++ "($Expected)") &&
      !accepted (bound ++ "($Expected) == \"12.04.2024\"") &&
      run (bound ++ "($Expected) == " ++ bound ++ "($Expected) And FieldFilled(Rows/N)") "14" ==
        some (.fired .omission, ["value 14"])) = true := by native_decide

example : bounds.all (fun bound =>
    ["YearFromDate", "MonthFromDate", "DayFromDate"].all fun operator =>
      let amount := if operator == "YearFromDate" then "2024"
        else if operator == "MonthFromDate" then "4" else if bound == "StartOfDateRange" then "12" else "15"
      let selected := if operator == "DayFromDate" then "5" else "14"
      run (operator ++ "(" ++ bound ++ "(Rows/Tag)) == " ++ amount) selected ==
        some (.fired .omission, ["value " ++ selected])) = true ∧
    run "MonthFromDate(EndOfDateRange(Rows/Tag)) == 2" "5" "02/02" "03/03" "02/02"
      (formatted "MM" "MM") = some (.fired .omission, ["value 5"]) ∧
    !accepted "DayFromDate(EndOfDateRange(Rows/Tag)) == 29" (formatted "MM" "MM") = true ∧
    !accepted "YearFromDate(StartOfDateRange(Rows/Tag)) == 2024" (formatted "MM" "MM") = true ∧
    run "YearFromDate(StartOfDateRange(Rows/Tag)) == 2024 And FieldFilled(Rows/N)" "14"
      "02/02" "03/03" "02/02" (formatted "MM" "MM" (some 2024)) =
        some (.fired .omission, ["value 14"]) := by native_decide

end A12Kernel.Dm.HavingRangeEndpointLocks
