import A12Kernel.Reference.Dm.HavingFixture

namespace A12Kernel.Dm.HavingCalendarLocks
open Lean A12Kernel HavingFixture

private def dates : FlatModel := { model with fields := model.fields.map fun field =>
  if field.id == 2 || field.id == 3 then { field with
    policy := { kind := .temporal .date TemporalComponents.fullDate }
    temporalTargetPolicy := some { format := "yyyy-MM-dd" } } else field }

example : [("DifferenceInMonths", "12"), ("DifferenceInYears", "1"), ("DifferenceInDays", "366")].all
    (fun (op, expected) => runModel dates s!"{op}(Rows/Tag, $Expected) == {expected}" false
      "2025-03-01" "2024-02-29" "2025-02-28" == some (.fired .omission, ["value 9"])) = true := by native_decide

example : runModel dates "DifferenceInDays($Expected, Rows/Tag) == -366" false
    "2025-03-01" "2024-02-29" "2025-02-28" = some (.fired .omission, ["value 9"]) ∧
    runModel dates "DifferenceInMonths(Rows/Tag, $Expected) == 0" false
      "2025-03-01" "" "2024-02-29" = some (.fired .omission, ["value 9"]) ∧
    runModel dates "DifferenceInYears(Rows/Tag, $Expected) == 0" false
      "2025-03-01" "bad" "2024-02-29" = some (.notFired, []) := by native_decide

private def dateTimes : FlatModel := { dates with timeZoneId := "Europe/Berlin", fields := dates.fields.map fun field =>
  if field.id == 2 || field.id == 3 then { field with
    policy := { kind := .temporal .dateTime (TemporalComponents.ofFormat "yyyy-MM-dd'T'HH:mm:ss") }
    temporalTargetPolicy := some { format := "yyyy-MM-dd'T'HH:mm:ss" } } else field }

example : runModel dateTimes "DifferenceInDays(Rows/Tag, $Expected) == 1" false
      "2024-03-31T12:00:00" "2024-03-30T12:00:00" "2024-03-31T12:00:00" = some (.fired .omission, ["value 9"]) ∧
    runModel dateTimes "DifferenceInDays(Rows/Tag, $Expected) == 1" false
      "2024-10-27T12:00:00" "2024-10-26T12:00:00" "2024-10-27T12:00:00" = some (.fired .omission, ["value 9"]) ∧
    runModel dates "DifferenceInMonths(Rows/Tag, $Expected) + 1 == 2" false
      "2024-02-29" "2024-01-31" "2024-02-01" = some (.fired .omission, ["value 9"]) := by native_decide

example : ["DifferenceInMonths", "DifferenceInYears"].all (fun op =>
    (runModel dateTimes s!"{op}(Rows/Tag, $Expected) > 0" false
      "2024-03-31T12:00:00" "2024-03-30T12:00:00" "2024-03-31T12:00:00").isNone) = true ∧
    (runModel { dates with timeZoneId := "America/New_York" }
      "DifferenceInDays(Rows/Tag, $Expected) > 0" false "2025-03-01" "2024-02-29" "2025-02-28").isNone = true ∧
    (runModel dates "DifferenceInDays(Rows/Tag, $Expected) == 1.0" false
      "2025-03-01" "2024-02-29" "2025-02-28").isNone = true := by native_decide

example : runModel dates "DifferenceInDays(Rows/Tag, $Expected) == 1" true
    "2025-03-01" "2024-02-29" "2025-02-28" "Date(\"01\", \"03\", \"2024\")" =
      some (.notFired, ["value 2024-03-01", "value 9"]) := by native_decide

private def formatted (left right : String) (baseYear : Option Int := none) : FlatModel := {
  dates with baseYear, fields := dates.fields.map fun field =>
    if field.id == 2 || field.id == 3 then
      let format := if field.id == 3 then left else right
      { field with
        policy := { kind := .temporal .date (TemporalComponents.ofFormat format) }
        temporalTargetPolicy := some { format } }
    else field }

private def admissions (fixture : FlatModel) (filter : String) (filtered : Bool := true) : List Bool :=
  let expression := if filtered then "Sum(Rows*/N Having " ++ filter ++ ")" else filter
  [((parseText .english (expression ++ " > 0")).toOption.bind fun parsed =>
    (lowerCondition fixture ["Form"] false parsed.body).toOption).isSome,
  (lowerComputation fixture .english {
    group := ["Form"], name := "Total", targetRelPath := "../Out", commonPrecondition := none,
    alternatives := [{ precondition := none, operation := expression }], errorCodesToSuppress := [] }).isOk]

private def admitted (fixture : FlatModel) (filter : String) : Bool := (admissions fixture filter).all id
private def refused (fixture : FlatModel) (filter : String) : Bool := (admissions fixture filter).all (!·)

example : [("DifferenceInMonths", "MM"), ("DifferenceInYears", "MM"), ("DifferenceInDays", "MM-dd")].all
    (fun (op, format) =>
      refused (formatted format "yyyy-MM-dd") s!"{op}(Rows/Tag, $Expected) > 0" &&
      admitted (formatted format "yyyy-MM-dd" (some 2024)) s!"{op}(Rows/Tag, $Expected) > 0") = true ∧
    refused (formatted "yyyy" "yyyy") "DifferenceInMonths(Rows/Tag, $Expected) > 0" ∧
    refused (formatted "yyyy-MM" "yyyy-MM") "DifferenceInDays(Rows/Tag, $Expected) > 0" ∧
    admitted (formatted "yyyy" "yyyy") "DifferenceInYears(Rows/Tag, $Expected) > 0" := by native_decide

example : ["DifferenceInMonths", "DifferenceInYears", "DifferenceInDays"].all (fun op =>
    referencesFor s!"{op}(/Form/Rows/Tag, $/Form/Rows/Tag) == 0"
      { dates with fields := dates.fields ++ [{
        id := 6, name := "Token", groupPath := ["Form", "Rows"]
        repeatableScope := [10], policy := { kind := .string } }] } "Token" == some (true, true) &&
    refused dates s!"{op}(Rows*/Tag, $Expected) > 0" &&
    refused dates s!"{op}([Rows/Tag], $Expected) > 0" &&
    refused dates s!"{op}(Rows/N, $Expected) > 0" &&
    refused dates s!"{op}(Rows/Tag, $Out) > 0") = true := by native_decide

example : [("DifferenceInMonths", "12"), ("DifferenceInYears", "1"), ("DifferenceInDays", "366")].all
    (fun (op, expected) => runModel dates s!"{op}(Rows/Tag, \"01.03.2025\") == {expected}" false
      "unused" "2024-02-29" "2025-02-28" == some (.fired .omission, ["value 9"])) = true := by native_decide

example : [("DifferenceInMonths", "-12"), ("DifferenceInYears", "-1"), ("DifferenceInDays", "-366")].all
    (fun (op, expected) => runModel dates s!"{op}(\"01.03.2025\", Rows/Tag) == {expected}" false
      "unused" "2024-02-29" "2025-02-28" == some (.fired .omission, ["value 9"])) = true := by native_decide

example : [("DifferenceInMonths", "12"), ("DifferenceInYears", "1"), ("DifferenceInDays", "366")].all
    (fun (op, expected) => runModel { dates with baseYear := some 2025 }
      s!"{op}(Rows/Tag, BaseYear) == {expected}" false
      "unused" "2024-01-01" "2025-01-01" == some (.fired .omission, ["value 9"]) &&
      runModel { dates with baseYear := some 2025 } s!"{op}(BaseYear, Rows/Tag) == -{expected}" false
      "unused" "2024-01-01" "2025-01-01" == some (.fired .omission, ["value 9"])) = true := by native_decide

example : runModel { dates with baseYear := some 2024 }
    "DifferenceInDays(Rows/Tag, \"01.03.\") == 1" false
    "unused" "2024-02-29" "2024-02-28" = some (.fired .omission, ["value 9"]) ∧
    runModel (formatted "MM-dd" "MM-dd") "DifferenceInDays(Rows/Tag, \"01.03.\") == 2" false
      "" "02-28" "03-01" = some (.fired .omission, ["value 9"]) ∧
    runModel (formatted "MM-dd" "MM-dd" (some 2024)) "DifferenceInDays(\"01.03.\", Rows/Tag) == -2" false
      "" "02-28" "03-01" = some (.fired .omission, ["value 9"]) := by native_decide

example : ["DifferenceInMonths", "DifferenceInYears", "DifferenceInDays"].all (fun op =>
    refused dates s!"{op}(Rows/Tag, BaseYear) == 0" &&
    refused dates s!"{op}(Rows/Tag, \"01.03.\") == 0" &&
    refused { dates with baseYear := some 2024 } s!"{op}(Rows/Tag, \"29.02.\") == 0" &&
    refused dates s!"{op}(Rows/Tag, \"2024-03-01\") == 0" &&
    refused dates s!"{op}(Rows/Tag, \"29.02.2023\") == 0" &&
    refused dates s!"{op}(\"01.03.2024\", \"01.03.2025\") > 0" &&
    refused dates s!"{op}($Expected, \"01.03.2025\") > 0" &&
    admitted dates s!"[Rows/N] > 0 And {op}($Expected, \"01.03.2025\") > 0" &&
    admitted dates s!"{op}(Rows/Tag, Today) > 0" &&
    refused dates s!"{op}(Rows/Tag, Now) > 0") = true := by native_decide

example : runModel dates "[Rows/N] > 0 And DifferenceInDays($Expected, \"02.03.2024\") == 1" true
    "2025-03-01" "2024-02-29" "2025-02-28" "Date(\"01\", \"03\", \"2024\")" =
      some (.notFired, ["value 2024-03-01", "value 14"]) ∧
    runModel dates "DifferenceInDays(Rows/Tag, \"01.03.2024\") == 0" false
      "unused" "" "2024-03-02" = some (.fired .omission, ["value 9"]) ∧
    runModel dates "DifferenceInMonths(\"01.03.2024\", Rows/Tag) == 0" false
      "unused" "bad" "2024-03-02" = some (.notFired, []) := by native_decide

example : ["DifferenceInMonths", "DifferenceInYears", "DifferenceInDays"].all (fun op =>
    let fixture := { dates with fields := dates.fields ++ [{
      id := 6, name := "Token", groupPath := ["Form", "Rows"]
      repeatableScope := [10], policy := { kind := .string } }] }
    referencesFor s!"{op}(/Form/Rows/Tag, \"01.03.2025\") > 0" fixture "Token" == some (true, false) &&
    referencesFor s!"[/Form/Rows/N] > 0 And {op}(\"01.03.2025\", $/Form/Rows/Tag) > 0" fixture "Token" == some (false, true)) = true := by native_decide


private def certifiedSource (source : ResolvedDateDifferenceOperand HavingTemporalRef) : Bool :=
  CorrelatedHavingLeaf.wellFormedForEnvironments { dates with baseYear := some 2024 } [10] [] (.numeric {
    op := .ordinary .equal
    left := .atom (.dayDifference .utc (.field { origin := .inner, field := {
      id := 3, kind := .date, components := TemporalComponents.fullDate } }) source)
    right := .literal { value := 0, authoredScale := 0 } })

example : certifiedSource (.literal { year := none, month := 3, day := 1 } 2024) = true ∧
    certifiedSource (.literal { year := none, month := 3, day := 1 } 2023) = false ∧
    certifiedSource (.literal { year := none, month := 2, day := 29 } 2024) = false ∧
    certifiedSource (.baseYear 2024 .direct) = true ∧
    certifiedSource (.baseYear 2025 .direct) = false ∧
    certifiedSource (.today .utc) = true ∧
    certifiedSource (.today .europeBerlin) = false := by native_decide


private def baseYearSources : List (String × List String) :=
  [("BaseYear", ["2024", "1", "1", "1"]),
   ("StartOfDateRange(BaseYear)", ["2024", "1", "1", "1"]),
   ("EndOfDateRange(BaseYear)", ["2024", "12", "31", "4"])]

example : baseYearSources.all (fun (source, values) =>
    (["YearFromDate", "MonthFromDate", "DayFromDate", "QuarterFromDate"].zip values).all fun (op, expected) =>
      runModel { dates with baseYear := some 2024 } "" false "" "" ""
        (operationOverride := some s!"{op}({source}) + 0") (ruleExpected := expected) ==
        some (.fired .value, [s!"value {expected}"]) &&
      runModel { dates with baseYear := some 2024 }
        s!"FieldFilled(Rows/Tag) And {op}({source}) == {expected}" false
        "" "2024-01-01" "" == some (.fired .omission, ["value 9"]) &&
      (admissions dates s!"{op}({source})" false).all (!·) &&
      refused dates s!"FieldFilled(Rows/Tag) And {op}({source}) == {expected}") = true := by native_decide

example : [("StartOfDateRange", "2023-01-01", "2024-01-01", "365"),
    ("EndOfDateRange", "2023-12-31", "2024-12-31", "366")].all (fun (bound, first, second, days) =>
      [("DifferenceInMonths", "12"), ("DifferenceInYears", "1"), ("DifferenceInDays", days)].all fun (op, expected) =>
        runModel { dates with baseYear := some 2024 }
          s!"{op}(Rows/Tag, {bound}(BaseYear)) == {expected}" false "" first second ==
          some (.fired .omission, ["value 9"]) &&
        runModel { dates with baseYear := some 2024 }
          s!"{op}({bound}(BaseYear), Rows/Tag) == -{expected}" false "" first second ==
          some (.fired .omission, ["value 9"])) = true := by native_decide

example : [("DifferenceInMonths", "11"), ("DifferenceInYears", "0"), ("DifferenceInDays", "365")].all
    (fun (op, expected) =>
      runModel { dates with baseYear := some 2024 } "" false "" "" ""
        (operationOverride := some s!"{op}(StartOfDateRange(BaseYear),EndOfDateRange(BaseYear))")
        (ruleExpected := expected) == some (.fired .value, [s!"value {expected}"]) &&
      (admissions dates s!"{op}(StartOfDateRange(BaseYear),EndOfDateRange(BaseYear))" false).all (!·) &&
      refused dates s!"{op}(Rows/Tag, EndOfDateRange(BaseYear)) > 0") = true := by native_decide

example : runModel { dates with baseYear := some 2023 } "" false "" "" ""
    (operationOverride := some "DifferenceInDays(EndOfDateRange(BaseYear),StartOfDateRange(BaseYear))")
    (ruleExpected := "-364") = some (.fired .value, ["value -364"]) ∧
    runModel { dates with baseYear := some 2024 } "DifferenceInDays(EndOfDateRange(BaseYear), Rows/Tag) == 0"
      false "" "" "2024-01-01" = some (.fired .omission, ["value 9"]) ∧
    runModel { dates with baseYear := some 2024 } "DifferenceInMonths(Rows/Tag, StartOfDateRange(BaseYear)) == 0"
      false "" "bad" "2024-01-01" = some (.notFired, []) := by native_decide

example : ["StartOfDateRange(BaseYear)", "EndOfDateRange(BaseYear)"].all (fun source =>
    refused { dates with baseYear := some 2024 } s!"DifferenceInDays({source}, BaseYear) == 0" &&
    ["DifferenceInHours", "DifferenceInMinutes", "DifferenceInSeconds"].all fun op =>
      (admissions { dates with baseYear := some 2024 } s!"{op}({source}, Now)" false).all (!·) &&
      refused { dates with baseYear := some 2024 } s!"{op}(Rows/Tag, {source}) == 0") = true := by native_decide


example : ["StartOfDateRange(BaseYear,BaseYear)", "EndOfDateRange(BaseYear,BaseYear)",
    "MonthFromDate(BaseYear)"].all (fun source =>
      (admissions { dates with baseYear := some 2024 } s!"DifferenceInDays(BaseYear,{source})" false).all (!·) &&
      refused { dates with baseYear := some 2024 } s!"DifferenceInDays(Rows/Tag,{source}) == 0") = true := by native_decide

example : ["StartOfDateRange", "EndOfDateRange"].all (fun bound =>
    referencesFor s!"DifferenceInDays(/Form/Rows/Tag,{bound}(BaseYear)) > 0"
      { dates with baseYear := some 2024, fields := dates.fields ++ [{
        id := 6, name := "Token", groupPath := ["Form", "Rows"]
        repeatableScope := [10], policy := { kind := .string } }] } "Token" == some (true, false)) = true := by native_decide


example : [("DifferenceInYears", "1"), ("DifferenceInMonths", "12"), ("DifferenceInDays", "365")].all
    (fun (op, expected) =>
      runModel dates s!"{op}(Rows/Tag, Today) == {expected}" false "" "1969-01-01" "1970-01-01" ==
        some (.fired .omission, ["value 9"]) &&
      runModel dates s!"{op}(Rows/Tag, Today) == {expected}" false "" "1969-01-01" "1970-01-01"
        (clock := { epochMillis := 31536000000 }) == some (.notFired, ["value 5"])) = true := by native_decide

example : [("Sum", "9", "5"), ("MinValue", "2", "5"), ("MaxValue", "7", "5"),
    ("FirstFilledValue", "2", "5"), ("NumberOfDifferentValues", "2", "1"),
    ("NumberOfFilledFields", "2", "1")].all (fun (op, first, second) =>
      let expression := s!"{op}(Rows*/N Having DifferenceInDays(Rows/Tag, Today) == 365)"
      runModel dates "" false "" "1969-01-01" "1970-01-01"
        (operationOverride := some expression) (ruleExpected := first) == some (.fired .omission, ["value " ++ first]) &&
      runModel dates "" false "" "1969-01-01" "1970-01-01"
        (operationOverride := some expression) (ruleExpected := first)
        (clock := { epochMillis := 31536000000 }) == some (.notFired, ["value " ++ second])) = true := by native_decide

private def clockFilter : String := "[Rows/N] > 0 And DifferenceInDays(Today, \"01.01.1970\") == 0"

private def booleanTags : FlatModel := { model with fields := model.fields.map fun field =>
  if field.id == 3 then { field with policy := { kind := .boolean } } else field }

example : [(model, "NumberOfValueInFields(2 In Rows*/N", "1", "keep", "drop"),
    (model, "NumberOfValueInFields(\"keep\" In Rows*/Tag", "2", "keep", "drop"),
    (model, "NumberOfDifferentValues(Rows*/Tag", "2", "keep", "drop"),
    (booleanTags, "NumberOfValueInFields(True In Rows*/Tag", "2", "true", "false"),
    (dates, "NumberOfDifferentValues(Rows*/Tag", "2", "1970-01-01", "1971-01-01")].all
    (fun (fixture, operationStart, count, first, second) =>
      let operation := some (operationStart ++ " Having " ++ clockFilter ++ ")")
      runModel fixture "" false "" first second (operationOverride := operation) (ruleExpected := count) ==
        some (.fired .omission, ["value " ++ count]) &&
      runModel fixture "" false "" first second (operationOverride := operation) (ruleExpected := count)
        (clock := { epochMillis := 86400000 }) == some (.notFired, ["value 0"])) = true := by native_decide

private def stringTarget : FlatModel := { model with fields := model.fields.map fun field =>
  if field.id == 5 then { field with policy := { kind := .string } } else field }

example : runModel stringTarget "" false "" "keep" "drop"
    (operationOverride := some s!"FirstFilledValue(Rows*/Tag Having {clockFilter})") (ruleExpected := "\"keep\"") =
      some (.fired .omission, ["value keep"]) ∧
    runModel stringTarget "" false "" "keep" "drop"
      (operationOverride := some s!"FirstFilledValue(Rows*/Tag Having {clockFilter})") (ruleExpected := "\"keep\"")
      (clock := { epochMillis := 86400000 }) = some (.notFired, []) := by native_decide

example : [("AtLeastOneFieldFilled", Verdict.unknown), ("FieldValuesNotUnique", Verdict.notFired)].all
    (fun (op, emptyVerdict) =>
      let guard := s!"{op}(Rows*/Tag Having {clockFilter})"
      runModel model "" false "" "keep" "drop" (operationOverride := some "1")
        (ruleCondition := some ("FieldFilled(Error) And " ++ guard)) (computationPrecondition := some guard) ==
          some (.fired .omission, ["value 1"]) &&
      runModel model "" false "" "keep" "drop" (operationOverride := some "1")
        (ruleCondition := some ("FieldFilled(Error) And " ++ guard)) (computationPrecondition := some guard)
        (clock := { epochMillis := 86400000 }) == some (emptyVerdict, [])) = true := by native_decide

example : runModel dates "DifferenceInDays(Rows/Tag, Today) == 0" false "" "1969-12-31" "1970-01-01"
    (clock := { epochMillis := -1800000 }) = some (.fired .omission, ["value 9"]) ∧
    runModel { dates with timeZoneId := "Europe/Berlin" } "DifferenceInDays(Rows/Tag, Today) == 0" false "" "1969-12-31" "1970-01-01"
      (clock := { epochMillis := -1800000 }) = some (.notFired, ["value 5"]) ∧
    runModel dates "DifferenceInDays(Today, Rows/Tag) == -365" false "" "1969-01-01" "1970-01-01" =
      some (.fired .omission, ["value 9"]) := by native_decide

private def enumerationTarget : FlatModel := { stringTarget with fields := stringTarget.fields.map fun field =>
  if field.id == 3 || field.id == 5 then { field with
    policy := { kind := .enumeration }, enumeration := some { storedTokens := ["keep", "drop"] } } else field }

example : runModel enumerationTarget "" false "" "keep" "drop"
    (operationOverride := some s!"FirstFilledValue(Rows*/Tag Having {clockFilter})") (ruleExpected := "\"keep\"") =
      some (.fired .omission, ["value keep"]) ∧
    runModel enumerationTarget "" false "" "keep" "drop"
      (operationOverride := some s!"FirstFilledValue(Rows*/Tag Having {clockFilter})") (ruleExpected := "\"keep\"")
      (clock := { epochMillis := 86400000 }) = some (.notFired, []) := by native_decide

example : refused dates "DifferenceInDays(Today, \"01.01.1970\") == 0" ∧
    refused dates "DifferenceInDays(Rows/Tag, Now) == 0" ∧
    refused { dates with timeZoneId := "America/New_York" } "DifferenceInYears(Rows/Tag, Today) == 0" := by native_decide

example : [(model, "keep", "drop"), (dates, "1970-01-01", "1971-01-01")].all
    (fun (fixture, first, second) =>
      let guard := s!"FieldValuesNotUnique(Rows*/Tag Having {clockFilter})"
      runModel fixture "" false "" first second (operationOverride := some "1")
        (ruleCondition := some ("FieldFilled(Error) And " ++ guard)) (computationPrecondition := some guard) ==
          some (.fired .omission, ["value 1"]) &&
      runModel fixture "" false "" first second (operationOverride := some "1")
        (ruleCondition := some ("FieldFilled(Error) And " ++ guard)) (computationPrecondition := some guard)
        (clock := { epochMillis := 86400000 }) == some (.notFired, [])) = true := by native_decide

private def utcInstants : FlatModel := { dateTimes with timeZoneId := "UTC" }

example : [("DifferenceInHours", "2"), ("DifferenceInMinutes", "120"), ("DifferenceInSeconds", "7201")].all
    (fun (op, expected) =>
      runModel utcInstants s!"{op}(Rows/Tag, Now) == {expected}" false
        "unused" "1970-01-01T00:00:00" "1970-01-01T03:00:00"
        (clock := { epochMillis := 7201999 }) == some (.fired .omission, ["value 9"]) &&
      runModel utcInstants s!"{op}(Now, Rows/Tag) == -{expected}" false
        "unused" "1970-01-01T00:00:00" "1970-01-01T03:00:00"
        (clock := { epochMillis := 7201999 }) == some (.fired .omission, ["value 9"])
    ) = true := by native_decide

example : ["DifferenceInHours", "DifferenceInMinutes", "DifferenceInSeconds"].all (fun op =>
    admitted utcInstants s!"{op}(Rows/Tag, Now) > 0" &&
    refused utcInstants s!"{op}(Now, Now) == 0" &&
    refused utcInstants s!"{op}($Expected, Now) == 0" &&
    admitted utcInstants s!"[Rows/N] > 0 And {op}($Expected, Now) == 0" &&
    refused utcInstants s!"{op}(Rows/Tag, Today) > 0" &&
    refused utcInstants s!"{op}(Rows/Tag, BaseYear) > 0" &&
    refused dates s!"{op}(Rows/Tag, Now) > 0") = true := by native_decide

example : runModel utcInstants "DifferenceInSeconds(Now, Rows/Tag) == 0" false
    "unused" "1970-01-01T00:00:01" "1970-01-01T00:00:03"
    (clock := { epochMillis := 999 }) = some (.fired .omission, ["value 9"]) ∧
    runModel utcInstants "DifferenceInSeconds(Now, Rows/Tag) == 0" false
      "unused" "1970-01-01T00:00:01" "1970-01-01T00:00:03"
      (clock := { epochMillis := 3000 }) = some (.notFired, ["value 5"]) ∧
    runModel utcInstants "[Rows/N] > 0 And DifferenceInSeconds($Expected, Now) == 1" false
      "1970-01-01T00:00:00" "1970-01-01T00:00:03" "1970-01-01T00:00:04"
      (clock := { epochMillis := 1999 }) (ruleExpected := "14") = some (.fired .omission, ["value 14"]) := by native_decide

example : ["[Rows/Tag] < Today", "Today > [Rows/Tag]", "[Rows/Tag] < \"02.01.1970\"",
    "\"02.01.1970\" > [Rows/Tag]"].all (fun filter =>
      runModel dates filter false "unused" "1970-01-01" "1970-01-03"
        (clock := { epochMillis := 86400000 }) (zoneRules := ModelZone.concreteRules) == some (.fired .omission, ["value 9"])) = true := by native_decide

example : ["[Rows/Tag] < Now", "Now > [Rows/Tag]"].all (fun filter =>
    runModel utcInstants filter false "unused" "1970-01-01T00:00:01" "1970-01-01T00:00:03"
      (clock := { epochMillis := 1001 }) == some (.fired .omission, ["value 9"])) = true := by native_decide

example : ["BaseYear", "StartOfDateRange(BaseYear)", "EndOfDateRange(BaseYear)"].all (fun source =>
    runModel { dates with baseYear := some 1970 } s!"[Rows/Tag] < {source}" false
      "unused" "1969-01-01" "1971-01-01" (zoneRules := ModelZone.concreteRules) == some (.fired .omission, ["value 9"])) = true := by native_decide

example : runModel { model with baseYear := some 2024 } "[Rows/N] < BaseYear" false
    "unused" "a" "b" (ruleExpected := "14") = some (.fired .omission, ["value 14"]) := by native_decide

example : [("<", "9"), ("<=", "9"), (">", "5"), (">=", "5"), ("==", "0"), ("!=", "14")].all
    (fun (op, amount) => runModel dates s!"[Rows/Tag] {op} Today" false
      "unused" "1970-01-01" "1970-01-03" (clock := { epochMillis := 86400000 })
      (ruleExpected := amount) (zoneRules := ModelZone.concreteRules) == some (.fired .omission, [s!"value {amount}"])) = true := by native_decide

example : runModel { dates with baseYear := some 1970 } "[Rows/Tag] < \"02.01.\"" false
    "unused" "1970-01-01" "1970-01-03" = some (.fired .omission, ["value 9"]) ∧
    refused dates "[Rows/Tag] < \"02.01.\"" ∧
    refused { dates with baseYear := some 2024 } "[Rows/Tag] < \"29.02.\"" ∧
    refused utcInstants "[Rows/Tag] == Today" ∧
    refused dates "[Rows/Tag] == Now" ∧
    refused dates "Today == Today" ∧
    refused dates "[$Expected] < Today" ∧
    admitted dates "[Rows/N] > 0 And [$Expected] < Today" := by native_decide

example : runModel { dates with timeZoneId := "Europe/Berlin" } "[Rows/Tag] == Today" false
    "unused" "1970-01-01" "1969-12-31" (clock := { epochMillis := -1 })
    (zoneRules := ModelZone.concreteRules) = some (.fired .omission, ["value 9"]) ∧
    runModel dates "[Rows/Tag] == Today" false "unused" "1970-01-01" "1969-12-31"
      (clock := { epochMillis := -1 }) (ruleExpected := "5") (zoneRules := ModelZone.concreteRules) =
        some (.fired .omission, ["value 5"]) ∧
    runModel dates "[Rows/Tag] < Today" false "unused" "1970-01-01" "1970-01-03"
      (clock := { epochMillis := 86400000 }) = some (.notFired, []) := by native_decide

example : runModel dates "[Rows/N] > 0 And [$Expected] < Today" true
    "1971-01-01" "unused" "unused" "Date(\"01\", \"01\", \"1970\")"
    (clock := { epochMillis := 86400000 }) (zoneRules := ModelZone.concreteRules) =
      some (.notFired, ["value 1970-01-01", "value 14"]) ∧
    referencesFor "[/Form/Rows/N] > 0 And [$/Form/Rows/Tag] < Today"
      { dates with fields := dates.fields ++ [{
        id := 6, name := "Token", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .string } }] } "Token" = some (false, true) := by native_decide

example : [("MM-dd", "03-05", "07-14", "05.03."), ("MM", "03", "07", "01.03.")].all
    (fun (format, first, second, literal) =>
      let fixture := formatted format format
      runModel fixture s!"[Rows/Tag] == \"{literal}\"" false "unused" first second ==
        some (.fired .omission, ["value 9"]) &&
      runModel fixture s!"\"13.07.\" < [Rows/Tag]" false "unused" first second
        (ruleExpected := if format == "MM" then "0" else "5") ==
          some (.fired .omission, [if format == "MM" then "value 0" else "value 5"]) &&
      runModel fixture "" false first first second (operationOverride := some "1")
        (ruleCondition := some s!"FieldFilled(Error) And [Expected] == \"{literal}\"")
        (computationPrecondition := some s!"[Expected] == \"{literal}\"") ==
          some (.fired .value, ["value 1"])) = true := by native_decide

private def ordinaryAdmissions (fixture : FlatModel) (condition : String) : List Bool :=
  match (parseText .english condition).toOption with
  | none => [false, false]
  | some parsed => [(lowerCondition fixture ["Form"] false parsed.body).isOk,
      (lowerComputation fixture .english {
        group := ["Form"], name := "Total", targetRelPath := "../Out", commonPrecondition := none,
        alternatives := [{ precondition := some condition, operation := "1" }], errorCodesToSuppress := [] }).isOk]

example : [none, some 2023, some 2024].all (fun baseYear =>
    ["MM-dd", "yyyy-MM-dd"].all (fun format =>
      ["05.03.", "05.03.2024"].all (fun literal =>
        let fixture := formatted format format baseYear
        let expected := baseYear.isSome || ((format == "yyyy-MM-dd") == (literal == "05.03.2024"))
        [s!"[Rows/Tag] == \"{literal}\"", s!"\"{literal}\" < [Rows/Tag]"].all (fun condition =>
          (admissions fixture condition).all (· == expected)) &&
        [s!"[Expected] == \"{literal}\"", s!"\"{literal}\" < [Expected]"].all (fun condition =>
          (ordinaryAdmissions fixture condition).all (· == expected))))) = true := by native_decide

example : [none, some 2024].all (fun baseYear =>
    let fixture := formatted "MM-dd" "MM-dd" baseYear
    refused fixture "[Rows/Tag] < \"29.02.\"" &&
    (ordinaryAdmissions fixture "[Expected] < \"29.02.\"").all (!·)) = true := by native_decide

example : ["UTC", "Europe/Berlin"].all (fun zone =>
    [none, some 2024].all (fun baseYear =>
      let fixture := { formatted "MM-dd" "MM-dd" baseYear with timeZoneId := zone }
      runModel fixture "[Rows/Tag] < \"01.03.\"" false "02-29" "02-29" "03-01" ==
        some (.fired .omission, ["value 9"]) &&
      runModel fixture "" false "02-29" "02-29" "03-01" (operationOverride := some "1")
        (ruleCondition := some "FieldFilled(Error) And \"01.03.\" > [Expected]")
        (computationPrecondition := some "\"01.03.\" > [Expected]") ==
          some (.fired .value, ["value 1"]))) = true := by native_decide

example : runModel (formatted "MM-dd" "MM-dd" (some 2023)) "[Rows/Tag] < \"01.03.\"" false
    "unused" "02-29" "03-01" = some (.notFired, []) := by native_decide

private def clockComponents : List (String × String × String) :=
  ["Today", "Now"].flatMap (fun source =>
    [("DayFromDate", source, "1"), ("MonthFromDate", source, "4"),
      ("QuarterFromDate", source, "2"), ("YearFromDate", source, "2024")]) ++
    [("HoursFromTime", "Now", "12"), ("MinutesFromTime", "Now", "34"),
      ("SecondsFromTime", "Now", "56")]

example : clockComponents.all (fun (op, source, expected) =>
    let filter := s!"[Rows/N] > 0 And {op}({source}) == {expected}"
    admitted model filter && refused model s!"{op}({source}) == {expected}" &&
      runModel model filter false "" "" "" (clock := { epochMillis := 1711974896999 })
        (ruleExpected := "14") == some (.fired .omission, ["value 14"]) &&
      runModel model s!"[Rows/N] > 0 And {op}({source}) == {expected} + 1" false "" "" ""
        (clock := { epochMillis := 1711974896999 }) (ruleExpected := "14") ==
          some (.notFired, ["value 0"])) = true := by native_decide

example : ["HoursFromTime", "MinutesFromTime", "SecondsFromTime"].all (fun op =>
    refused model s!"[Rows/N] > 0 And {op}(Today) == 0") = true ∧
    clockComponents.all (fun (op, source, _) =>
      refused { model with timeZoneId := "America/New_York" } s!"[Rows/N] > 0 And {op}({source}) == 0" &&
      (admissions model s!"Sum(Rows/N Having [Rows/N] > 0 And {op}({source}) == 0)" false).all (!·)) = true := by native_decide

example : runModel model
    "[Rows/N] > 0 And MonthFromDate(Now) + QuarterFromDate(Today) * 2 == 8" false "" "" ""
    (clock := { epochMillis := 1711974896999 }) (ruleExpected := "14") ==
      some (.fired .omission, ["value 14"]) ∧
    runModel model "[Rows/N] > 0 And SecondsFromTime(Now) == 0" false "" "" ""
      (clock := { epochMillis := 999 }) (ruleExpected := "14") == some (.fired .omission, ["value 14"]) ∧
    runModel model "[Rows/N] > 0 And SecondsFromTime(Now) == 1" false "" "" ""
      (clock := { epochMillis := 1000 }) (ruleExpected := "14") == some (.fired .omission, ["value 14"]) := by native_decide

example : [("UTC", "31", "12", "4", "1969", "23"),
    ("Europe/Berlin", "1", "1", "1", "1970", "0")].all
    (fun (zone, day, month, quarter, year, hour) =>
      ["Today", "Now"].all (fun source =>
        (["DayFromDate", "MonthFromDate", "QuarterFromDate", "YearFromDate"].zip [day, month, quarter, year]).all
          fun (op, expected) => runModel { model with timeZoneId := zone }
            s!"[Rows/N] > 0 And {op}({source}) == {expected}" false "" "" ""
            (clock := { epochMillis := -1 }) (ruleExpected := "14") == some (.fired .omission, ["value 14"])) &&
      runModel { model with timeZoneId := zone }
        s!"[Rows/N] > 0 And HoursFromTime(Now) == {hour} And MinutesFromTime(Now) == 59 And SecondsFromTime(Now) == 59"
        false "" "" "" (clock := { epochMillis := -1 }) (ruleExpected := "14") ==
          some (.fired .omission, ["value 14"])) = true := by native_decide

example : runModel model "[Rows/N] > 0 And DayFromDate(Now) == 4 And YearFromDate(Now) == 1582"
    false "" "" "" (clock := { epochMillis := -12219379200000 }) (ruleExpected := "14") ==
      some (.fired .omission, ["value 14"]) := by native_decide

private def clockAtoms : List HavingNumericAtom :=
  [.today, .now].flatMap (fun source => [.day, .month, .quarter, .year].map fun part =>
    .clockPart source .utc (.date part)) ++
    [.hour, .minute, .second].map (fun part => .clockPart .now .utc (.time part))

private def clockFrame : CorrelationFrame := { innerEnv := [(10, 1)], outerEnv := [(10, 2)] }
private def clockContext (clock : Option Instant) : CorrelationContext := {
  read := fun _ _ => checkAdmittedRawCell (.rejected .malformed)
  world := clock.map fun now => { now } }
private def clockResolving (clock : Option Instant) : ResolvingCorrelationContext String := {
  read := fun _ _ => .error "field read"
  bindingError := fun _ => "binding", unsupportedDateCalendar := "calendar"
  temporalValueFailure := "value failure"
  worldUnavailable := "world unavailable"
  typeValidityValueFailure := "type validity value failure", groupUnavailable := fun _ => "group unavailable"
  world := clock.map fun now => { now } }
private def calendarRefusal (result : Except String α) : Bool :=
  match result with | .error reason => reason == "calendar" | .ok _ => false
private def clockCondition (atom : HavingNumericAtom) : CorrelatedHaving := .leaf (.numeric {
  op := .ordinary .equal, left := .atom atom, right := .literal { value := 0, authoredScale := 0 } })

example : [none, some { epochMillis := -100000000000000 }].all (fun clock =>
    clockAtoms.all fun atom =>
      (atom.readValidation (clockContext clock) clockFrame).toOption.isNone &&
      (atom.readComputation (clockContext clock) clockFrame).toOption.isNone &&
      calendarRefusal (atom.readValidationResolving (clockResolving clock) clockFrame) &&
      calendarRefusal (atom.readComputationResolving (clockResolving clock) clockFrame)) = true := by native_decide

example :
    let clock := some { epochMillis := -12219379200000 }
    let today := HavingNumericAtom.clockPart .today .utc (.date .day)
    let now := HavingNumericAtom.clockPart .now .utc (.date .day)
    (today.readValidation (clockContext clock) clockFrame).toOption.isNone &&
      (today.readComputation (clockContext clock) clockFrame).toOption.isNone &&
      calendarRefusal (today.readValidationResolving (clockResolving clock) clockFrame) &&
      calendarRefusal (today.readComputationResolving (clockResolving clock) clockFrame) &&
      (now.readValidation (clockContext clock) clockFrame).toOption == some (.value 4 .fixed) &&
      (now.readComputation (clockContext clock) clockFrame).toOption == some (.value 4) &&
      ((now.readValidationResolving (clockResolving clock) clockFrame).toOption.bind (·.toOption)) ==
        some (.value 4 .fixed) &&
      (now.readComputationResolving (clockResolving clock) clockFrame).toOption == some (.value 4)
    := by native_decide

example : (clockAtoms.zip [1, 4, 2, 2024, 1, 4, 2, 2024, 12, 34, 56]).all (fun (atom, expected) =>
    let clock := some { epochMillis := 1711974896999 }
    (atom.readValidation (clockContext clock) clockFrame).toOption == some (.value expected .fixed) &&
      ((atom.readValidationResolving (clockResolving clock) clockFrame).toOption.bind (·.toOption)) ==
        some (.value expected .fixed) &&
      (atom.readComputationResolving (clockResolving clock) clockFrame).toOption == some (.value expected)) = true := by native_decide

example : clockAtoms.all (fun atom =>
    let condition := clockCondition atom
    atom.origins.isEmpty && atom.fieldOrigins.isEmpty && condition.fieldIds.isEmpty &&
      condition.markedFieldIds.isEmpty && !condition.usesInner && !condition.usesOuter &&
      condition.outerIterationScopes model == [none] &&
      !condition.reachesReopenedLevel model [10] &&
      condition.wellFormedForEnvironments model [10] [10] &&
      !(CorrelatedHavingLeaf.numeric {
        op := .ordinary .equal, left := .atom atom, right := .literal { value := 0, authoredScale := 0 } }).wellFormedForSingleGroup
          model { level := 10, path := ["Form", "Rows"], repeatability := some 3 }) = true ∧
    !(clockCondition (.clockPart .today .utc (.time .hour))).wellFormedForEnvironments model [10] [] ∧
    !(clockCondition (.clockPart .now .europeBerlin (.date .year))).wellFormedForEnvironments model [10] [] := by native_decide

private def clockReferenceIds (filter : String) : Option (List FieldId) := do
  let parsed ← (parseText .english s!"FieldValuesNotUnique(/Form/Rows*/Tag Having [/Form/Rows/N] > 0 And {filter})").toOption
  let checked ← (lowerCondition model ["Form", "Rows"] false parsed.body).toOption
  let pointers ← (checked.core.referencePointers [(10, 2)]).toOption
  pure (pointers.map (·.field) |>.eraseDups)

example : clockComponents.all (fun (op, source, expected) =>
    (clockReferenceIds s!"{op}({source}) == {expected}").any fun fields =>
      fields.length == 2 && fields.contains 3 && fields.contains 4) = true := by native_decide

example : ["[Rows/Tag] == \"05.03.2024T03:04:05\"", "\"05.03.2024T03:04:05\" == [Rows/Tag]"].all
    (fun filter => runModel utcInstants filter false "unused" "2024-03-05T03:04:05" "2024-03-06T03:04:05" ==
      some (.fired .omission, ["value 9"])) = true := by native_decide

example : ["{Today} == Today", "Today == {Today}", "{Now} == Now", "Now == {Now}",
    "Now == \"01.01.1970T00:00:00\"", "\"01.01.1970T00:00:00\" == Now"].all
    (fun condition => runModel model ("[Rows/N] > 0 And " ++ condition) false "" "" ""
      (ruleExpected := "14") (zoneRules := ModelZone.concreteRules) ==
        some (.fired .omission, ["value 14"])) = true := by native_decide

private def clocks : FlatModel := { dates with fields := dates.fields.map fun field =>
  if field.id == 2 || field.id == 3 then { field with
    policy := { kind := .temporal .time TemporalComponents.time }
    temporalTargetPolicy := some { format := "HH:mm:ss" } } else field }

example : ["[Rows/Tag] == \"03:04:05\"", "\"03:04:05\" == [Rows/Tag]"].all (fun filter =>
    runModel clocks filter false "" "03:04:05" "04:05:06" == some (.fired .omission, ["value 9"])) = true := by native_decide

example : ["Today == Today", "Now == Now", "{Today} == {Today}", "{Now} == {Now}",
    "\"05.03.2024\" == \"05.03.2024\"", "Now == \"05.03.2024\"",
    "\"05.03.2024\" == Now", "\"03:04:05\" == Now"].all (fun condition =>
    (runModel model ("[Rows/N] > 0 And " ++ condition) false "" "" "").isNone) = true := by native_decide

private def gapFilter (literalFirst : Bool) : String :=
  if literalFirst then "\"31.03.2024T02:30:00\" < [Rows/Tag]"
  else "[Rows/Tag] > \"31.03.2024T02:30:00\""

example : [false, true].all (fun first => ["", "bad", "2024-03-05T03:04:05"].all fun value =>
    (runModel dateTimes (gapFilter first) false "" value "2024-03-05T03:04:05") ==
      some (.fired .value, [])) = true := by native_decide

example : runModel dateTimes ("[Rows/N] < 0 And " ++ gapFilter true) false "" "bad" "bad"
    (ruleExpected := "0") = some (.fired .omission, ["value 0"]) := by native_decide

example : runModel dateTimes ("[Rows/N] > 0 Or " ++ gapFilter true) false "" "bad" "bad"
    (ruleExpected := "14") = some (.fired .omission, ["value 14"]) ∧
    runModel dateTimes ("[Rows/Tag] == \"05.03.2024T03:04:05\" And " ++ gapFilter true) false "" "bad" "bad"
    (ruleExpected := "0") = some (.fired .omission, []) := by native_decide

private def gapTargetOutcome (literalFirst : Bool) (value : String) (rows : Bool := true) :
    Option NumericTargetCheckResult := do
  let dm : DmModel := { flat := dateTimes, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let input ← (readDocument dm (Json.mkObj [("Form", Json.mkObj [
    ("Rows", Json.arr (if rows then #[Json.mkObj [("Tag", Json.str value), ("N", Json.str "2")]] else #[]))])])).toOption
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler dateTimes).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  let (_, .number table _) ← (lowerComputation dateTimes .english {
    group := ["Form"], name := "Total", targetRelPath := "../Out", commonPrecondition := none,
    alternatives := [{ precondition := none, operation := "Sum(Rows*/N Having " ++ gapFilter literalFirst ++ ")" }],
    errorCodesToSuppress := [] }).toOption | none
  let addressed := checked.indexedComputationFillContext
  (table.evaluateIn {
    scalar := checked.scalarComputationContext world
    document := addressed.document
    outer := []
    filterRead := addressed.read
    starRead := addressed.read }).toOption

example : gapTargetOutcome false "" = some (.supported (.invalidNoValue .calculationValue)) ∧
    gapTargetOutcome true "bad" = some (.supported (.invalidNoValue .calculationValue)) ∧
    gapTargetOutcome false "bad" = some (.supported (.inheritedPoison .dateFormat)) := by native_decide

private def keywordTargets : FlatModel := { model with
  fields := model.fields ++ (["Date", "Time", "Datum", "Zeit"].zipIdx.map fun (name, index) =>
    { id := index + 20, groupPath := ["Form"], name,
      policy := { kind := .number { scale := 0, signed := true } } }) }

example : [Language.english, .german].all (fun language =>
    (["Date", "Time", "Datum", "Zeit"].zipIdx).all fun (name, index) =>
      ((targetOf language keywordTargets {
        group := ["Form"]
        name := "Compute"
        targetRelPath := "../" ++ name
        commonPrecondition := none
        alternatives := []
        errorCodesToSuppress := [] }).toOption.map (·.id)) == some (index + 20) &&
      (errorFieldOf language keywordTargets {
        group := ["Form"]
        name := "Validate"
        errorEntityRelPath := "../" ++ name
        condition := ""
        severity := "ERROR"
        errorCode := "E" }).toOption == some (index + 20)) = true := by native_decide

example : [("==", "9", "9"), ("!=", "5", "5"), ("<", "0", "5"),
    ("<=", "9", "14"), (">", "5", "0"), (">=", "14", "9")].all
    (fun (op, forward, reverse) =>
      [(clocks, "03:04:05", "03:04:05", "04:05:06"),
        (utcInstants, "05.03.2024T03:04:05", "2024-03-05T03:04:05", "2024-03-06T03:04:05")].all
        fun (profile, literal, first, second) =>
          runModel profile ("[Rows/Tag] " ++ op ++ " \"" ++ literal ++ "\"") false "" first second
            (ruleExpected := forward) == some (.fired .omission, ["value " ++ forward]) &&
          runModel profile ("\"" ++ literal ++ "\" " ++ op ++ " [Rows/Tag]") false "" first second
            (ruleExpected := reverse) == some (.fired .omission, ["value " ++ reverse])) = true := by native_decide

private def groupedNumericPreserved (plain grouped : String) : Bool :=
  let configured := { model with baseYear := some 2024 }
  let expected := runModel configured plain false "" "" ""
  expected.isSome && runModel configured grouped false "" "" "" == expected

example : ["==", "!=", "<", "<=", ">", ">="].all (fun op =>
    [("[Rows/N]", "{[Rows/N]}"), ("BaseYear", "{BaseYear}")].all (fun (right, groupedRight) =>
      groupedNumericPreserved s!"[Rows/N] {op} {right}" ("{[Rows/N]} " ++ op ++ " " ++ right) &&
      groupedNumericPreserved s!"[Rows/N] {op} {right}" s!"[Rows/N] {op} {groupedRight}" &&
      groupedNumericPreserved s!"{right} {op} [Rows/N]" (groupedRight ++ " " ++ op ++ " {[Rows/N]}"))) = true := by
  native_decide

example : runModel { model with timeZoneId := "Europe/Berlin" }
    "[Rows/N] > 0 Or Now > \"31.03.2024T02:30:00\"" false "" "" "" (ruleExpected := "14") =
      some (.fired .omission, ["value 14"]) ∧
    runModel { model with timeZoneId := "Europe/Berlin" }
    "Now > \"31.03.2024T02:30:00\" Or [Rows/N] > 0" false "" "" "" (ruleExpected := "14") =
      some (.fired .value, []) := by native_decide

end A12Kernel.Dm.HavingCalendarLocks
