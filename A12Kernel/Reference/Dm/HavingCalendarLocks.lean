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

end A12Kernel.Dm.HavingCalendarLocks
