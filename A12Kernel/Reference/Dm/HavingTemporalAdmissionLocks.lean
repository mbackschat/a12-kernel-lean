import A12Kernel.Reference.Dm.HavingFixture

namespace A12Kernel.Dm.HavingTemporalAdmissionLocks
open A12Kernel

private def model : FlatModel := { HavingFixture.model with
  baseYear := some 2024
  fields := HavingFixture.model.fields ++ [
    { id := 6, name := "RowOut", groupPath := ["Form", "Rows"], repeatableScope := [10],
      policy := { kind := .number { scale := 0, signed := true } } },
    { id := 7, name := "Stamp", groupPath := ["Form", "Rows"], repeatableScope := [10],
      policy := { kind := .temporal .dateTime .now },
      temporalTargetPolicy := some { format := "yyyy-MM-dd'T'HH:mm:ss" } },
    { id := 8, name := "Choice", groupPath := ["Form", "Rows"], repeatableScope := [10],
      policy := { kind := .enumeration }, enumeration := some {
        storedTokens := ["a"], categories := [{ name := "Label", tokens := ["b"] }] } },
    { id := 9, name := "Calendar", groupPath := ["Form", "Rows"], repeatableScope := [10],
      policy := { kind := .temporal .date .fullDate }, temporalTargetPolicy := some { format := "yyyy-MM-dd" } },
    { id := 10, name := "Span", groupPath := ["Form", "Rows"], repeatableScope := [10],
      policy := { kind := .dateRange }, dateRangePolicy := some { format := "yyyy-MM-dd", separator := "/" } },
    { id := 11, name := "Clock", groupPath := ["Form", "Rows"], repeatableScope := [10],
      policy := { kind := .temporal .time .time }, temporalTargetPolicy := some { format := "HH:mm:ss" } },
    { id := 12, name := "Part", groupPath := ["Form", "Rows"], repeatableScope := [10],
      policy := { kind := .number { scale := 0, signed := false } }, numericTargetConstraints := { maxStoredLength := some 2 } },
    { id := 13, name := "YearPart", groupPath := ["Form", "Rows"], repeatableScope := [10],
      policy := { kind := .number { scale := 0, signed := false } }, numericTargetConstraints := { maxStoredLength := some 4 } },
    { id := 14, name := "Digits", groupPath := ["Form", "Rows"], repeatableScope := [10],
      policy := { kind := .string }, stringPolicy := { maxLength := some 2 }, stringPatternSource := some "[0-9]+" }]
  repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 3, indexField := some 3 }] }

private def result (body : String) (row : Bool) (fixture : FlatModel := model) : String × String :=
  HavingFixture.readerResults ("Sum(Rows*/N Having " ++ body ++ ")") fixture row

private def parts : List String := ["YearFromDate", "QuarterFromDate", "MonthFromDate", "DayFromDate",
  "HoursFromTime", "MinutesFromTime", "SecondsFromTime"]

private def numericSources (source : String) : List String :=
  parts.map (fun part => part ++ "(" ++ source ++ ")") ++
    ["YearFromDate(DateFromDateTime(" ++ source ++ "))", "HoursFromTime(TimeFromDateTime(" ++ source ++ "))"]

example : model.validate.isOk = true := by native_decide

example : [false, true].all (fun row =>
    (numericSources "Rows/Stamp").all (fun source => result (source ++ " > 0") row == ("admitted", "admitted")) &&
    (numericSources "Rows/Stamp For \"keep\"").all (fun source =>
      result (source ++ " > 0") row == ("MVK_SEMANTIC_INDEX_NOT_ALLOWED", "MVK_SEMANTIC_INDEX_NOT_ALLOWED"))) = true := by native_decide

example : [false, true].all (fun row =>
    (numericSources "Missing").all (fun source => result (source ++ " > [AlsoMissing]") row ==
      ("MVK_INVALID_ENTITY", "MVK_INVALID_ENTITY")) &&
    (numericSources "Rows/N For \"keep\"").all (fun source => result (source ++ " > [Missing]") row ==
      ("MVK_NO_DATE", "MVK_NO_DATE")) &&
    (numericSources "Rows/N").all (fun source => result (source ++ " > 0") row ==
      ("MVK_NO_DATE", "MVK_NO_DATE"))) = true := by native_decide

example : [false, true].all (fun row =>
    parts.all (fun part =>
      result (part ++ "(\"01.03.2024\") > 0") row == ("MVK_NO_CONST", "MVK_NO_CONST") &&
      result (part ++ "(\"broken\") > 0") row == ("MVK_INVALID_DATE_STRING", "MVK_INVALID_DATE_STRING")) &&
    result "YearFromDate(DateFromDateTime(Now)) > 0 And [Rows/N] > 0" row == ("admitted", "admitted") &&
    result "HoursFromTime(TimeFromDateTime(Now)) > 0 And [Rows/N] > 0" row == ("admitted", "admitted") &&
    result "YearFromDate(DateFromDateTime(Today)) > 0" row == ("MVK_WRONG_DATE_FORMAT_FOR_OP", "MVK_WRONG_DATE_FORMAT_FOR_OP") &&
    result "YearFromDate(BaseYear) > 0" row { model with baseYear := none } ==
      ("MVK_NO_BASE_YEAR", "MVK_NO_BASE_YEAR")) = true := by native_decide

example : [false, true].all (fun row =>
    (numericSources "RuleGroup").all (fun source => result (source ++ " > 0") row ==
      ("MVK_NO_GROUPS_ALLOWED", "MVK_NO_GROUPS_ALLOWED")) &&
    (numericSources "Rows*/Stamp").all (fun source => result (source ++ " > 0") row ==
      ("MVK_NO_WILDCARDS_ALLOWED", "MVK_NO_WILDCARDS_ALLOWED")) &&
    (numericSources "Rows/Choice->Label For \"keep\"").all (fun source => result (source ++ " > [Missing]") row ==
      ("MVK_CATEGORY_NOT_ALLOWED", "MVK_CATEGORY_NOT_ALLOWED")) &&
    result "YearFromDate(YearFromDate(Rows/Stamp For \"keep\")) > [Missing]" row ==
      ("MVK_INVALID_DATE_FOR_OP", "MVK_INVALID_DATE_FOR_OP") &&
    result "YearFromDate(DateFromDateTime(\"01.03.2024T12:30:00\")) > 0 And [Rows/N] > 0" row ==
      ("admitted", "admitted") &&
    result "HoursFromTime(TimeFromDateTime(\"01.03.2024T12:30:00\")) > 0 And [Rows/N] > 0" row ==
      ("admitted", "admitted")) = true := by native_decide

private def partialModel (mode : TemporalPartialMode) : FlatModel := { model with
  fields := model.fields.map fun field =>
    if field.id == 7 then
      { field with
        policy := { kind := .temporal .date .fullDate }
        temporalTargetPolicy := some { format := "yyyy-MM-dd", partialMode := mode } }
    else field }

example : [.dayOptional, .monthOptional, .yearOptional].all
    (fun mode => (partialModel mode).validate.isOk) = true := by native_decide

example : [false, true].all (fun row =>
    [(.dayOptional, ["YearFromDate", "QuarterFromDate", "MonthFromDate"]),
     (.monthOptional, ["YearFromDate"]), (.yearOptional, [])].all (fun (mode, admitted) =>
      parts.all (fun part =>
        let expected := if admitted.contains part then "MVK_SEMANTIC_INDEX_NOT_ALLOWED" else "MVK_INVALID_DATE_TYPE"
        result (part ++ "(Rows/Stamp For \"keep\") > 0") row (partialModel mode) == (expected, expected)))) = true := by native_decide

example : [false, true].all (fun row =>
    let preceding := "AtLeastOneFieldFilled(Rows*/N Having FieldFilled(Rows/N)) And "
    (numericSources "Rows/Stamp").all (fun source =>
      let expected := if row then "MVK_DISALLOWED_CONSTRUCT_IN_FILTER_CONDITION" else "MVK_NO_WILDCARD"
      result (preceding ++ source ++ " > 0") row == (expected, expected)) &&
    (numericSources "$Rows/Stamp").all (fun source =>
      result (preceding ++ source ++ " > 0") row == ("MVK_INVALID_OUTER_ITERATION", "MVK_INVALID_OUTER_ITERATION"))) = true := by native_decide

private def units : List (String × String) := [
  ("Days", "Calendar"), ("Months", "Calendar"), ("Years", "Calendar"),
  ("Hours", "Stamp"), ("Minutes", "Stamp"), ("Seconds", "Stamp")]

example : [false, true].all (fun row => units.all (fun (unit, field) =>
    let plain := "Rows/" ++ field
    let indexed := plain ++ " For \"keep\""
    result ("YearFromDate(Add" ++ unit ++ "(" ++ plain ++ ",1)) > 0") row == ("admitted", "admitted") &&
    result ("YearFromDate(Add" ++ unit ++ "(" ++ indexed ++ ",1)) > 0") row ==
      ("MVK_SEMANTIC_INDEX_NOT_ALLOWED", "MVK_SEMANTIC_INDEX_NOT_ALLOWED") &&
    result ("DifferenceIn" ++ unit ++ "(" ++ plain ++ "," ++ plain ++ ") > 0") row == ("admitted", "admitted") &&
    result ("DifferenceIn" ++ unit ++ "(" ++ indexed ++ "," ++ plain ++ ") > 0") row ==
      ("MVK_SEMANTIC_INDEX_NOT_ALLOWED", "MVK_SEMANTIC_INDEX_NOT_ALLOWED"))) = true := by native_decide

example : [false, true].all (fun row => units.all (fun (unit, field) =>
    result ("YearFromDate(Add" ++ unit ++ "(Rows/" ++ field ++ " For \"keep\",[Missing])) > 0") row ==
      ("MVK_INVALID_ENTITY", "MVK_INVALID_ENTITY") &&
    result ("DifferenceIn" ++ unit ++ "(Rows/" ++ field ++ " For \"keep\",Missing) > 0") row ==
      ("MVK_INVALID_ENTITY", "MVK_INVALID_ENTITY") &&
    result ("YearFromDate(Add" ++ unit ++ "(Rows/N,[Missing])) > 0") row ==
      ("MVK_NO_DATE", "MVK_NO_DATE"))) = true := by native_decide

example : [false, true].all (fun row =>
    ["StartOfDateRange", "EndOfDateRange"].all (fun bound =>
      result ("YearFromDate(" ++ bound ++ "(Rows/Span)) > 0") row == ("admitted", "admitted") &&
      result ("YearFromDate(" ++ bound ++ "(Rows/Span For \"keep\")) > 0") row ==
        ("MVK_SEMANTIC_INDEX_NOT_ALLOWED", "MVK_SEMANTIC_INDEX_NOT_ALLOWED") &&
      result ("YearFromDate(" ++ bound ++ "(Rows/N For \"keep\")) > [Missing]") row ==
        ("MVK_NO_DATE_RANGE", "MVK_NO_DATE_RANGE")) &&
    result "DifferenceInDays(StartOfDateRange(Rows/Span For \"keep\"),EndOfDateRange(Rows/Span)) > 0" row ==
      ("MVK_SEMANTIC_INDEX_NOT_ALLOWED", "MVK_SEMANTIC_INDEX_NOT_ALLOWED") &&
    result "YearFromDate(AddDays(StartOfDateRange(Rows/Span For \"keep\"),1)) > 0" row ==
      ("MVK_SEMANTIC_INDEX_NOT_ALLOWED", "MVK_SEMANTIC_INDEX_NOT_ALLOWED")) = true := by native_decide

example : [false, true].all (fun row =>
    result "YearFromDate(AddDays(Rows/Stamp,[Missing])) > 0" row (partialModel .dayOptional) ==
      ("MVK_INVALID_ENTITY", "MVK_INVALID_ENTITY") &&
    result "DifferenceInDays(Rows/Stamp,Missing) > 0" row (partialModel .dayOptional) ==
      ("MVK_INVALID_ENTITY", "MVK_INVALID_ENTITY") &&
    result "YearFromDate(AddDays(Rows/Stamp,1)) > 0" row (partialModel .dayOptional) ==
      ("MVK_INVALID_DATE_TYPE", "MVK_INVALID_DATE_TYPE") &&
    result "YearFromDate(AddDays(ValueAsDate(Rows/Stamp,FirstDay),1)) > 0" row (partialModel .dayOptional) ==
      ("admitted", "admitted") &&
    result "YearFromDate(AddDays(ValueAsDate(Rows/Stamp For \"keep\",LastDay),1)) > 0" row (partialModel .dayOptional) ==
      ("MVK_SEMANTIC_INDEX_NOT_ALLOWED", "MVK_SEMANTIC_INDEX_NOT_ALLOWED") &&
    result "YearFromDate(AddDays(ValueAsDate(Rows/Calendar,FirstDay),[Missing])) > 0" row ==
      ("MVK_INVALID_DATE_TYPE_FOR_OP", "MVK_INVALID_DATE_TYPE_FOR_OP")) = true := by native_decide

private def arithmeticRefusals : List (String × String) := [
  ("YearFromDate(AddDays(Rows/Calendar,\"x\")) > 0", "MVK_NON_NUMERIC"),
  ("YearFromDate(AddDays(Rows/Calendar,Now)) > 0", "MVK_NON_NUMERIC"),
  ("YearFromDate(AddDays(Rows/Calendar,\"01.03.2024\")) > 0", "MVK_NON_NUMERIC"),
  ("YearFromDate(AddMonths(Rows/Stamp,\"x\")) > 0", "MVK_WRONG_DATE_FORMAT_FOR_OP"),
  ("YearFromDate(AddHours(Rows/Calendar,1)) > 0", "MVK_WRONG_DATE_FORMAT_FOR_OP"),
  ("HoursFromTime(AddHours(Rows/Clock,1)) > 0", "MVK_INVALID_TIME"),
  ("YearFromDate(AddYears(Rows/Clock,1)) > 0", "MVK_INVALID_TIME"),
  ("DifferenceInHours(Rows/Clock,Rows/Clock) > 0", "MVK_INVALID_TIME"),
  ("DifferenceInMonths(Rows/Calendar,Rows/Stamp) > 0", "MVK_WRONG_DATE_FORMAT_FOR_OP"),
  ("DifferenceInDays(YearFromDate(Rows/Stamp),Missing) > 0", "MVK_INVALID_DATE_FOR_OP"),
  ("DifferenceInDays(AddMonths(Rows/Stamp,1),Missing) > 0", "MVK_WRONG_DATE_FORMAT_FOR_OP")]

example : [false, true].all (fun row => arithmeticRefusals.all (fun (body, expected) =>
    result body row == (expected, expected))) = true := by native_decide

example : [false, true].all (fun row =>
    result "DifferenceInDays(Rows/Clock,Rows/Stamp) > 0" row (partialModel .dayOptional) ==
      ("MVK_INVALID_DATE_TYPE", "MVK_INVALID_DATE_TYPE") &&
    result "YearFromDate(AddDays(Rows/Stamp,[Rows/N]+\"x\")) > 0" row (partialModel .dayOptional) ==
      ("MVK_NO_STRING_OR_NUMBER_FOR_ADD", "MVK_NO_STRING_OR_NUMBER_FOR_ADD") &&
    result "DifferenceInDays(Rows/Calendar,\"01.03.\") > 0" row { model with baseYear := none } ==
      ("MVK_DATE_WITH_AND_WITHOUT_YEAR", "MVK_DATE_WITH_AND_WITHOUT_YEAR") &&
    result "DifferenceInDays(Rows/Calendar,\"01.03.\") > 0" row == ("admitted", "admitted") &&
    result "YearFromDate(AddDays(Rows/Calendar,YearFromDate(Now))) > 0" row == ("admitted", "admitted")) = true := by native_decide

example : [false, true].all (fun row =>
    ["StartOfDateRange", "EndOfDateRange"].all (fun bound =>
      result ("YearFromDate(" ++ bound ++ "(RuleGroup)) > 0") row ==
        ("MVK_NO_GROUPS_ALLOWED", "MVK_NO_GROUPS_ALLOWED") &&
      result ("YearFromDate(" ++ bound ++ "(Rows*/Span)) > 0") row ==
        ("MVK_NO_WILDCARDS_ALLOWED", "MVK_NO_WILDCARDS_ALLOWED") &&
      result ("YearFromDate(" ++ bound ++ "(Rows/Choice->Label)) > 0") row ==
        ("MVK_CATEGORY_NOT_ALLOWED", "MVK_CATEGORY_NOT_ALLOWED") &&
      result ("YearFromDate(" ++ bound ++ "(BaseYear)) > 0") row { model with baseYear := none } ==
        ("MVK_NO_BASE_YEAR", "MVK_NO_BASE_YEAR"))) = true := by native_decide

example : [false, true].all (fun row =>
    let preceding := "AtLeastOneFieldFilled(Rows*/N Having FieldFilled(Rows/N)) And "
    let expected := if row then "MVK_DISALLOWED_CONSTRUCT_IN_FILTER_CONDITION" else "MVK_NO_WILDCARD"
    units.all (fun (unit, field) =>
      result (preceding ++ "YearFromDate(Add" ++ unit ++ "(Rows/" ++ field ++ ",1)) > 0") row == (expected, expected) &&
      result (preceding ++ "DifferenceIn" ++ unit ++ "(Rows/" ++ field ++ ",Rows/" ++ field ++ ") > 0") row == (expected, expected)) &&
    result "YearFromDate(AddDays(Rows/Calendar,Sum(Rows*/N Having FieldFilled(Rows/N))+[Rows/N])) > 0" row ==
      (expected, expected)) = true := by native_decide

example : [false, true].all (fun row => units.all (fun (unit, field) =>
    result ("Add" ++ unit ++ "(Rows/" ++ field ++ ",1) == [Rows/" ++ field ++ "]") row == ("admitted", "admitted") &&
    result ("Add" ++ unit ++ "(Rows/" ++ field ++ " For \"keep\",1) == [Rows/" ++ field ++ "]") row ==
      ("MVK_SEMANTIC_INDEX_NOT_ALLOWED", "MVK_SEMANTIC_INDEX_NOT_ALLOWED"))) = true := by native_decide

example : [false, true].all (fun row =>
    ["DateFromDateTime(Rows/Stamp For \"keep\") == Today",
     "TimeFromDateTime(Rows/Stamp For \"keep\") == \"12:30:00\"",
     "StartOfDateRange(Rows/Span For \"keep\") == [Rows/Calendar]",
     "AddDays(Rows/Stamp For \"keep\",1) > Today",
     "AddDays(Rows/Calendar For \"keep\",1) == BaseYear",
     "{BaseYear} < AddDays(Rows/Calendar For \"keep\",1)"].all (fun body =>
      result body row == ("MVK_SEMANTIC_INDEX_NOT_ALLOWED", "MVK_SEMANTIC_INDEX_NOT_ALLOWED")) &&
    ["AddDays(Rows/Stamp For \"keep\",1) == Today",
     "AddDays(Rows/Calendar For \"keep\",1) > [Rows/Clock]",
     "AddDays(Rows/Calendar For \"keep\",1) == \"x\"",
     "AddDays(Rows/Calendar For \"keep\",1) == BaseYear + 1",
     "TimeFromDateTime(Rows/Stamp For \"keep\") == BaseYear"].all (fun body =>
      result body row == ("MVK_INVALID_COMPARE_TO_DATE", "MVK_INVALID_COMPARE_TO_DATE"))) = true := by native_decide

private def constructors (index : String) : List String := [
  "Date(Rows/Part" ++ index ++ ",\"03\",\"2024\") == \"01.03.2024\"",
  "Date(\"01\",\"03\",Rows/YearPart" ++ index ++ ") == \"01.03.2024\"",
  "Date(\"01\",\"03\",Rows/Part" ++ index ++ ",\"24\") == \"01.03.2024\"",
  "Time(Rows/Part" ++ index ++ ") == \"08:00:00\"",
  "Time(Rows/Digits" ++ index ++ ",\"30\") == \"08:30:00\"",
  "DateTime(Rows/Calendar" ++ index ++ ",Rows/Clock) == Now",
  "DateTime(Rows/Calendar,Rows/Clock" ++ index ++ ") == Now",
  "Date(DayFromDate(Rows/Stamp" ++ index ++ "),\"03\",\"2024\") == Today",
  "Time(HoursFromTime(Rows/Stamp" ++ index ++ ")) == \"08:00:00\""]

example : [false, true].all (fun row =>
    (constructors "").all (fun body => result body row == ("admitted", "admitted")) &&
    (constructors " For \"keep\"").all (fun body => result body row ==
      ("MVK_SEMANTIC_INDEX_NOT_ALLOWED", "MVK_SEMANTIC_INDEX_NOT_ALLOWED"))) = true := by native_decide

example : [false, true].all (fun row =>
    ["Time(Rows/N,Missing) == \"08:00:00\"",
     "Time(Rows/Tag,Missing) == \"08:00:00\"",
     "Date(Rows/N,Missing,\"2024\") == Today",
     "DateTime(Rows/Stamp,Missing) == Now",
     "Date(MonthFromDate(Rows/Stamp For \"keep\"),Missing,\"2024\") == Today"].all (fun body =>
      result body row == ("MVK_INVALID_ENTITY", "MVK_INVALID_ENTITY")) &&
    result "Time(HoursFromTime(Rows/N),Missing) == \"08:00:00\"" row == ("MVK_NO_DATE", "MVK_NO_DATE")) = true := by native_decide

example : [false, true].all (fun row =>
    result "Time() == \"00:00:00\" And [Rows/N] > 0" row == ("admitted", "admitted") &&
    result "Date(\"01\",\"03\") == Today And [Rows/N] > 0" row == ("admitted", "admitted") &&
    result "Date(\"01\",\"03\") == Today And [Rows/N] > 0" row { model with baseYear := none } ==
      ("MVK_MISSING_YEAR", "MVK_MISSING_YEAR") &&
    result "DateTime(Date(\"01\",\"03\",\"2024\"),Time(Rows/Part For \"keep\")) == Now" row ==
      ("MVK_SEMANTIC_INDEX_NOT_ALLOWED", "MVK_SEMANTIC_INDEX_NOT_ALLOWED")) = true := by native_decide


private def constructorRefusals : List (String × String) := [
  ("Time(Rows/N For \"keep\") == \"08:00:00\"", "MVK_WRONG_DATE_FORMAT_FOR_OP"),
  ("Time(Rows/Tag For \"keep\") == \"08:00:00\"", "MVK_NO_DIGIT_PATTERN"),
  ("Time(Rows*/Digits) == \"08:00:00\"", "MVK_NO_WILDCARDS_ALLOWED"),
  ("Time(Rows) == \"08:00:00\"", "MVK_NO_GROUPS_ALLOWED"),
  ("Date(RuleGroup,\"03\",\"2024\") == Today", "MVK_NO_GROUPS_ALLOWED"),
  ("Time(Rows/Choice->Label For \"keep\") == \"08:00:00\"", "MVK_CATEGORY_NOT_ALLOWED"),
  ("Time(Rows/Choice For \"keep\") == \"08:00:00\"", "MVK_WRONG_DATE_FORMAT_FOR_OP"),
  ("Date(MonthFromDate(Rows/Stamp For \"keep\"),\"03\",\"2024\") == Today", "MVK_INVALID_DATE_OR_TIME_EXTRACT_OP"),
  ("Time(MinutesFromTime(Rows/Stamp For \"keep\")) == \"08:00:00\"", "MVK_INVALID_DATE_OR_TIME_EXTRACT_OP"),
  ("Date(QuarterFromDate(Rows/Stamp For \"keep\"),\"03\",\"2024\") == Today", "MVK_DATE_OR_TIME_EXTRACT_OP_NOT_ALLOWED"),
  ("Time(DayFromDate(Rows/Stamp For \"keep\")) == \"08:00:00\"", "MVK_DATE_OR_TIME_EXTRACT_OP_NOT_ALLOWED"),
  ("Time(TimeFromDateTime(Rows/Stamp For \"keep\")) == \"08:00:00\"", "MVK_DATE_OR_TIME_EXTRACT_OP_NOT_ALLOWED"),
  ("Date(\"01\",\"03\",YearFromDate(Rows/Stamp For \"keep\"),\"24\") == Today", "MVK_EXTRACT_OP_NOT_ALLOWED_4_DATE_CONSTRUCT_WITH_4_PARAMS"),
  ("Date(\"01\",\"03\",\"20\",YearFromDate(Rows/Stamp For \"keep\")) == Today", "MVK_EXTRACT_OP_NOT_ALLOWED_4_DATE_CONSTRUCT_WITH_4_PARAMS"),
  ("DateTime(Rows/Stamp For \"keep\",Rows/Clock) == Now", "MVK_WRONG_DATE_FORMAT_FOR_OP"),
  ("DateTime(Rows/Calendar,Rows/Calendar For \"keep\") == Now", "MVK_WRONG_DATE_FORMAT_FOR_OP"),
  ("DateTime(DayFromDate(Rows/Stamp For \"keep\"),Missing) == Now", "MVK_INVALID_DATE_FOR_OP"),
  ("Date(\"00\",Rows/Part For \"keep\",\"2024\") == Today", "MVK_WRONG_DATE_FORMAT_FOR_OP"),
  ("Time(\"24\",Rows/Part For \"keep\") == \"08:00:00\"", "MVK_WRONG_DATE_FORMAT_FOR_OP")]

example : [false, true].all (fun row => constructorRefusals.all (fun (body, expected) =>
    result body row == (expected, expected))) = true := by native_decide

example : [false, true].all (fun row =>
    result "DateTime(Rows/Stamp,Rows/Calendar) == Now" row (partialModel .dayOptional) ==
      ("MVK_INVALID_DATE_TYPE", "MVK_INVALID_DATE_TYPE") &&
    result "DateTime(Rows/Stamp,Missing) == Now" row (partialModel .dayOptional) ==
      ("MVK_INVALID_ENTITY", "MVK_INVALID_ENTITY") &&
    result "DateTime(ValueAsDate(Rows/Stamp,FirstDay),Rows/Clock) == Now" row (partialModel .dayOptional) ==
      ("admitted", "admitted") &&
    result "DateTime(ValueAsDate(Rows/Stamp For \"keep\",LastDay),Rows/Clock) == Now" row (partialModel .dayOptional) ==
      ("MVK_SEMANTIC_INDEX_NOT_ALLOWED", "MVK_SEMANTIC_INDEX_NOT_ALLOWED")) = true := by native_decide

private def constructorExitCases (row : Bool) : List (String × String) :=
  let preceding := "AtLeastOneFieldFilled(Rows*/N Having FieldFilled(Rows/N)) And "
  let expected := if row then "MVK_DISALLOWED_CONSTRUCT_IN_FILTER_CONDITION" else "MVK_NO_WILDCARD"
  (constructors "").map (fun body => (preceding ++ body, expected)) ++ [
    (preceding ++ "Time($Rows/Part) == \"08:00:00\"", "MVK_INVALID_OUTER_ITERATION"),
    ("Time(HoursFromTime(AddHours(Rows/Stamp,Sum(Rows*/N Having FieldFilled(Rows/N)))),Rows/Part) == \"08:00:00\"", expected),
    ("DateTime(AddDays(Rows/Calendar,Sum(Rows*/N Having FieldFilled(Rows/N))),Rows/Clock) == Now", expected),
    ("DateTime(Rows/Calendar,TimeFromDateTime(AddHours(Rows/Stamp,Sum(Rows*/N Having FieldFilled(Rows/N))))) == Now And [Rows/N] > 0", expected)]

example : [false, true].all (fun row => (constructorExitCases row).all (fun (body, expected) =>
    result body row == (expected, expected))) = true := by native_decide

private def digitModel (width : Nat) (pattern : String) (extensible : Bool := false) : FlatModel :=
  { model with fields := model.fields.map fun field => if field.id == 14 then
      { field with
        stringPolicy := { maxLength := some width }
        stringPatternSource := some pattern
        stringExtensibleEnum := extensible } else field }

example : [(2,"[0-9]{2}",false), (3,"[0-9]{3}",false), (3,"[0-9]{2}",false),
    (2,"x",true)].all (fun (width, pattern, extensible) => (digitModel width pattern extensible).validate.isOk) = true := by native_decide

example : [false, true].all (fun row =>
    result "Time(Rows/Digits) == \"08:00:00\"" row (digitModel 2 "[0-9]{2}") == ("admitted", "admitted") &&
    result "Time(Rows/Digits) == \"08:00:00\"" row (digitModel 2 "x" true) == ("admitted", "admitted") &&
    [(3,"[0-9]{3}","MVK_WRONG_DATE_FORMAT_FOR_OP"),
     (3,"[0-9]{2}","MVK_NO_DIGIT_PATTERN"),
     (2,"[0-9]{2}","MVK_SEMANTIC_INDEX_NOT_ALLOWED")].all (fun (width, pattern, expected) =>
      result "Time(Rows/Digits For \"keep\") == \"08:00:00\"" row (digitModel width pattern) == (expected, expected)) &&
    result "Time(Rows/Digits,Missing) == \"08:00:00\"" row (digitModel 3 "[0-9]{2}") ==
      ("MVK_INVALID_ENTITY", "MVK_INVALID_ENTITY")) = true := by native_decide


private def rangeModel : FlatModel := { model with fields := model.fields ++ [
  { id := 15, name := "MonthDay", groupPath := ["Form", "Rows"], repeatableScope := [10],
    policy := { kind := .temporal .date (TemporalComponents.ofFormat "MM-dd") },
    temporalTargetPolicy := some { format := "MM-dd" } },
  { id := 16, name := "ShortSpan", groupPath := ["Form", "Rows"], repeatableScope := [10],
    policy := { kind := .dateRange }, dateRangePolicy := some { format := "MM-dd", separator := "/" } },
  { id := 17, name := "OtherSpan", groupPath := ["Form", "Rows"], repeatableScope := [10],
    policy := { kind := .dateRange }, dateRangePolicy := some { format := "yyyy-MM-dd", separator := "/" } },
  { id := 18, name := "Flag", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .boolean } }] }

example : rangeModel.validate.isOk = true := by native_decide

example : [false, true].all (fun row =>
    ["DateRange(Rows/Calendar,Rows/Calendar) == [Rows/Span]",
     "DateRange(Rows/Calendar,Rows/Calendar) != DateRange(Rows/Calendar,Rows/Calendar)",
     "DateRange(Rows/MonthDay,Rows/MonthDay) == [Rows/ShortSpan]",
     "Valid(Date(Rows/Part,\"03\",\"2024\"))", "Invalid(Date(Rows/Part,\"03\",\"2024\"))"].all fun body =>
       result body row rangeModel == ("admitted", "admitted")) = true := by native_decide

private def rangeAndValidityCases : List (String × String) := [
  ("DateRange(Rows/Calendar For \"keep\",Rows/Calendar) == [Rows/Span]", "MVK_SEMANTIC_INDEX_NOT_ALLOWED"),
  ("{DateRange(Rows/Calendar,Rows/Calendar For \"keep\")} == [Rows/Span]", "MVK_SEMANTIC_INDEX_NOT_ALLOWED"),
  ("[Rows/Span For \"keep\"] == DateRange(Rows/Calendar,Rows/Calendar)", "MVK_SEMANTIC_INDEX_NOT_ALLOWED"),
  ("[Rows/Span For \"keep\"] == [Rows/OtherSpan]", "MVK_SEMANTIC_INDEX_NOT_ALLOWED"),
  ("FirstFilledValue(Rows/Span For \"keep\",Rows/OtherSpan) == [Rows/Span]", "MVK_SEMANTIC_INDEX_NOT_ALLOWED"),
  ("DateRange(Rows/Calendar For \"keep\",Rows/MonthDay) == [Rows/Span]", "MVK_WRONG_DATE_FORMAT_FOR_OP"),
  ("DateRange(Rows/Calendar For \"keep\",Rows/Calendar) == [Rows/ShortSpan]", "MVK_INVALID_COMPARE_TO_DATE_RANGE"),
  ("[Rows/ShortSpan] == DateRange(Rows/Calendar For \"keep\",Rows/Calendar)", "MVK_INVALID_COMPARE_TO_DATE_RANGE"),
  ("DateRange(Rows/Calendar For \"keep\",Rows/Calendar) > [Rows/Span]", "MVK_INVALID_TYPE_FOR_COMPARISON"),
  ("DateRange(Rows/Calendar For \"keep\",Rows/Calendar) == [Rows/N]", "MVK_INVALID_COMPARE_TO_DATE_RANGE"),
  ("DateRange(Rows/Calendar For \"keep\",Rows/Calendar) == [Rows/Flag]", "MVK_INVALID_COMPARE_TO_YESNO"),
  ("DateRange(Rows/Calendar For \"keep\",Rows/Calendar) == Today", "MVK_INVALID_COMPARE_TO_DATE"),
  ("DateRange(Rows/N For \"keep\",Missing) == [Rows/Span]", "MVK_INVALID_ENTITY"),
  ("DateRange(Rows/N For \"keep\",Rows/Calendar) == [Missing]", "MVK_WRONG_DATE_FORMAT_FOR_OP"),
  ("DateRange(Rows*/Calendar,Rows/Calendar For \"keep\") == [Rows/Span]", "MVK_NO_WILDCARDS_ALLOWED"),
  ("DateRange(Rows For \"keep\",Rows/Calendar) == [Rows/Span]", "MVK_NO_GROUPS_ALLOWED")]

example : [false, true].all (fun row => rangeAndValidityCases.all fun (body, diagnostic) =>
    result body row rangeModel == (diagnostic, diagnostic)) = true := by native_decide

example : [false, true].all (fun row => ["Valid", "Invalid"].all fun op =>
    [("Date(Rows/Part For \"keep\",\"03\",\"2024\")", "MVK_SEMANTIC_INDEX_NOT_ALLOWED"),
     ("Date(\"01\",\"03\",YearFromDate(Rows/Calendar For \"keep\"))", "MVK_ONLY_CONSTANTS_USED"),
     ("Date(\"01\",\"03\",\"2024\")", "MVK_ONLY_CONSTANTS_USED"),
     ("Date(Rows/Part For \"keep\",Missing,\"2024\")", "MVK_INVALID_ENTITY"),
     ("Date(Rows/Part For \"keep\",\"00\",\"2024\")", "MVK_WRONG_DATE_FORMAT_FOR_OP")].all fun (source, diagnostic) =>
       result (op ++ "(" ++ source ++ ")") row rangeModel == (diagnostic, diagnostic)) = true := by native_decide

example : [false, true].all (fun row =>
    let preceding := "AtLeastOneFieldFilled(Rows*/N Having FieldFilled(Rows/N)) And "
    ["DateRange(Rows/Calendar,Rows/Calendar) == [Rows/Span]",
      "Valid(Date(Rows/Part,\"03\",\"2024\"))", "Invalid(Date(Rows/Part,\"03\",\"2024\"))"].all (fun body =>
        result (preceding ++ body) row rangeModel ==
          (if row then ("MVK_DISALLOWED_CONSTRUCT_IN_FILTER_CONDITION", "MVK_DISALLOWED_CONSTRUCT_IN_FILTER_CONDITION")
           else ("MVK_NO_WILDCARD", "MVK_NO_WILDCARD"))) &&
    ["DateRange($Rows/Calendar,Rows/Calendar) == [Rows/Span]",
      "Valid(Date($Rows/Part,\"03\",\"2024\"))", "Invalid(Date($Rows/Part,\"03\",\"2024\"))"].all (fun body =>
        result (preceding ++ body) row rangeModel == ("MVK_INVALID_OUTER_ITERATION", "MVK_INVALID_OUTER_ITERATION"))) = true := by native_decide

example : [false, true].all (fun row =>
    ["DateRange(Rows*/Calendar Having FieldFilled(Rows/N),Rows/Calendar) == [Rows/Span]",
      "Valid(Date(Rows*/Part Having FieldFilled(Rows/N),Rows/Part,\"2024\"))"].all fun body =>
        result body row rangeModel ==
          (if row then ("MVK_NO_WILDCARDS_ALLOWED", "MVK_NO_WILDCARDS_ALLOWED")
           else ("MVK_NO_WILDCARD", "MVK_NO_WILDCARD"))) = true := by native_decide

private def partialRangeModel : FlatModel := { rangeModel with fields := rangeModel.fields.map fun field =>
  if field.id == 9 then { field with temporalTargetPolicy := some { format := "yyyy-MM-dd", partialMode := .dayOptional } }
  else field }

example : partialRangeModel.validate.isOk = true ∧ [false, true].all (fun row =>
    result "DateRange(Rows/Calendar For \"keep\",Missing) == [Rows/Span]" row partialRangeModel ==
      ("MVK_INVALID_ENTITY", "MVK_INVALID_ENTITY") &&
    result "DateRange(Rows/Calendar For \"keep\",Rows/Calendar) == [Rows/Span]" row partialRangeModel ==
      ("MVK_WRONG_DATE_FORMAT_FOR_OP", "MVK_WRONG_DATE_FORMAT_FOR_OP")) = true := by native_decide

example : [false, true].all (fun row => [none, some 2024].all fun year =>
    result "DateRange(Rows/MonthDay For \"keep\",Rows/MonthDay) == [Rows/ShortSpan]" row { rangeModel with baseYear := year } ==
      ("MVK_SEMANTIC_INDEX_NOT_ALLOWED", "MVK_SEMANTIC_INDEX_NOT_ALLOWED") &&
    result "DateRange(Rows/Calendar,Rows/MonthDay For \"keep\") == [Rows/Span]" row { rangeModel with baseYear := year } ==
      ("MVK_WRONG_DATE_FORMAT_FOR_OP", "MVK_WRONG_DATE_FORMAT_FOR_OP") &&
    result "DateRange(Rows/MonthDay For \"keep\",Rows/MonthDay) == [Rows/Span]" row { rangeModel with baseYear := year } ==
      ("MVK_INVALID_COMPARE_TO_DATE_RANGE", "MVK_INVALID_COMPARE_TO_DATE_RANGE")) = true := by native_decide

example : [false, true].all (fun row =>
    ["DateRange(Rows/Calendar For \"keep\",Rows/Calendar) == [Rows/Span]",
      "Valid(Date(Rows/Part For \"keep\",\"03\",\"2024\"))"].all fun body =>
        result (body ++ " And FieldFilled(Missing)") row rangeModel == ("MVK_INVALID_ENTITY", "MVK_INVALID_ENTITY")) = true := by native_decide

example : [false, true].all (fun row =>
    result "[Rows/Calendar For \"keep\"] == [Missing]" row partialRangeModel ==
      (KernelStaticDiagnostic.invalidDateType.kernelCode, KernelStaticDiagnostic.invalidDateType.kernelCode)) = true := by native_decide

private def grammarModel : FlatModel := { model with fields := model.fields ++ [
  { id := 15, name := "RootStamp", groupPath := ["Form"], policy := { kind := .temporal .dateTime .now },
    temporalTargetPolicy := some { format := "yyyy-MM-dd'T'HH:mm:ss" } }] }

private def grammarResults (operation : String) (filtered : Bool) : String × String :=
  HavingFixture.readerResults
    (if filtered then "Sum(Rows*/N Having FieldFilled(Rows/N) And " ++ operation ++ " > 0)" else operation)
    grammarModel false

private def componentSlots : List (String × String × String) := [
  ("YearFromDate(Date(", ",\"01\",\"2024\"))", "\"01\""),
  ("YearFromDate(Date(\"01\",", ",\"2024\"))", "\"01\""),
  ("YearFromDate(Date(\"01\",\"01\",", "))", "\"2024\""),
  ("YearFromDate(Date(\"01\",\"01\",", ",\"24\"))", "\"20\""),
  ("YearFromDate(Date(\"01\",\"01\",\"20\",", "))", "\"24\""),
  ("HoursFromTime(Time(", "))", "\"01\""),
  ("HoursFromTime(Time(\"01\",", "))", "\"01\""),
  ("HoursFromTime(Time(\"01\",\"01\",", "))", "\"01\"")]

private def nonComponents : List String := [
  "Sum(Rows*/N)", "MaxValue(Rows*/N)", "RoundUp([Out],0)",
  "Date(\"01\",\"01\",\"2024\")", "Time(\"01\")", "[Out]", "{[Out]}", "[Out]+1",
  "1.5", "-1", "True", "Today"]

-- KF532 separates datumParam grammar from numeric expression lowering across every component slot.
example : [false, true].all (fun filtered => componentSlots.all (fun (beforeText, afterText, control) =>
    grammarResults (beforeText ++ control ++ afterText) filtered == ("admitted", "admitted") &&
    nonComponents.all (fun component => grammarResults (beforeText ++ component ++ afterText) filtered ==
      ("MVK_UNEXPECTED_TOKEN", "MVK_UNEXPECTED_TOKEN")) &&
    grammarResults (beforeText ++ "1" ++ afterText) filtered == ("MVK_INVALID_ENTITY", "MVK_INVALID_ENTITY"))) = true := by native_decide

private def constructorPrecedence : List (String × String) := [
  ("HoursFromTime(Time(1,Sum(Rows*/N)))", "MVK_INVALID_ENTITY"),
  ("HoursFromTime(Time(Sum(Rows*/N),1))", "MVK_UNEXPECTED_TOKEN"),
  ("HoursFromTime(Time(MinutesFromTime(RootStamp),Sum(Rows*/N)))", "MVK_UNEXPECTED_TOKEN"),
  ("HoursFromTime(Time(Sum(Rows*/N),MinutesFromTime(RootStamp)))", "MVK_UNEXPECTED_TOKEN"),
  ("YearFromDate(Date(DateFromDateTime(RootStamp),\"01\",Sum(Rows*/N)))", "MVK_UNEXPECTED_TOKEN"),
  ("YearFromDate(Date(Sum(Rows*/N),\"01\",DateFromDateTime(RootStamp)))", "MVK_UNEXPECTED_TOKEN"),
  ("HoursFromTime(Time(MinutesFromTime(RootStamp),Missing))", "MVK_INVALID_ENTITY"),
  ("HoursFromTime(Time(HoursFromTime(Out),Missing))", "MVK_NO_DATE"),
  ("YearFromDate(Date(\"01\",\"01\",DateFromDateTime(RootStamp),\"24\"))", "MVK_EXTRACT_OP_NOT_ALLOWED_4_DATE_CONSTRUCT_WITH_4_PARAMS"),
  ("YearFromDate(Date(\"01\",\"01\",\"01\",\"24\"))", "MVK_WRONG_DATE_FORMAT_FOR_OP"),
  ("YearFromDate(Date(\"01\",\"01\",\"20\",\"1\"))", "MVK_WRONG_DATE_FORMAT_FOR_OP")]


example : [false, true].all (fun filtered => constructorPrecedence.all (fun (operation, expected) =>
    grammarResults operation filtered == (expected, expected))) = true := by native_decide

private def digitNameModel : FlatModel := { grammarModel with fields := grammarModel.fields ++ [
  { id := 16, name := "1", groupPath := ["Form"], policy := { kind := .number { scale := 0, signed := false } },
    numericTargetConstraints := { maxStoredLength := some 2 } }] }

example : (digitNameModel.validate.isOk &&
    HavingFixture.readerResults "HoursFromTime(Time(1))" digitNameModel false == ("admitted", "admitted") &&
    HavingFixture.readerResults "YearFromDate(Date(1,\"01\",\"2024\"))" digitNameModel false == ("admitted", "admitted")) = true := by native_decide

-- KF531's selected String components must survive the shared grammar gate and read the selected row.
example : (["DayFromDate(Date(Rows/Digits For Expected,\"01\",\"2024\"))",
    "HoursFromTime(Time(Rows/Digits For Expected))"].all fun operation =>
    HavingFixture.runModel model "[Rows/N] > 0" false "keep" "drop" "keep"
      (operationOverride := some operation) (ruleExpected := "7")
      (rowsOverride := some #[
        Lean.Json.mkObj [("Tag", .str "drop"), ("Digits", .str "03"), ("N", .str "1")],
        Lean.Json.mkObj [("Tag", .str "keep"), ("Digits", .str "07"), ("N", .str "1")]]) ==
      some (.fired .value, ["value 7"])) = true := by native_decide

private def temporalExtremumResults (operator : String) (baseYear : Option Int) : String × String :=
  let fixture : FlatModel := { model with baseYear, fields := model.fields ++ [
    { id := 15, name := "DateOut", groupPath := ["Form"], policy := { kind := .temporal .date .fullDate },
      temporalTargetPolicy := some { format := "yyyy-MM-dd" } }] }
  let dm : DmModel := { flat := fixture, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let operation := operator ++ "(Date(Rows/Part For Expected,Rows/Part For Expected),\"15.02.2024\")"
  let report {α : Type} : Lowering α → String
    | .ok _ => "admitted"
    | .error refusal => refusal.detail
  (report (checkRule dm .english {
    group := ["Form"], name := "Extremum", errorCode := "EXTREMUM",
    errorEntityRelPath := "../Error", condition := "FieldFilled(Error) And " ++ operation ++ " == Today", severity := "ERROR" }),
   report (lowerComputation fixture .english {
    group := ["Form"], name := "Extremum", targetRelPath := "../DateOut",
    commonPrecondition := none, alternatives := [{ precondition := none, operation }], errorCodesToSuppress := [] }))

-- The date-components/date-validity captures admit the omitted-year constructor under scalar Min;
-- CheckFeldListenOperOpImpl uses the same model-aware temporal comparison for Max.
example : (["Min", "Max"].all fun operator =>
    temporalExtremumResults operator (some 2024) == ("admitted", "admitted") &&
    temporalExtremumResults operator none == ("MVK_MISSING_YEAR", "MVK_MISSING_YEAR")) = true := by native_decide

end A12Kernel.Dm.HavingTemporalAdmissionLocks
