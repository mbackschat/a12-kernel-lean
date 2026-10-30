import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Document
import A12Kernel.Reference.Dm.Replay

namespace A12Kernel.Dm.CalendarExpressionLocks

private def model : FlatModel := {
  fields := [
    { id := 0, groupPath := ["Form"], name := "D", policy := { kind := .temporal .date TemporalComponents.fullDate },
      temporalTargetPolicy := some { format := "yyyy-MM-dd" } },
    { id := 1, groupPath := ["Form"], name := "N", policy := { kind := .number { scale := 0, signed := true } } },
    { id := 2, groupPath := ["Form"], name := "Result", policy := { kind := .temporal .date TemporalComponents.fullDate },
      temporalTargetPolicy := some { format := "yyyy-MM-dd" } }]
  timeZoneId := "Europe/Berlin", baseYear := some 2024 }

private def admittedIn (model : FlatModel) (operation : String) : Bool :=
  (lowerComputation model .english {
    group := ["Form"], name := "ResultComp", targetRelPath := "../Result"
    commonPrecondition := none, alternatives := [{ precondition := none, operation }]
    errorCodesToSuppress := [] }).isOk

private def admitted := admittedIn model

example : admitted "[D]" = true := by native_decide

-- The calendar-family admission grid keeps the source forms legal across all three units.
example :
    ["AddDays(D,[N])", "AddMonths(D,[N])", "AddYears(D,[N])",
      "AddDays(Today,1)", "AddMonths(Today,1)", "AddYears(Today,1)",
      "Date(DayFromDate(D),MonthFromDate(D),YearFromDate(D))", "Date(\"29\",\"02\",\"20\",\"24\")",
      "AddDays(AddMonths(D,[N]),1)", "AddMonths(AddDays(D,1),[N])"].all admitted = true := by
  native_decide

private def fragmentModel (format : String) (components : TemporalComponents)
    (baseYear : Option Int) : FlatModel :=
  { model with baseYear, fields := model.fields.map fun field =>
      if field.id == 1 then field else { field with
        policy := { kind := .temporal .date components }
        temporalTargetPolicy := some { format } } }

-- The 24 retained static rows cross declared components, calendar unit and Base Year.
example :
    [("yyyy-MM", { TemporalComponents.fullDate with day := false }, [false, true, true]),
     ("MM-dd", { TemporalComponents.fullDate with year := false }, [true, true, false]),
     ("yyyy", { TemporalComponents.fullDate with month := false, day := false }, [false, false, true]),
     ("MM", { TemporalComponents.fullDate with year := false, day := false }, [false, true, false])].all
      (fun (format, components, expected) =>
        ["AddDays(D,1)", "AddMonths(D,1)", "AddYears(D,1)"].map
          (admittedIn (fragmentModel format components none)) == expected &&
        ["AddDays(D,1)", "AddMonths(D,1)", "AddYears(D,1)"].map
          (admittedIn (fragmentModel format components (some 2024))) ==
            [expected[0]!, expected[1]!, true]) = true := by
  native_decide

-- An unavailable calendar era is an implementation fault, not a measured kernel value error.
example :
    (do
      let parsed ← (parseText .english "AddYears(\"01.01.2024\",-3000)").toOption
      let surface ← (lowerScalarTemporalExpression model ["Form"] parsed.body).toOption
      let checked ← (elaborateScalarTemporalExpression model ["Form"] surface).toOption
      pure (match checked.evalResult .computation { read := fun _ => malformedCheckedCell } with
        | .error .calendarUnavailable => true | _ => false)) =
      some true := by
  native_decide

private def constructorModel : FlatModel :=
  { model with fields := model.fields ++ [
      { id := 3, groupPath := ["Form"], name := "Y",
        policy := { kind := .temporal .date (TemporalComponents.ofFormat "yyyy") }
        temporalTargetPolicy := some { format := "yyyy" } }] }

private def extremumGiven (operator constructor : String) : Option Bool := do
  let parsed ← (parseText .english s!"{operator}({constructor},[D])").toOption
  let surface ← (lowerScalarTemporalExpression constructorModel ["Form"] parsed.body).toOption
  let checked ← (elaborateScalarTemporalExpression constructorModel ["Form"] surface).toOption
  let value ← ModelZone.ConcreteProfile.europeBerlin.resolveCompletedDateParts? {
    year := 2024, month := 3, day := 1 }
  let result ← (checked.evalResult .validation {
    read := fun field => checkAdmittedRawCell
      (if field == 0 then .parsed (.temporal (.date value)) else .presentEmpty) }).toOption
  match result with
  | .value _ given => pure given
  | _ => none

-- The review-control grid distinguishes value absence from a missing component for both selectors.
example : ["Min", "Max"].all (fun operator =>
    extremumGiven operator "Date(\"31\",\"02\",\"2024\")" == some true &&
    extremumGiven operator "Date(\"01\",\"01\",Y)" == some false) := by native_decide

private def completedYearGuard (initial : String) : Option (List String) := do
  let model := { constructorModel with fields := constructorModel.fields ++ [
    { id := 4, groupPath := ["Form"], name := "S", policy := { kind := .string } }] }
  let dm : DmModel := { flat := model, computations := [], rules := [], conditionLanguage := "en_US", refusals := [] }
  let input ← (readDocument dm (Lean.Json.mkObj [("Form", Lean.Json.mkObj [
    ("Y", Lean.toJson initial), ("N", "9"), ("S", "old")])])).toOption
  if !input.refusals.isEmpty then none
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  let define (name target operation : String) (precondition : Option String) : DmComputation := {
    group := ["Form"], name, targetRelPath := target, commonPrecondition := none
    alternatives := [{ precondition, operation }], errorCodesToSuppress := [] }
  let guard := some "Date(\"01\",\"01\",Y) == \"01.01.2024\""
  let steps ← [define "Producer" "../Y" "\"01.01.2024\"" none,
      define "NumberConsumer" "../N" "7" guard,
      define "StringConsumer" "../S" "\"selected\"" guard].mapM fun computation =>
        (lowerComputation model .english computation).toOption.map (·.2)
  pure ((← (runComputations world prepared checked steps).toOption).map (·.outcome))

-- Both consumer kinds must see the completed year's spelling, even when no source spelling exists.
example : completedYearGuard "2023" = some ["value 2024", "value 7", "value selected"] ∧
    completedYearGuard "" = some ["value 2024", "value 7", "value selected"] := by native_decide

private def extensibleComponents (repeated : Bool) (values : List String) (arity : Nat := 3)
    (year : String := "2e3") (minute : String := "0") (century : String := "20") :
    Option (List String × List (List String)) := do
  let group := if repeated then ["Form", "Rows"] else ["Form"]
  let scope := if repeated then [10] else []
  let field (id : FieldId) (name : String) (kind : FieldKind) : FlatFieldDecl := {
    id, name, groupPath := group, repeatableScope := scope, policy := { kind } }
  let model : FlatModel := {
    fields := [
      { (field 1 "C" .string) with stringExtensibleEnum := true, stringPolicy := { maxLength := some 2 } },
      { (field 2 "Y" .string) with stringExtensibleEnum := true, stringPolicy := { maxLength := some 4 } },
      { (field 3 "D" (.temporal .date TemporalComponents.fullDate)) with
        temporalTargetPolicy := some { format := "yyyy-MM-dd" } },
      { (field 4 "T" (.temporal .time TemporalComponents.time)) with
        temporalTargetPolicy := some { format := "HH:mm:ss" } },
      field 5 "N" (.number { scale := 0, signed := true }),
      field 6 "H" (.number { scale := 0, signed := true }),
      { (field 7 "M" .string) with stringExtensibleEnum := true, stringPolicy := { maxLength := some 2 } },
      { (field 8 "Century" .string) with stringExtensibleEnum := true, stringPolicy := { maxLength := some 2 } }]
    timeZoneId := "UTC", baseYear := some 2000
    repeatableGroups := if repeated then [{ level := 10, path := group, repeatability := some 4 }] else [] }
  let dm : DmModel := { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let row (value : String) := Lean.Json.mkObj [
    ("C", Lean.toJson value), ("Y", Lean.toJson year), ("M", Lean.toJson minute), ("Century", Lean.toJson century), ("D", "2001-01-01"), ("T", "09:00:00"), ("N", "9"), ("H", "9")]
  let data := if repeated then Lean.Json.mkObj [("Rows", .arr (values.map row).toArray)]
    else row (values.headD "")
  let input ← (readDocument dm (Lean.Json.mkObj [("Form", data)])).toOption
  if !input.refusals.isEmpty then none
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  let dateOperation := match arity with
    | 2 => "Date(C,\"02\")"
    | 4 => "Date(C,\"02\",Century,C)"
    | _ => "Date(C,\"02\",Y)"
  let steps ← [("D", dateOperation), ("T", "Time(C,M)"),
    ("N", "DayFromDate(D)"), ("H", "HoursFromTime(T)")].mapM fun (target, operation) =>
    (lowerComputation model .english {
      group, name := target ++ "Comp", targetRelPath := "../" ++ target
      commonPrecondition := none, alternatives := [{ operation, precondition := none }]
      errorCodesToSuppress := [] }).toOption.map (·.2)
  let outcomes ← (runComputations world prepared checked steps).toOption
  let messages ← ["Date(C,\"02\",Y) == \"01.02.2000\"", "Time(C,M) == \"01:00:00\""].mapM fun condition => do
    let rule ← (checkRule dm .english {
      group, name := "Rule", errorCode := "R", errorEntityRelPath := "../C", condition, severity := "ERROR" } world).toOption
    pure ((← (runRule world checked rule).toOption).map fun message =>
      (observe model message).pointer ++ ":" ++ (observe model message).messageType)
  pure (outcomes.map (fun outcome => outcome.pointer ++ ":" ++ outcome.outcome), messages)

example : extensibleComponents false ["+1"] = some (
    ["Form/D:value 2000-02-01", "Form/T:value 01:00:00", "Form/N:value 1", "Form/H:value 1"],
    [["Form/C:VALUE_ERROR"], ["Form/C:VALUE_ERROR"]]) := by native_decide

example : extensibleComponents true ["+1", "2"] = some (
    ["Form/Rows/D:value 2000-02-01", "Form/Rows[2]/D:value 2000-02-02",
     "Form/Rows/T:value 01:00:00", "Form/Rows[2]/T:value 02:00:00",
     "Form/Rows/N:value 1", "Form/Rows[2]/N:value 2", "Form/Rows/H:value 1", "Form/Rows[2]/H:value 2"],
    [["Form/Rows/C:VALUE_ERROR"], ["Form/Rows/C:VALUE_ERROR"]]) := by native_decide

example : extensibleComponents false [""] = some (
    ["Form/D:cleared", "Form/T:cleared", "Form/N:value 0", "Form/H:value 0"], [[], []]) ∧
    extensibleComponents false ["x"] = some (
    ["Form/D:cleared", "Form/T:cleared", "Form/N:cleared", "Form/H:cleared"],
    [["Form/C:VALUE_ERROR"], ["Form/C:VALUE_ERROR"]]) ∧
    extensibleComponents false ["123"] = some (
    ["Form/D:cleared", "Form/T:cleared", "Form/N:cleared", "Form/H:cleared"], [[], []]) := by native_decide

example : extensibleComponents false [".5"] = some (
    ["Form/D:cleared", "Form/T:value 00:00:00", "Form/N:value 0", "Form/H:value 0"], [[], []]) ∧
    extensibleComponents false ["١"] = extensibleComponents false ["+1"] ∧
    extensibleComponents false ["+1"] 2 = extensibleComponents false ["+1"] := by native_decide

example : (extensibleComponents false ["+1"] 4).map (·.1) = some (
    ["Form/D:value 2001-02-01", "Form/T:value 01:00:00", "Form/N:value 1", "Form/H:value 1"]) := by native_decide

example : (extensibleComponents false ["123"] 3 "x" "x").map (·.2) =
    some [["Form/C:VALUE_ERROR"], ["Form/C:VALUE_ERROR"]] := by native_decide

example : extensibleComponents true ["2", "x"] = some (
    ["Form/Rows/D:value 2000-02-02", "Form/Rows[2]/D:cleared",
     "Form/Rows/T:value 02:00:00", "Form/Rows[2]/T:cleared",
     "Form/Rows/N:value 2", "Form/Rows[2]/N:cleared", "Form/Rows/H:value 2", "Form/Rows[2]/H:cleared"],
    [["Form/Rows/C:VALUE_ERROR"], ["Form/Rows/C:VALUE_ERROR"]]) := by native_decide

example : ["3e8", "2e9"].all (fun year =>
    extensibleComponents false ["+1"] 3 year == some (
      ["Form/D:cleared", "Form/T:value 01:00:00", "Form/N:value 0", "Form/H:value 1"],
      [[], ["Form/C:VALUE_ERROR"]])) := by native_decide

example : extensibleComponents false ["+1"] 3 "2e8" = some (
    ["Form/D:errored 200000000-02-01", "Form/T:value 01:00:00", "Form/N:cleared", "Form/H:value 1"],
    [[], ["Form/C:VALUE_ERROR"]]) := by native_decide

example : [(".5", "1"), ("-0", "2")].all (fun (century, day) =>
    (extensibleComponents false [day] 4 "2e3" "0" century).map (·.1) == some (
      ["Form/D:cleared", "Form/T:value 0" ++ day ++ ":00:00", "Form/N:value 0", "Form/H:value " ++ day])) := by native_decide

private def completedLiteralResult (year : Int) (phase : Phase) (source : String) :
    Option (TemporalComponents × SimpleComparisonOperand ScalarTemporalValue) := do
  let fixture := { model with baseYear := some year }
  let parsed ← (parseText .english source).toOption
  let surface ← (lowerScalarTemporalExpression fixture ["Form"] parsed.body).toOption
  let checked ← (elaborateScalarTemporalExpression fixture ["Form"] surface).toOption
  let stored ← ModelZone.ConcreteProfile.europeBerlin.resolveCompletedDateParts? {
    year, month := 3, day := 6 }
  let result ← (checked.evalResult phase {
    read := fun _ => checkAdmittedRawCell (.parsed (.temporal (.date stored))) }).toOption
  pure (checked.components, result)

example : [2023, 2024].all (fun year => [.validation, .computation].all (fun phase =>
    [("AddDays(", ",1)"), ("AddMonths(", ",1)"), ("AddYears(", ",1)"),
      ("DateTime(", ",\"12:00:00\")"), ("Min(", ",[D])"), ("Max(", ",[D])"),
      ("AddMonths(AddYears(", ",1),1)")].all (fun (before, after) =>
        let explicit := completedLiteralResult year phase s!"{before}\"05.03.{year}\"{after}"
        explicit.isSome && completedLiteralResult year phase s!"{before}\"05.03.\"{after}" == explicit))) = true := by native_decide

example : (do
    let parsed ← (parseText .english "\"05.03.\"").toOption
    let surface ← (lowerScalarTemporalExpression model ["Form"] parsed.body).toOption
    let checked ← (elaborateScalarTemporalExpression model ["Form"] surface).toOption
    pure (checked.components == TemporalComponents.fullDate && match checked.core with
      | .atom (.dateLiteral _ _ authoredYear) => !authoredYear
      | _ => false)) = some true := by native_decide

private def storedYear (format source operation : String) : Option (List String) := do
  let fixture := fragmentModel format (TemporalComponents.ofFormat format) (some 2024)
  let fixture : FlatModel := { fixture with timeZoneId := "UTC", fields := fixture.fields ++ [
    { id := 3, name := "InlineYear", groupPath := ["Form"],
      policy := { kind := .number { scale := 0, signed := true } } }] }
  let dm : DmModel := { flat := fixture, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let input ← (readDocument dm (Lean.Json.mkObj [("Form", Lean.Json.mkObj [
    ("D", .str source), ("N", "9"), ("InlineYear", "9")])])).toOption
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler fixture).toOption
  let document ← (checkDocument prepared "en_US" input.data).toOption
  let steps ← [("N", "YearFromDate(Result)"), ("InlineYear", "YearFromDate(" ++ operation ++ ")"),
    ("Result", operation)].mapM fun (target, expression) =>
      (lowerComputation fixture .english {
        name := target ++ "Comp", group := ["Form"], targetRelPath := "../" ++ target,
        commonPrecondition := none, alternatives := [{ precondition := none, operation := expression }],
        errorCodesToSuppress := [] }).toOption
  let results ← (runComputations world prepared document (steps.map (·.2))).toOption
  pure ((results.map fun result => result.pointer ++ "=" ++ result.outcome).mergeSort (· ≤ ·))

-- KF540's stored-Date witness makes producer inlining observably wrong at a yearless target.
example : storedYear "dd.MM." "31.12." "AddDays(D,1)" =
    some ["Form/InlineYear=value 2025", "Form/N=value 2024", "Form/Result=value 01.01."] ∧
    storedYear "dd.MM." "01.01." "AddDays(D,-1)" =
      some ["Form/InlineYear=value 2023", "Form/N=value 2024", "Form/Result=value 31.12."] ∧
    storedYear "yyyy-MM-dd" "2024-12-31" "AddDays(D,1)" =
      some ["Form/InlineYear=value 2025", "Form/N=value 2025", "Form/Result=value 2025-01-01"] := by native_decide

private def bindingModel : FlatModel :=
  let date (id : FieldId) (name : String) (path : GroupPath) (scope : List RepeatableLevel) : FlatFieldDecl := {
    id, name, groupPath := path, repeatableScope := scope, policy := { kind := .temporal .date TemporalComponents.fullDate },
    temporalTargetPolicy := some { format := "yyyy-MM-dd" } }
  let stamp (id : FieldId) (name : String) (path : GroupPath) (scope : List RepeatableLevel) : FlatFieldDecl := {
    id, name, groupPath := path, repeatableScope := scope, policy := { kind := .temporal .dateTime .now },
    temporalTargetPolicy := some { format := "yyyy-MM-dd'T'HH:mm:ss" } }
  let number (id : FieldId) (name : String) (path : GroupPath) (scope : List RepeatableLevel) : FlatFieldDecl := {
    id, name, groupPath := path, repeatableScope := scope, policy := { kind := .number { scale := 0, signed := true } } }
  let range (id : FieldId) (name : String) (path : GroupPath) (scope : List RepeatableLevel) : FlatFieldDecl := {
    id, name, groupPath := path, repeatableScope := scope, policy := { kind := .dateRange }
    dateRangePolicy := some { format := "yyyy-MM-dd", separator := "/" } }
  { fields := [number 0 "N0" ["P"] [], date 1 "D0" ["P"] [], stamp 2 "DT0" ["P"] [], date 3 "D2" ["P"] [],
      { id := 4, name := "T2", groupPath := ["P"], policy := { kind := .temporal .time .time },
        temporalTargetPolicy := some { format := "HH:mm:ss" } },
      range 5 "R2" ["P"] [], number 6 "N2" ["P"] [], date 7 "D" ["P", "Rows"] [10], stamp 8 "DT" ["P", "Rows"] [10],
      number 9 "N" ["P", "Rows"] [10], range 10 "R" ["P", "Rows"] [10],
      { id := 11, name := "C", groupPath := ["P", "Rows"], repeatableScope := [10], policy := { kind := .confirm } },
      { id := 12, name := "C0", groupPath := ["P"], policy := { kind := .confirm } },
      { id := 13, name := "C2", groupPath := ["P", "Rows"], repeatableScope := [10], policy := { kind := .confirm } },
      { id := 14, name := "B", groupPath := ["P", "Rows"], repeatableScope := [10], policy := { kind := .boolean } },
      { id := 15, name := "B0", groupPath := ["P"], policy := { kind := .boolean } },
      { id := 16, name := "B2", groupPath := ["P", "Rows"], repeatableScope := [10], policy := { kind := .boolean } }]
    repeatableGroups := [{ level := 10, path := ["P", "Rows"], repeatability := some 4 }] }

private def bindingAdmitted (group : GroupPath) (target operation : String) : Bool :=
  (lowerComputation bindingModel .english {
    group, name := "C", targetRelPath := (if group.length == 1 then "../" else "../../") ++ target
    commonPrecondition := none, alternatives := [{ precondition := none, operation }]
    errorCodesToSuppress := [] }).isOk

/-- The fixed-target arms that read an operand through a temporal or by-id carrier — copy, shift
amount and source, both extractions from a DateTime, DateRange and Date construction and a Date
part — refuse an unstarred row operand from the root and from the row's own declaring group, as the
Kernel does on each (`MVK_NO_WILDCARD`, `MVK_ERROR_FIELD_NOT_IN_RULEGROUP`), and admit the root
twin. Rows `a1`–`a8` of the
[checkpoint](../../../docs/sources/computation-placement-and-constant-probes.md#src-by-id-temporal-arm-binding). -/
example : [("D2", "[Rows/D]", "[D]", "[D0]"), ("D2", "AddDays(D0, [Rows/N])", "AddDays(/P/D0, [N])", "AddDays(D0, [N0])"),
    ("D2", "AddDays(Rows/D, 1)", "AddDays(D, 1)", "AddDays(D0, 1)"),
    ("D2", "DateFromDateTime(Rows/DT)", "DateFromDateTime(DT)", "DateFromDateTime(DT0)"),
    ("T2", "TimeFromDateTime(Rows/DT)", "TimeFromDateTime(DT)", "TimeFromDateTime(DT0)"),
    ("R2", "DateRange(Rows/D, D0)", "DateRange(D, /P/D0)", "DateRange(D0, D0)"),
    ("D2", "Date(Rows/N, N0, N0)", "Date(N, /P/N0, /P/N0)", "Date(N0, N0, N0)"),
    ("N2", "YearFromDate(Rows/D)", "YearFromDate(D)", "YearFromDate(D0)")].map (fun (target, root, row, twin) =>
      (bindingAdmitted ["P"] target root, bindingAdmitted ["P", "Rows"] target row, bindingAdmitted ["P"] target twin)) =
    [(false, false, true), (false, false, true), (false, false, true), (false, false, true), (false, false, true),
      (false, false, true), (false, false, false), (false, false, true)] := by native_decide

/-- The row-declared refusals above come from the row operand, not from the root target the row group
declares: the same group and target admit a copy and a shift of a root field, rows `bx1` and `bx2` of
the [waiver-carrier capture](../../../docs/sources/computation-placement-and-constant-probes.md#src-by-id-temporal-arm-binding). -/
example : bindingAdmitted ["P", "Rows"] "D2" "[/P/D0]" = true ∧
    bindingAdmitted ["P", "Rows"] "D2" "AddDays(/P/D0, 1)" = true := by native_decide

/-- A row Boolean target first-fills its own row's Boolean before a root one, while the Confirm
twin draws `MVK_NO_BOOLY_ALLOWED`: rows `k04` and `k05` of the
[checkpoint](../../../docs/sources/computation-placement-and-constant-probes.md#src-row-copy-carriers-and-root-indices). -/
example : bindingAdmitted ["P"] "Rows/B2" "FirstFilledValue(Rows/B, B0)" = true ∧
    (match lowerComputation bindingModel .english {
        group := ["P"], name := "C", targetRelPath := "../Rows/C2", commonPrecondition := none
        alternatives := [{ precondition := none, operation := "FirstFilledValue(Rows/C, C0)" }]
        errorCodesToSuppress := [] } with
      | .error refusal => refusal.detail == "MVK_NO_BOOLY_ALLOWED"
      | .ok _ => false) = true := by native_decide

private def yearlessShiftEquality (baseYear : Option Int) (source stored : String) (fires : Bool) :
    Option (List String) := do
  let fixture := { fragmentModel "MM-dd" (TemporalComponents.ofFormat "MM-dd") baseYear with timeZoneId := "Europe/Berlin" }
  let rule : DmRule := {
    group := ["Form"], name := "Shifted", errorEntityRelPath := "../Result"
    errorCode := "SHIFTED", condition := "AddDays(D,1) == [Result]", severity := "ERROR" }
  let dm : DmModel := { flat := fixture, rules := [rule], computations := [], conditionLanguage := "en_US", refusals := [] }
  let input ← (readDocument dm (Lean.Json.mkObj [("Form", Lean.Json.mkObj [
    ("D", .str source), ("Result", .str stored)])])).toOption
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler fixture).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  let messages := if fires then [{
    code := "SHIFTED", pointer := "Form/Result", messageType := "VALUE_ERROR", severity := "ERROR" }] else []
  pure ((replayRules dm .english world checked messages).map (·.status.tier))

-- A yearless shift keeps the year it reaches, so crossing December 31 leaves it unequal to the
-- stored `01-01`, with or without a Base Year; inside the year it equals the stored month and day
-- ([yearless shift anchor](../../../docs/sources/temporal-constant-and-base-year-probes.md#src-yearless-shift-anchor)).
example : [none, some 2001].all (fun baseYear =>
    yearlessShiftEquality baseYear "12-31" "01-01" false == some ["match"] &&
    yearlessShiftEquality baseYear "12-30" "12-31" true == some ["match"] &&
    yearlessShiftEquality baseYear "06-15" "06-16" true == some ["match"]) = true := by
  native_decide

end A12Kernel.Dm.CalendarExpressionLocks
