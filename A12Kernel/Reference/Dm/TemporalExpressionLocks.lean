import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Document
import A12Kernel.Reference.Dm.Validate
import A12Kernel.Reference.Dm.LowerValidation
import A12Kernel.Reference.Dm.Parser

namespace A12Kernel.Dm.TemporalExpressionLocks

open A12Kernel A12Kernel.Dm

private def model : FlatModel := {
  fields := [
    {
      id := 5
      groupPath := ["Order"]
      name := "Due1"
      policy := { kind := .temporal .date TemporalComponents.fullDate }
      temporalTargetPolicy := some { format := "yyyy-MM-dd" }
    }, {
      id := 6
      groupPath := ["Order"]
      name := "Clock"
      policy := { kind := .temporal .time TemporalComponents.time }
      temporalTargetPolicy := some { format := "HH:mm:ss" }
    }, {
      id := 7
      groupPath := ["Order"]
      name := "Stamp"
      policy := { kind := .temporal .dateTime TemporalComponents.now }
      temporalTargetPolicy := some { format := "yyyy-MM-dd'T'HH:mm:ss" }
    }, {
      id := 8
      groupPath := ["Order"]
      name := "Stamp2"
      policy := { kind := .temporal .dateTime TemporalComponents.now }
      temporalTargetPolicy := some { format := "yyyy-MM-dd'T'HH:mm:ss" }
    }]
}

private def admitted (text : String) : Bool :=
  match parseText .english text with
  | .ok parsed => (lowerCondition model ["Order"] false parsed.body).toOption.isSome
  | .error _ => false

private def numericModel : FlatModel := { model with
  timeZoneId := "Europe/Berlin"
  fields := model.fields ++ [(90, "NumericOut"), (91, "NumericDep"), (92, "Anchor")].map
    (fun (id, name) => {
      id, name, groupPath := ["Order"]
      policy := { kind := .number { scale := 0, signed := true } } }) }

private def numericArms (expression : String) : Bool × Bool :=
  ((match parseText .english (expression ++ " == 1") with
    | .ok parsed => (lowerCondition numericModel ["Order"] false parsed.body).isOk
    | .error _ => false), (lowerComputation numericModel .english {
    group := ["Order"], name := "NumericOutComp", targetRelPath := "../NumericOut"
    commonPrecondition := none, alternatives := [{ precondition := none, operation := expression }]
    errorCodesToSuppress := [] }).isOk)

example : ["HoursFromTime(Now)", "MinutesFromTime(Now)", "SecondsFromTime(Now)",
    "HoursFromTime(AddHours(Stamp,1))", "MinutesFromTime(AddMinutes(Stamp,90))",
    "SecondsFromTime(AddSeconds(Stamp,1))", "HoursFromTime(TimeFromDateTime(Stamp))",
    "HoursFromTime(Time(\"01\",\"02\",\"03\"))"].all
      (fun expression => numericArms expression == (true, true)) = true := by native_decide

example : ["HoursFromTime(\"01:02:03\")", "MinutesFromTime(Today)",
    "SecondsFromTime([Clock])", "HoursFromTime({Now})"].all
      (fun expression => numericArms expression == (false, false)) = true := by native_decide

example : numericArms "HoursFromTime(AddSeconds(Stamp,[NumericOut]))" = (true, false) ∧
    numericArms "HoursFromTime(AddSeconds(Stamp,[NumericDep]))" = (true, true) ∧
    numericArms "HoursFromTime(Time(MinutesFromTime(Clock)))" = (false, false) ∧
    numericArms "SecondsFromTime(Time(HoursFromTime(Now),MinutesFromTime(Now),SecondsFromTime(Now)))" =
      (true, true) := by native_decide

private def numericReadback (expression stamp clock : String) :
    Option (List String × List (List Polarity)) := do
  let dm : DmModel := {
    flat := numericModel, computations := [], rules := [], conditionLanguage := "en_US", refusals := [] }
  let input ← (readDocument dm (Lean.Json.mkObj [("Order", Lean.Json.mkObj [
    ("Stamp", Lean.Json.str stamp), ("Clock", Lean.Json.str clock),
    ("NumericOut", Lean.Json.num 99), ("NumericDep", Lean.Json.num 99),
    ("Anchor", Lean.Json.num 1)])])).toOption
  let world : World := { now := { epochMillis := 1704112496000 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler numericModel).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  let steps ← [("NumericDep", "[NumericOut] + 1"), ("NumericOut", expression)].mapM fun (name, operation) =>
    (lowerComputation numericModel .english {
      group := ["Order"], name := name ++ "Comp", targetRelPath := "../" ++ name
      commonPrecondition := none, alternatives := [{ precondition := none, operation }]
      errorCodesToSuppress := [] }).toOption.map (·.2)
  let computed ← (runComputations world prepared checked steps).toOption
  let messages ← [" == 0", " < 1", " > -1"].mapM fun suffix => do
    let rule ← (checkRule dm .english {
      group := ["Order"], name := "Check", errorEntityRelPath := "../Anchor", errorCode := "Check"
      condition := "FieldFilled(Anchor) And " ++ expression ++ suffix, severity := "ERROR" } world).toOption
    pure ((← (runRule world checked rule).toOption).map (·.messageType))
  pure ((computed.map fun result => result.pointer ++ ":" ++ result.outcome).mergeSort, messages)

example : numericReadback "HoursFromTime(TimeFromDateTime(Stamp))" "2024-01-01T00:00:00" "" =
    some (["Order/NumericDep:value 1", "Order/NumericOut:value 0"], [[.value], [.value], [.value]]) ∧
    numericReadback "HoursFromTime(TimeFromDateTime(Stamp))" "" "" =
    some (["Order/NumericDep:value 1", "Order/NumericOut:value 0"], [[.omission], [.omission], [.omission]]) ∧
    numericReadback "HoursFromTime(TimeFromDateTime(Stamp))" "bad" "" =
    some (["Order/NumericDep:cleared", "Order/NumericOut:cleared"], [[], [], []]) := by native_decide

example : numericReadback "SecondsFromTime(AddSeconds(Stamp,61))" "2024-01-01T23:59:30" "bad" =
    some (["Order/NumericDep:value 32", "Order/NumericOut:value 31"], [[], [], [.value]]) ∧
    numericReadback "HoursFromTime(Now)" "bad" "bad" =
    some (["Order/NumericDep:value 14", "Order/NumericOut:value 13"], [[], [], [.value]]) ∧
    numericReadback "MinutesFromTime(Time(\"01\",\"02\",\"03\"))" "bad" "bad" =
    some (["Order/NumericDep:value 3", "Order/NumericOut:value 2"], [[], [], [.value]]) := by native_decide

example : numericReadback "HoursFromTime(Time(HoursFromTime(TimeFromDateTime(AddSeconds(Stamp,61)))))"
      "2024-01-01T23:59:30" "" =
    some (["Order/NumericDep:value 1", "Order/NumericOut:value 0"], [[.value], [.value], [.value]]) := by native_decide

example : numericReadback "SecondsFromTime(AddSeconds(Stamp,HoursFromTime(Clock)))"
      "2024-01-01T23:59:30" "" =
    some (["Order/NumericDep:value 31", "Order/NumericOut:value 30"], [[], [], [.omission]]) ∧
    numericReadback "SecondsFromTime(AddSeconds(Stamp,HoursFromTime(Clock)))"
      "2024-01-01T23:59:30" "00:00:00" =
    some (["Order/NumericDep:value 31", "Order/NumericOut:value 30"], [[], [], [.value]]) ∧
    numericReadback "SecondsFromTime(AddSeconds(Stamp,HoursFromTime(Clock)))" "" "bad" =
    some (["Order/NumericDep:cleared", "Order/NumericOut:cleared"], [[], [], []]) := by native_decide

example : ["AddSeconds", "AddDays"].all (fun shift =>
    numericReadback ("HoursFromTime(" ++ shift ++ "(Stamp,1/0))") "2024-01-01T23:59:30" "" ==
      some (["Order/NumericDep:value 1", "Order/NumericOut:value 0"], [[.value], [.value], [.value]]) &&
    numericReadback ("HoursFromTime(" ++ shift ++ "(Stamp,1/0))") "" "" ==
      some (["Order/NumericDep:value 1", "Order/NumericOut:value 0"], [[.omission], [.omission], [.omission]]) &&
    numericReadback ("HoursFromTime(" ++ shift ++ "(Stamp,HoursFromTime(TimeFromDateTime(\"31.03.2024T02:30:00\"))))") "bad" "" ==
      some (["Order/NumericDep:cleared", "Order/NumericOut:cleared"], [[.value], [.value], [.value]])) = true := by native_decide

private def numericRows (expression : String) : Option (List String) := do
  let model := { numericModel with
    fields := numericModel.fields.map (fun field => { field with groupPath := ["Order", "Rows"], repeatableScope := [10] })
    repeatableGroups := [{ level := 10, path := ["Order", "Rows"], repeatability := some 3 }] }
  let dm : DmModel := { flat := model, computations := [], rules := [], conditionLanguage := "en_US", refusals := [] }
  let rows := [("2024-01-01T23:59:30", "05:06:07"), ("2024-01-01T23:59:30", ""), ("bad", "00:00:00")].map
    (fun (stamp, clock) => Lean.Json.mkObj [("Stamp", Lean.Json.str stamp), ("Clock", Lean.Json.str clock),
      ("NumericOut", Lean.Json.num 99), ("NumericDep", Lean.Json.num 99), ("Anchor", Lean.Json.num 1)])
  let input ← (readDocument dm (Lean.Json.mkObj [("Order", Lean.Json.mkObj [("Rows", .arr rows.toArray)])])).toOption
  let world : World := { now := { epochMillis := 1704112496000 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  let steps ← [("NumericDep", "[NumericOut] + 1"), ("NumericOut", expression)].mapM fun (name, operation) =>
    (lowerComputation model .english {
      group := ["Order", "Rows"], name := name ++ "Comp", targetRelPath := "../" ++ name
      commonPrecondition := none, alternatives := [{ precondition := none, operation }]
      errorCodesToSuppress := [] }).toOption.map (·.2)
  pure ((← (runComputations world prepared checked steps).toOption).map
    (fun result => result.pointer ++ ":" ++ result.outcome)).mergeSort

example : numericRows "SecondsFromTime(AddSeconds(Stamp,HoursFromTime(Clock)))" = some [
    "Order/Rows/NumericDep:value 36", "Order/Rows/NumericOut:value 35",
    "Order/Rows[2]/NumericDep:value 31", "Order/Rows[2]/NumericOut:value 30",
    "Order/Rows[3]/NumericDep:cleared", "Order/Rows[3]/NumericOut:cleared"] ∧
    numericRows "HoursFromTime(Time(HoursFromTime(TimeFromDateTime(AddSeconds(Stamp,61)))))" = some [
    "Order/Rows/NumericDep:value 1", "Order/Rows/NumericOut:value 0",
    "Order/Rows[2]/NumericDep:value 1", "Order/Rows[2]/NumericOut:value 0",
    "Order/Rows[3]/NumericDep:cleared", "Order/Rows[3]/NumericOut:cleared"] := by native_decide

private def operationAdmitted (text : String) : Bool :=
  match parseText .english text, model.lookupUniqueId 7 with
  | .ok parsed, .ok target =>
      (lowerDocumentStep model ["Order"] target parsed.body).toOption.isSome
  | _, _ => false

example :
    !admitted "Stamp == Now" ∧
      !admitted "{Stamp} == Now" ∧
      !admitted "Min(Stamp, Stamp2) == Now" ∧
      !operationAdmitted "Stamp2" ∧
      admitted "[Stamp] == Now" ∧
      admitted "{[Stamp]} == Now" ∧
      admitted "Min([Stamp], [Stamp2]) == Now" ∧
      operationAdmitted "[Stamp2]" := by native_decide

example :
    !admitted "AddHours(Min([Stamp], [Stamp2]), 1) == Now" ∧
      !admitted "TimeFromDateTime(MinValue(Stamp, Stamp2)) == [Clock]" ∧
      !admitted "TimeFromDateTime([Stamp]) == [Clock]" ∧
      admitted "TimeFromDateTime(Stamp) == [Clock]" ∧
      admitted "Min([Stamp], [Stamp2]) == Now" := by native_decide

private def stored (targetField : FieldId) (text : String) : Option String := do
  let parsed ← (parseText .english text).toOption
  let target ← (model.lookupUniqueId targetField).toOption
  let step ← (lowerDocumentStep model ["Order"] target parsed.body).toOption
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption
  let document ← (checkDocument prepared "en_US" { instantiatedRows := [], cells := [] }).toOption
  let (outcome, _) ← (step.run { now := { epochMillis := 0 } } (fun _ => none) document).toOption
  pure (match outcome with
    | .fullDate (.accepted value) => value.text
    | .time (.accepted value) => value.text
    | .dateTime (.accepted value) => value.text
    | _ => "unavailable")

example :
    admitted "DateFromDateTime(AddHours(Now, 25)) == Today" ∧
      admitted "TimeFromDateTime(AddMinutes(Now, 90)) == \"01:30:00\"" ∧
      !admitted "\"01:30:00\" == \"01:30:00\"" ∧
      admitted "{Now} == Now" ∧
      !admitted "{Now} == {Now}" ∧
      !admitted "AddHours(\"01:30:00\", 1) == Now" := by native_decide

example :
    stored 5 "DateFromDateTime(AddHours(Now, 25))" = some "1970-01-02" ∧
      stored 6 "Time(\"1\", \"30\")" = some "01:30:00" ∧
      stored 7 "AddSeconds(Now, 61)" = some "1970-01-01T00:01:01" ∧
      stored 7 "AddHours(Stamp, 1)" = none := by native_decide

example :
    admitted "MinValue(Stamp, Stamp2) == [Stamp]" ∧
      !admitted "DateFromDateTime(MinValue(Stamp, Stamp2)) == Today" ∧
      !admitted "AddHours(MinValue(Stamp, Stamp2), 1) == Now" ∧
      !admitted "AddHours({Now}, 1) == Now" ∧
      !admitted "AddHours([Stamp], 1) == Now" ∧
      admitted "AddHours(Stamp, 1) == Now" ∧
      admitted "DateFromDateTime(AddHours(Now, 25)) == Today" ∧
      admitted "AddHours(AddSeconds(Now, 1), 1) == Now" := by native_decide

private def gapResult (targetField : FieldId) (text : String) (badSource : Bool := false) :
    Option (DocumentTargetOutcome × CheckedCell) := do
  let berlin := { model with timeZoneId := "Europe/Berlin" }
  let parsed ← (parseText .english text).toOption
  let target ← (berlin.lookupUniqueId targetField).toOption
  let step ← (lowerDocumentStep berlin ["Order"] target parsed.body).toOption
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler berlin).toOption
  let document ← (checkDocument prepared "en_US" { instantiatedRows := [], cells := if badSource then
      [{ address := { field := 8, path := [] }, stored := "bad", raw := .rejected .malformed }] else [] }).toOption
  (step.run world (fun _ => none) document).toOption

example :
    gapResult 7 "\"31.03.2024T02:30:00\"" =
        some (.valueError .dateTime, DocumentComputationReadBack.poison) ∧
      gapResult 7 "AddSeconds(\"31.03.2024T02:30:00\", 1)" =
        some (.valueError .dateTime, DocumentComputationReadBack.poison) ∧
      gapResult 5 "DateFromDateTime(\"31.03.2024T02:30:00\")" =
        some (.valueError .fullDate, DocumentComputationReadBack.poison) ∧
      gapResult 6 "TimeFromDateTime(\"31.03.2024T02:30:00\")" =
        some (.valueError .time, DocumentComputationReadBack.poison) := by native_decide

example :
    (DocumentTargetOutcome.valueError .dateTime).storedText? = none ∧
      (DocumentTargetOutcome.valueError .dateTime).formalValueMessage?
          (MessagePointer.ofCellAddr { field := 7, path := [] }) =
        some {
          pointer := MessagePointer.ofCellAddr { field := 7, path := [] }
          errorCode := berechnungsWertFehler
          messageType := .value
          payload := () } := by native_decide

example : (match gapResult 7 "Min([Stamp2], \"31.03.2024T02:30:00\")" true with
    | some (.dateTime (.poison _), _) => true | _ => false) = true ∧
    (match gapResult 7 "Max([Stamp2], \"31.03.2024T02:30:00\")" true with
    | some (.dateTime (.poison _), _) => true | _ => false) = true ∧
    (match gapResult 7 "Min(\"31.03.2024T02:30:00\", [Stamp2])" true with
    | some (.valueError .dateTime, _) => true | _ => false) = true := by native_decide

private def runtimeModel : FlatModel := { model with
  timeZoneId := "Europe/Berlin"
  fields := model.fields ++ [(9, "Shift"), (10, "First"), (11, "Guard")].map fun (id, name) => {
    id, name, groupPath := ["Order"]
    policy := { kind := .temporal .dateTime TemporalComponents.now }
    temporalTargetPolicy := some { format := "yyyy-MM-dd'T'HH:mm:ss" } } }

private def runtimeInput (stamp : String) (seed : Bool) : Lean.Json :=
  Lean.Json.mkObj [("Order", Lean.Json.mkObj (
    [("Stamp", Lean.Json.str stamp)] ++
    if seed then ["Stamp2", "Shift", "First", "Guard"].map
      (fun name => (name, Lean.Json.str "2020-01-01T00:00:00")) else []))]

private def dependentRun (label : String) (seed : Bool) : Option (List String) := do
  let dm : DmModel := {
    flat := runtimeModel, computations := [], rules := []
    conditionLanguage := "en_US", refusals := [] }
  let input ← (readDocument dm (runtimeInput "2020-01-01T00:00:00" seed)).toOption
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler runtimeModel).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  let definitions : List (String × String × Option String) := [
    ("First", "FirstFilledValue(Stamp,Stamp2)", none),
    ("Guard", "\"05.03.2024T12:30:00\"", some "FieldNotFilled(Stamp)"),
    ("Shift", "AddSeconds(Stamp,1)", none),
    ("Stamp", "\"" ++ label ++ "\"", none),
    ("Stamp2", "\"05.03.2024T12:30:00\"", none)]
  let steps ← definitions.mapM fun (name, operation, precondition) =>
    (lowerComputation runtimeModel .english {
      group := ["Order"], name := name ++ "Comp"
      targetRelPath := "../" ++ name, commonPrecondition := precondition
      alternatives := [{ precondition := none, operation }], errorCodesToSuppress := [] }).toOption.map (·.2)
  pure ((← (runComputations world prepared checked steps).toOption).map
    (fun result => result.pointer ++ ":" ++ result.outcome)).mergeSort

example : dependentRun "31.03.2024T02:30:00" true = some [
    "Order/First:cleared", "Order/Guard:cleared", "Order/Shift:cleared", "Order/Stamp2:value 2024-03-05T12:30:00",
    "Order/Stamp:cleared"] := by native_decide

private def validationRun (condition stamp : String) : Option (List Polarity) := do
  let dm : DmModel := {
    flat := runtimeModel, computations := [], rules := []
    conditionLanguage := "en_US", refusals := [] }
  let input ← (readDocument dm (runtimeInput stamp true)).toOption
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler runtimeModel).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  let rule ← (checkRule dm .english {
    group := ["Order"], name := "Check", errorEntityRelPath := "../Stamp"
    errorCode := "Check", condition, severity := "ERROR" } world).toOption
  pure ((← (runRule world checked rule).toOption).map (·.messageType))

example : ["", "bad", "2024-03-31T01:00:00", "2024-03-31T04:00:00"].all
    (fun stamp => validationRun "[Stamp] < \"31.03.2024T02:30:00\"" stamp == some [.value]) := by native_decide

example : validationRun "[Stamp] < \"31.03.2024T02:30:00\" And FieldNotFilled(Stamp)"
      "2024-03-31T01:00:00" = some [.value] ∧
    validationRun "FieldNotFilled(Stamp) And [Stamp] < \"31.03.2024T02:30:00\""
      "2024-03-31T01:00:00" = some [] ∧
    validationRun "[Stamp] < \"31.03.2024T01:30:00\"" "2024-03-31T01:00:00" = some [.value] ∧
    validationRun "[Stamp] < \"31.03.2024T01:30:00\"" "2024-03-31T04:00:00" = some [] := by native_decide

example : validationRun "FieldNotFilled(Stamp) And [Stamp] < \"31.03.2024T02:30:00\""
    "bad" = some [] := by native_decide


private def rowModel : FlatModel := {
  model with
  fields := (model.fields.map fun field =>
    { field with groupPath := ["Order", "Rows"], repeatableScope := [10] }) ++ [
    { id := 9, groupPath := ["Order", "Rows"], name := "Amount", repeatableScope := [10],
      policy := { kind := .number { scale := 0, signed := true } } },
    { id := 10, groupPath := ["Order"], name := "Flag", policy := { kind := .string } },
    { id := 11, groupPath := ["Order"], name := "Amount",
      policy := { kind := .number { scale := 0, signed := true } } },
    { id := 12, groupPath := ["Order", "Rows"], name := "Year", repeatableScope := [10],
      policy := { kind := .temporal .date { TemporalComponents.fullDate with month := false, day := false } },
      temporalTargetPolicy := some { format := "yyyy" } },
    { id := 13, groupPath := ["Order", "Rows"], name := "Partial", repeatableScope := [10],
      policy := { kind := .temporal .date TemporalComponents.fullDate },
      temporalTargetPolicy := some { format := "yyyy-MM-dd", partialMode := .yearOptional } },
    { id := 14, groupPath := ["Order", "Rows"], name := "Range", repeatableScope := [10],
      policy := { kind := .dateRange },
      dateRangePolicy := some { format := "yyyy-MM-dd", separator := "/" } },
    { id := 15, groupPath := ["Order", "Rows"], name := "Day", repeatableScope := [10],
      policy := { kind := .number { scale := 0, signed := false } },
      numericTargetConstraints := { maxStoredLength := some 2 } },
    { id := 16, groupPath := ["Order", "Rows"], name := "Month", repeatableScope := [10],
      policy := { kind := .string }, stringPolicy := { maxLength := some 2 },
      stringPatternSource := some asciiDigitsPatternSource }]
  repeatableGroups := [{ level := 10, path := ["Order", "Rows"], repeatability := some 3 }] }

private def rowDm : DmModel := {
  flat := rowModel, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }

private def rowRule (text : String) (atRoot : Bool := false) : DmRule := {
  group := if atRoot then ["Order"] else ["Order", "Rows"]
  name := "Rule", errorCode := "R", condition := text, severity := "ERROR"
  errorEntityRelPath := if atRoot then "../Rows/Stamp2" else "../Stamp2" }

private def runRows (text : String) (rows : List Lean.Json) (atRoot : Bool := false)
    (zone : String := "UTC") :
    Option (List String) := do
  let rowDm := { rowDm with flat := { rowModel with timeZoneId := zone } }
  let rowModel := rowDm.flat
  let rule ← (checkRule rowDm .english (rowRule text atRoot)).toOption
  let input ← (readDocument rowDm (Lean.Json.mkObj [("Order", Lean.Json.mkObj [
    ("Flag", "yes"), ("Amount", "0"), ("Rows", Lean.Json.arr rows.toArray)])])).toOption
  if !input.refusals.isEmpty then none
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler rowModel).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  pure ((← (runRule world checked rule).toOption).map fun message =>
    (observe rowModel message).pointer)

private def clockRow (amount : String) : Lean.Json := Lean.Json.mkObj [
  ("Stamp", "2024-03-31T01:00:00"), ("Stamp2", "2024-03-31T02:00:00"),
  ("Clock", "01:00:00"), ("Due1", "2024-03-31"), ("Amount", Lean.Json.str amount)]

-- The row-binding grid transposes the same temporal trees to selected and implicit
-- coordinates; equal field names at different rows must never read the scalar context.
example : runRows "AddHours(Stamp,[Amount]) == [Stamp2]" [clockRow "0", clockRow "1"] =
    some ["Order/Rows[2]/Stamp2"] := by native_decide

example : runRows "AddHours(Rows/Stamp,[Rows/Amount]) == [Rows/Stamp2]"
    [clockRow "0", clockRow "1"] true = some ["Order/Rows[2]/Stamp2"] := by native_decide

example : runRows "DateTime(DateFromDateTime(Stamp),TimeFromDateTime(Stamp)) == [Stamp2]"
    [] = some [] := by native_decide

example : (do
    let checked ← (checkRule rowDm .english
      (rowRule "AddHours(Stamp,[Amount]) == [Stamp2]")).toOption
    pure (checked.condition.rowGroup, checked.condition.declaringGroup,
      checked.iterationScope, checked.supportsOrdinaryRepeatablePartial)) =
    some (["Order", "Rows"], ["Order", "Rows"], some [10], false) := by native_decide

example : runRows "AddHours(Rows/Stamp,[Amount]) == [Rows/Stamp2]"
    [clockRow "1"] true = some [] ∧
    runRows "AddHours(Rows/Stamp,[Amount]+1) == [Rows/Stamp2]"
    [clockRow "0"] true = some ["Order/Rows/Stamp2"] := by native_decide

example : runRows "MinValue(Stamp,Stamp2) == [Stamp]" [clockRow "1"] =
    some ["Order/Rows/Stamp2"] := by native_decide

example : (do
    let parsed ← (parseText .english "AddHours(Rows/Stamp,1) == [Rows/Stamp2]").toOption
    pure (!(lowerCondition rowModel ["Order"] false parsed.body).isOk &&
      (lowerCondition rowModel ["Order"] false parsed.body (bindingGroup := ["Order", "Rows"])).isOk)) =
    some true := by native_decide

example : runRows "[Stamp2] < \"31.03.2024T02:30:00\""
    [Lean.Json.mkObj [("Stamp2", "2024-03-31T01:00:00"), ("Clock", "01:00:00")], Lean.Json.mkObj [("Stamp2", "2024-03-31T01:00:00"), ("Clock", "01:00:00")]] false "Europe/Berlin" =
    some ["Order/Rows/Stamp2"] := by native_decide

private def delayedFailureRows : List Lean.Json :=
  [Lean.Json.mkObj [("Stamp2", "2024-03-31T01:00:00")],
     Lean.Json.mkObj [("Stamp2", "2024-03-31T01:00:00"), ("Clock", "01:00:00")],
     Lean.Json.mkObj [("Stamp2", "2024-03-31T01:00:00"), ("Clock", "01:00:00")]]

example : runRows "FieldFilled(Clock) And [Stamp2] < \"31.03.2024T02:30:00\""
    delayedFailureRows
    false "Europe/Berlin" = some ["Order/Rows/Stamp2"] := by native_decide

example : runRows "[Stamp2] < \"31.03.2024T01:30:00\""
    (List.replicate 3 (Lean.Json.mkObj [("Stamp2", "2024-03-31T01:00:00")]))
    false "Europe/Berlin" =
    some ["Order/Rows/Stamp2", "Order/Rows[2]/Stamp2", "Order/Rows[3]/Stamp2"] := by native_decide

example : (do
    let dm := { rowDm with flat := { rowModel with timeZoneId := "Europe/Berlin" } }
    let world : World := { now := { epochMillis := 0 } }
    let rule ← (checkRule dm .english
      (rowRule "FieldFilled(Clock) And [Stamp2] < \"31.03.2024T02:30:00\"")).toOption
    let input ← (readDocument dm (Lean.Json.mkObj [("Order", Lean.Json.mkObj [
      ("Rows", Lean.Json.arr delayedFailureRows.toArray)])])).toOption
    let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler dm.flat).toOption
    let checked ← (checkDocument prepared "en_US" input.data).toOption
    let outcomes ← (rule.evalOrdinaryRepeatableFull checked (some world)).toOption
    pure (outcomes.map fun (environment, outcome) =>
      (environment, outcome.message?.map fun message =>
        (observe dm.flat message).pointer))) =
    some [([(10, 1)], none), ([(10, 2)], some "Order/Rows/Stamp2")] := by native_decide

example : runRows
    "FieldFilled(Stamp2) Or [Stamp2] < \"31.03.2024T02:30:00\""
    (List.replicate 3 (Lean.Json.mkObj [("Stamp2", "2024-03-31T01:00:00"), ("Clock", "01:00:00")])) false "Europe/Berlin" =
    some ["Order/Rows/Stamp2"] := by native_decide

example : runRows
    "FieldFilled(Stamp2) Or (FieldFilled(Stamp2) And Now < \"31.03.2024T02:30:00\")"
    (List.replicate 3 (Lean.Json.mkObj [("Stamp2", "2024-03-31T01:00:00"), ("Clock", "01:00:00")])) false "Europe/Berlin" =
    some ["Order/Rows/Stamp2", "Order/Rows[2]/Stamp2", "Order/Rows[3]/Stamp2"] := by native_decide

example : runRows
    "GroupFilled(/Order/Rows) And (FieldFilled(Stamp2) Or (FieldFilled(Stamp2) And Now < \"31.03.2024T02:30:00\"))"
    (List.replicate 3 (Lean.Json.mkObj [("Stamp2", "2024-03-31T01:00:00"), ("Clock", "01:00:00")])) false "Europe/Berlin" =
    some ["Order/Rows/Stamp2"] := by native_decide

example : runRows
    "(FieldNotFilled(Clock) Or Now < \"31.03.2024T02:30:00\") And FieldFilled(Stamp2) And FieldFilled(Clock)"
    [Lean.Json.mkObj [("Stamp2", "2024-03-31T01:00:00")]] false "Europe/Berlin" =
    some [] := by native_decide

example : validationRun
    "(FieldNotFilled(Stamp) Or Now < \"31.03.2024T02:30:00\") And FieldFilled(Stamp)"
    "" = some [] := by native_decide

private def classificationEnabled (text : String) : Option Bool := do
  let parsed ← (parseText .english text).toOption
  let checked ← (lowerCondition rowModel ["Order", "Rows"] false parsed.body).toOption
  pure (checked.core.anyLeaf ValidationConditionLeaf.requiresClassificationPass)

example : classificationEnabled "GroupFilled(/Order)" = some false ∧
    classificationEnabled "GroupFilled(/Order/Rows)" = some true ∧
    classificationEnabled "FieldFilled(Stamp2)" = some false ∧
    classificationEnabled "FieldNotFilled(Stamp2)" = some true ∧
    classificationEnabled "[Amount] > 0" = some true ∧
    classificationEnabled "Now < \"31.03.2024T02:30:00\"" = some false := by native_decide

private def membershipClassification (text : String) : Option Bool := do
  let membershipModel : FlatModel := { fields := [
    { id := 1, groupPath := ["Order"], name := "A", policy := { kind := .number { scale := 0, signed := true } } },
    { id := 2, groupPath := ["Order"], name := "B", policy := { kind := .number { scale := 0, signed := true } } }] }
  let parsed ← (parseText .english text).toOption
  let checked ← (lowerCondition membershipModel ["Order"] false parsed.body).toOption
  pure (checked.core.anyLeaf ValidationConditionLeaf.requiresClassificationPass)

example : membershipClassification "FieldValueNotIncludedInValueList(A, 1)" = some false ∧
    membershipClassification "NoFieldValueIncludedInValueList(A In B)" = some true ∧
    membershipClassification "AtLeastOneFieldValueIncludedInValueList(A In B)" = some false := by native_decide

example : (do
    let membershipModel : FlatModel := { fields := [
      { id := 1, groupPath := ["Order"], name := "A", policy := { kind := .number { scale := 0, signed := true } } },
      { id := 2, groupPath := ["Order"], name := "B", policy := { kind := .number { scale := 0, signed := true } } }] }
    let checked ← (elaborate membershipModel ["Order"]
      (.numberFieldValueMembership .included { base := .relative 0, groups := [], field := "A" }
        [{ base := .relative 0, groups := [], field := "B" }])).toOption
    pure ((ValidationCondition.flat (model := membershipModel) checked.core).anyLeaf
      ValidationConditionLeaf.requiresClassificationPass)) = some true := by native_decide

private def sourceRow (second : Bool) : Lean.Json := Lean.Json.mkObj [
  ("Stamp2", "2024-03-31T01:00:00"), ("Clock", "01:00:00"),
  ("Due1", if second then "2024-04-30" else "2024-03-31"),
  ("Year", if second then "2023" else "2024"), ("Day", "31"), ("Month", "03"),
  ("Partial", if second then "2024-04-00" else "2024-03-00"),
  ("Range", if second then "2024-04-01/2024-04-30" else "2024-03-01/2024-03-31")]


example : runRows
    "DateTime(Date(DayFromDate(Due1),MonthFromDate(Due1),YearFromDate(Due1)),Clock) == [Stamp2]"
    [sourceRow false, sourceRow true] = some ["Order/Rows/Stamp2"] := by native_decide

example : runRows
    "DateTime(Due1,Time(HoursFromTime(Clock),MinutesFromTime(Clock),SecondsFromTime(Clock))) == [Stamp2]"
    [sourceRow false, sourceRow true] = some ["Order/Rows/Stamp2"] := by native_decide

example : runRows "DateTime(Date(Day,Month,Year),Clock) == [Stamp2]"
    [sourceRow false, sourceRow true] = some ["Order/Rows/Stamp2"] := by native_decide

example : runRows "DateTime(ValueAsDate(Partial,LastDay),Clock) == [Stamp2]"
    [sourceRow false, sourceRow true] = some ["Order/Rows/Stamp2"] := by native_decide

example : runRows "DateTime(EndOfDateRange(Range),Clock) == [Stamp2]"
    [sourceRow false, sourceRow true] = some ["Order/Rows/Stamp2"] := by native_decide

example : [
    "DateTime(Date(Rows/Day,Rows/Month,Rows/Year),Rows/Clock) == [Rows/Stamp2]",
    "DateTime(Rows/Due1,Time(HoursFromTime(Rows/Clock))) == [Rows/Stamp2]",
    "DateTime(ValueAsDate(Rows/Partial,LastDay),Rows/Clock) == [Rows/Stamp2]",
    "DateTime(EndOfDateRange(Rows/Range),Rows/Clock) == [Rows/Stamp2]"].all (fun text =>
      match parseText .english text with
      | .error _ => false
      | .ok parsed =>
          !(lowerCondition rowModel ["Order"] false parsed.body).isOk &&
          (lowerCondition rowModel ["Order"] false parsed.body
            (bindingGroup := ["Order", "Rows"])).isOk) = true := by native_decide

example : (do
    let rule ← (checkRule rowDm .english
      (rowRule "DateTime(ValueAsDate(Partial,LastDay),Clock) == [Stamp2]")).toOption
    let emptyCell : CheckedCell := { rawPresent := false, parsed := none, findings := [] }
    let result := rule.condition.core.evalAddressed {
      scalar := { fields := { read := fun _ => emptyCell }, groups := .unavailable }
      outer := [(10, 1)]
      input := .legacy { instantiatedRows := [], rawCells := fun _ => none }
        (fun _ _ => emptyCell) }
    pure (match result with | .error (.checkedDocumentRequired []) => true | _ => false)) =
    some true := by native_decide

end A12Kernel.Dm.TemporalExpressionLocks
