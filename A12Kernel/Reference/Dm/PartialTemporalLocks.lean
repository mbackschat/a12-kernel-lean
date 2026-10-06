import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Document

namespace A12Kernel.Dm.PartialTemporalLocks

private def model : FlatModel :=
  let number (id : FieldId) (name : String) (path : GroupPath := ["Form"]) (scope : List RepeatableLevel := []) : FlatFieldDecl := {
    id, name, groupPath := path, repeatableScope := scope,
    policy := { kind := .number { scale := 0, signed := false } }, numericTargetConstraints := { maxStoredLength := some 2 } }
  let date (id : FieldId) (name : String) (path : GroupPath) (scope : List RepeatableLevel) : FlatFieldDecl := {
    id, name, groupPath := path, repeatableScope := scope, policy := { kind := .temporal .date .fullDate },
    temporalTargetPolicy := some { format := "yyyy-MM-dd" } }
  { fields := [number 0 "Ref", number 2 "Amount", number 9 "N" ["Form", "Rows"] [100],
      { id := 1, name := "Key", groupPath := ["Form"], policy := { kind := .string } },
      { id := 3, name := "Bad", groupPath := ["Form"], policy := { kind := .string }, stringPolicy := { maxLength := some 2 }, stringExtensibleEnum := true },
      date 4 "Low" ["Form"] [], date 5 "High" ["Form"] [], date 6 "D" ["Form", "Rows"] [100],
      { id := 7, name := "T", groupPath := ["Form", "Rows"], repeatableScope := [100],
        policy := { kind := .temporal .time .time }, temporalTargetPolicy := some { format := "HH:mm:ss" } },
      { id := 8, name := "S", groupPath := ["Form", "Rows"], repeatableScope := [100],
        policy := { kind := .string }, stringPolicy := { maxLength := some 2 }, stringPatternSource := some "[0-9]+" },
      { id := 10, name := "Id", groupPath := ["Form", "Rows"], repeatableScope := [100], policy := { kind := .string } },
      { id := 11, name := "PD", groupPath := ["Form", "Rows"], repeatableScope := [100],
        policy := { kind := .temporal .date .fullDate }, temporalTargetPolicy := some { format := "yyyy-MM-dd", partialMode := .yearOptional } },
      { id := 12, name := "Stamp", groupPath := ["Form", "Rows"], repeatableScope := [100],
        policy := { kind := .temporal .dateTime .now }, temporalTargetPolicy := some { format := "yyyy-MM-dd'T'HH:mm:ss" } },
      date 13 "D" ["Form", "Rows", "Items"] [100,200], date 14 "D" ["Form", "Rows", "Dates"] [100],
      date 15 "E" ["Form", "Rows", "Dates"] [100]]
    repeatableGroups := [{ level := 100, path := ["Form", "Rows"], repeatability := some 2, indexField := some 10 },
      { level := 200, path := ["Form", "Rows", "Items"], repeatability := some 2 }]
    timeZoneId := "UTC", baseYear := some 2024 }

private def world : World := { now := { epochMillis := 0 } }
private structure Scenario where
  key : String := "B"
  firstId : String := "A"
  date : String := "2024-02-01"
  firstDate : String := "2024-01-01"
  time : String := "03:04:05"
  number : String := "3"
  text : String := "1"
  partialDate : String := "2024-02-00"
  bad : String := "x"
  omitted : Bool := false
  children : Option (List String) := some ["2024-02-01", "2024-03-01"]

private def input (scenario : Scenario) : Lean.Json :=
  let row (id date : String) (selected : Bool) := Lean.Json.mkObj
    ([("Id", .str id), ("T", .str (if selected then scenario.time else "01:02:03")),
      ("S", .str (if selected then scenario.text else "2")), ("N", .str (if selected then scenario.number else "1")),
      ("PD", .str scenario.partialDate), ("Stamp", .str (date ++ "T03:04:05")),
      ("Dates", Lean.Json.mkObj [("D", .str date), ("E", .str "2024-03-01")])] ++
      (if selected && scenario.omitted then [] else [("D", .str date)]) ++
      (if selected then scenario.children.toList.map (fun children => ("Items", .arr
        (children.map (fun child => Lean.Json.mkObj [("D", .str child)])).toArray))
       else [("Items", .arr #[Lean.Json.mkObj [("D", .str date)]])]))
  Lean.Json.mkObj [("Form", Lean.Json.mkObj [("Ref", .str "1"), ("Key", .str scenario.key), ("Amount", .str "1"),
    ("Bad", .str scenario.bad), ("Low", .str "2024-03-01"), ("High", .str "2024-04-01"),
    ("Rows", .arr #[row scenario.firstId scenario.firstDate false, row "B" scenario.date true])])]

private def checked (scenario : Scenario := {}) : Option (CheckedDocument model) := do
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let raw ← (readDocument { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
    (input scenario)).toOption
  (checkDocument prepared "en_US" raw.data).toOption

private inductive ReadChange where
  | unchanged | unavailable | malformed | value (payload : Value) | structural | unavailableError

private def readChanged (document : CheckedDocument model) (field : FieldId) (change : ReadChange) :
    Env → FieldId → Except CheckedAddressingError (Option CheckedCell) := fun row current =>
  if current != field then (document.fullValidationAddressedCell row current).map (fun addressed => some addressed.cell)
  else match change with
    | .unchanged => (document.fullValidationAddressedCell row current).map (fun addressed => some addressed.cell)
    | .unavailable => pure none
    | .malformed => pure (some malformedCheckedCell)
    | .value payload => pure (some (checkAdmittedRawCell (.parsed payload)))
    | .structural => .error (.checkedDocumentRequired ["injected"])
    | .unavailableError => .error (.partialUnavailable row current)

private def context (document : CheckedDocument model) (field : FieldId := 99)
    (change : ReadChange := .unchanged) (row : Env := []) : AddressedValidationEvaluationContext model := {
  scalar := { fields := document.flatContext.withWorld world, groups := GroupPresenceContext.unavailable }
  outer := row, input := .partialView document (readChanged document field change) }

private def partialLeaf (text : String) (scenario : Scenario := {})
    (scope : ValidationRelevanceScope := .full) (field : FieldId := 99)
    (change : ReadChange := .unchanged) (row : Env := []) (group : GroupPath := ["Form"]) :
    Option (Except CheckedAddressingError Verdict) := do
  let document ← checked scenario
  let parsed ← (parseText .english text).toOption
  let condition ← (lowerCondition model group false parsed.body (world := world)).toOption
  let .leaf leaf := condition.core | none
  leaf.evalAddressedPartial? (context document field change row) scope
    (fun field => scope.coversField model field row) (fun _ _ => .error (.checkedDocumentRequired [])) none

private def partialMatches (actual : Option (Except CheckedAddressingError Verdict))
    (expected : Except CheckedAddressingError Verdict) : Bool :=
  match actual, expected with
  | some (.ok actual), .ok expected => actual == expected
  | some (.error actual), .error expected => decide (actual = expected)
  | _, _ => false

private def partialVerdict (text : String) (scenario : Scenario := {})
    (scope : ValidationRelevanceScope := .full) : Option Verdict :=
  (partialLeaf text scenario scope).bind Except.toOption

private def fullVerdict (text : String) (scenario : Scenario := {}) : Option Verdict := do
  let document ← checked scenario
  let parsed ← (parseText .english text).toOption
  let condition ← (lowerCondition model ["Form"] false parsed.body (world := world)).toOption
  (condition.core.evalAddressed { (context document) with input := .checked document }).toOption

private def ruleFor (text : String) : Option (CheckedResolvedValidationRule model) :=
  (checkRule { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
    .english {
      name := "Temporal", group := ["Form"], errorCode := "PROBE", errorEntityRelPath := "../Ref"
      condition := "FieldFilled(Ref) And (" ++ text ++ ")", severity := "ERROR" } world).toOption

private def partialRule (text : String) (scenario : Scenario := {})
    (scope : ValidationRelevanceScope := .full) : Option Verdict := do
  let document ← checked scenario
  let rule ← ruleFor text
  let result ← (rule.evalAddressedPartial document scope (some world)).toOption
  match result with
  | .evaluated result => some result.verdict
  | .skipped => none

private def fullRule (text : String) (scenario : Scenario := {}) : Option (List String) := do
  let document ← checked scenario
  let rule ← ruleFor text
  let messages ← (runRule world document rule).toOption
  pure (messages.map fun message => (observe model message).messageType)

private def fieldRelevant (name : String) : RelevantEntityPattern := {
  path := ["Form", name], indices := [.all, .all] }
private def rowsRelevant : RelevantEntityPattern := { path := ["Form", "Rows"], indices := [.all, .all] }
private def rowField (name : String) (row : Option Nat := none) : RelevantEntityPattern := {
  path := ["Form", "Rows", name], indices := [.all, row.map RelevanceIndex.concrete |>.getD .all, .all] }
private def childField (row : Option Nat := none) (child : Option Nat := none) : RelevantEntityPattern := {
  path := ["Form", "Rows", "Items", "D"],
  indices := [.all, row.map RelevanceIndex.concrete |>.getD .all, child.map RelevanceIndex.concrete |>.getD .all, .all] }
private def coverage (entities : List RelevantEntityPattern) : ValidationRelevanceScope :=
  .partialSet (fieldRelevant "Ref" :: entities)
private def selectedCoverage (row : Nat := 2) : ValidationRelevanceScope := coverage
  ([fieldRelevant "Key", fieldRelevant "Amount", fieldRelevant "Low", rowField "Id"] ++
    ["D", "T", "N", "S", "PD", "Stamp"].map (fun field => rowField field (some row)))

private def positiveConditions : List String := [
  "[Rows/D For Key] == \"01.02.2024\"", "[Rows/T For Key] == \"03:04:05\"",
  "[Rows/Stamp For Key] == \"01.02.2024T03:04:05\"", "[Rows/D For \"B\"] == \"01.02.2024\"",
  "HoursFromTime(Rows/T For Key) == 3", "MinutesFromTime(Rows/T For Key) == 4", "SecondsFromTime(Rows/T For Key) == 5",
  "DayFromDate(Rows/D For Key) == 1", "AddDays(Rows/D For Key,[Amount]) == \"02.02.2024\"",
  "AddDays(Rows/D For Key,HoursFromTime(Rows/T For Key)) == \"04.02.2024\"",
  "Time(Rows/N For Key,\"4\",\"5\") == \"03:04:05\"",
  "Date(DayFromDate(Rows/D For Key),\"2\",\"2024\") == \"01.02.2024\"",
  "Valid(Date(Rows/S For Key,\"2\",\"2024\"))",
  "DateTime(Rows/D For Key,Rows/T For Key) == \"01.02.2024T03:04:05\"",
  "Min([Rows/D For Key],\"01.03.2024\") == \"01.02.2024\"",
  "MinValue(Rows/D For Key,Low) == \"01.02.2024\"",
  "MinValue(Rows*/D) == \"01.01.2024\"", "MaxValue(Rows*/D) == \"01.02.2024\"",
  "MinValue(Rows/Items*/D For Key) == \"01.02.2024\""]

example : positiveConditions.all (fun text =>
    partialVerdict text == some (.fired .value) && fullVerdict text == some (.fired .value) &&
    partialRule text == some (.fired .value) && fullRule text == some ["VALUE_ERROR"]) = true := by native_decide

example : ["[Low] == \"01.03.2024\"", "Time() == \"00:00:00\"",
    "Valid(Date(Bad,\"2\",\"2024\"))", "Valid(Date(Bad,\"2\"))"].all (fun text =>
      partialVerdict text { bad := "1" } == fullVerdict text { bad := "1" } &&
      partialRule text { bad := "1" } == some (.fired .value)) = true := by native_decide

example : ["D", "T", "Stamp"].all (fun field =>
    let constant := if field == "D" then "01.02.2024" else if field == "T" then "03:04:05" else "01.02.2024T03:04:05"
    let variableText := s!"[Rows/{field} For Key] == \"{constant}\""
    let literal := s!"[Rows/{field} For \"B\"] == \"{constant}\""
    partialVerdict variableText {} (coverage [rowsRelevant]) == some .unknown &&
    partialRule variableText {} (coverage [rowsRelevant]) == some .unknown &&
    partialVerdict literal {} (coverage [rowsRelevant]) == some (.fired .value) &&
    partialVerdict literal {} (coverage [fieldRelevant "Key", rowField field]) == some .unknown &&
    partialVerdict variableText {} (selectedCoverage) == some (.fired .value) &&
    partialVerdict variableText {} (selectedCoverage 1) == some .unknown &&
    partialMatches (partialLeaf literal {} .full 1 .structural) (.ok (.fired .value))) = true := by native_decide

example : ["D", "T", "Stamp"].all (fun field =>
    let text := s!"[Rows/{field} For Key] == [Rows/{field} For Key]"
    partialVerdict text { firstId := "B" } (coverage [fieldRelevant "Key", rowsRelevant]) == some .unknown &&
    partialVerdict text { firstId := "B" } (selectedCoverage) == some .unknown) = true := by native_decide

example : ["Valid", "Invalid"].all (fun op =>
    let text := s!"{op}(Date(Rows/S For Key,\"2\",\"2024\"))"
    partialRule text {} (selectedCoverage) == some (if op == "Valid" then .fired .value else .notFired) &&
    partialRule text {} (coverage [fieldRelevant "Key", rowField "Id"]) == some .unknown &&
    partialRule text { key := "Z" } == some (if op == "Valid" then .notFired else .fired .omission) &&
    partialRule text { text := "32" } == some (if op == "Valid" then .notFired else .fired .value) &&
    partialRule text { text := "" } == some (if op == "Valid" then .notFired else .fired .omission) &&
    partialRule text { firstId := "B" } == some .unknown) = true := by native_decide

example : ["FirstDay", "LastDay"].all (fun endpoint =>
    let day := if endpoint == "FirstDay" then "01" else "29"
    let text := s!"ValueAsDate(Rows/PD For Key,{endpoint}) == \"{day}.02.2024\""
    let minimum := s!"Min(ValueAsDate(Rows/PD For Key,{endpoint}),\"15.02.2024\") == \"15.02.2024\""
    partialVerdict text == some (.fired .value) &&
    partialRule text {} (selectedCoverage) == some (.fired .value) &&
    partialRule text {} (coverage [fieldRelevant "Key", rowField "Id"]) == some .unknown &&
    partialRule minimum { partialDate := "0000-00-00" } == some .unknown &&
    partialRule minimum { partialDate := "" } == some (.fired .omission) &&
    partialRule minimum { partialDate := "bad" } == some .unknown) = true := by native_decide

example : ["HoursFromTime", "MinutesFromTime", "SecondsFromTime"].all (fun op =>
    partialRule s!"{op}(Time(Rows/N For Key)) == 0" { number := "24" } == some (.fired .value) &&
    partialRule s!"{op}(Time(Rows/N For Key)) == 0" { number := "" } == some (.fired .omission) &&
    partialRule s!"{op}(Time(Rows/N For Key)) == 0" {} (coverage [fieldRelevant "Key", rowField "Id"]) == some .unknown &&
    partialRule s!"{op}(Rows/T For Key) == 0" { time := "bad" } == some .unknown) = true := by native_decide

example : partialRule "Time(HoursFromTime(Rows/T For Key),Bad) == \"03:04:00\" And FieldNotFilled(Ref)"
      {} (coverage [fieldRelevant "Bad", fieldRelevant "Key", rowField "Id"]) == some (.fired .value) ∧
    partialRule "Valid(Date(DayFromDate(Rows/D For Key),Bad,\"2024\")) And FieldNotFilled(Ref)"
      {} (coverage [fieldRelevant "Bad", fieldRelevant "Key", rowField "Id"]) == some (.fired .value) ∧
    partialMatches (partialLeaf "Valid(Date(DayFromDate(Rows/D For Key),Bad,\"2024\"))"
      {} (coverage [fieldRelevant "Bad", fieldRelevant "Key", rowField "Id"])) (.error .temporalUnavailable) := by native_decide

example : ["Time(HoursFromTime(Rows/T For Key),Bad) == \"03:04:00\"",
    "Valid(Date(DayFromDate(Rows/D For Key),Bad,\"2024\"))"].all (fun condition =>
    partialRule (condition ++ " And FieldNotFilled(Ref)") { bad := "1" }
      (coverage [fieldRelevant "Bad", fieldRelevant "Key", rowField "Id"]) == some .notFired) = true := by native_decide

example : partialRule "Invalid(Date(DayFromDate(Rows/D For Key),Rows/N For Key,\"2024\"))"
      { number := "long" } (coverage [fieldRelevant "Key", rowField "Id", rowField "N"]) == some .unknown ∧
    partialRule "Invalid(Date(DayFromDate(Rows/D For Key),Rows/N For Key,\"2024\"))"
      {} (coverage [fieldRelevant "Key", rowField "Id", rowField "N"]) == some .unknown := by native_decide

example : ["[Rows/D For Key] == \"01.02.2024\"", "Time(Rows/N For Key) == \"03:00:00\"",
    "Valid(Date(Rows/S For Key,\"2\",\"2024\"))"].all (fun text =>
    partialMatches (partialLeaf text {} .full 1 .structural) (.error (.checkedDocumentRequired ["injected"])) &&
    partialMatches (partialLeaf text {} .full 1 .unavailableError) (.ok .unknown)) = true := by native_decide

example : ["[Rows/D For Key] == \"01.02.2024\"", "DayFromDate(Rows/D For Key) == 1"].all (fun text =>
    partialMatches (partialLeaf text {} .full 6 .unavailable) (.ok .unknown) &&
    partialMatches (partialLeaf text {} .full 6 .malformed) (.ok .unknown) &&
    partialMatches (partialLeaf text {} .full 6 .structural) (.error (.checkedDocumentRequired ["injected"])) &&
    partialMatches (partialLeaf text {} .full 6 .unavailableError) (.error (.partialUnavailable [(100,2)] 6))) = true := by native_decide

example : partialMatches (partialLeaf "DayFromDate(Rows/D For Key) == 1" {} .full 1 (.value (.str "A")))
      (.ok (.fired .value)) ∧
    partialMatches (partialLeaf "Time(Rows/N For Key) == \"04:00:00\"" {} .full 9 (.value (.num 4)))
      (.ok (.fired .value)) ∧
    partialMatches (partialLeaf "ValueAsDate(Rows/PD For Key,LastDay) == \"31.03.2024\"" {} .full 11
      (.value (.partialDate "2024-03-00"))) (.ok (.fired .value)) := by native_decide

example : ["MinValue(Rows*/D) == \"01.01.2024\"", "MaxValue(Rows*/D) == \"01.02.2024\""].all (fun text =>
    partialRule text {} (coverage [rowField "D"]) == some (.fired .value) &&
    partialRule text {} (selectedCoverage) == some .unknown &&
    partialRule text {} (selectedCoverage 1) == some .unknown) = true := by native_decide

example : ["MinValue(Rows/Dates For Key)", "MinValue(Rows/Items*/D For Key)", "MinValue(Rows/Items* For Key)"].all (fun source =>
    let text := source ++ " == \"01.02.2024\""
    partialRule text == some (.fired .value) &&
    partialRule text {} (coverage [fieldRelevant "Key", rowField "Id",
      { path := ["Form", "Rows", "Dates"], indices := [.all, .concrete 2, .all] }, childField (some 2)]) == some (.fired .value)) = true := by native_decide

example : ["MinValue(Low,High)", "MinValue(Rows*/Dates,Low)"].all (fun source =>
    partialRule (source ++ " == \"01.03.2024\"") {} (coverage [fieldRelevant "Low", fieldRelevant "High"]) ==
      some (if source == "MinValue(Low,High)" then .fired .value else .unknown)) = true := by native_decide

example : ["MinValue", "MaxValue"].all (fun operator =>
    let text := operator ++ "(Rows/D For Key,Low) == \"01.03.2024\""
    fullVerdict text { key := "Z" } == some (.fired .omission) &&
    partialVerdict text { key := "Z" } == some (.fired .omission)) = true := by native_decide

example : partialRule "MinValue(Rows/Items*/D For Key) == \"01.02.2024\"" {}
      (coverage [fieldRelevant "Key", rowField "Id", childField (some 2) (some 1)]) == some .unknown ∧
    partialRule "MinValue(Rows/Items*/D For Key) == \"01.02.2024\"" { children := none }
      (coverage [fieldRelevant "Key", rowField "Id", childField (some 2)]) == some .notFired ∧
    partialRule "MinValue(Rows/D For Key,Low) == \"01.03.2024\"" { key := "Z" }
      (coverage [fieldRelevant "Key", fieldRelevant "Low", rowField "Id", rowField "D"]) == some (.fired .omission) ∧
    partialRule "MinValue(Rows/D For Key,Low) == \"01.03.2024\"" { key := "Z" }
      (selectedCoverage) == some .unknown := by native_decide

example : partialMatches (partialLeaf "[D] == \"01.02.2024\"" {} (selectedCoverage) 99 .unchanged [(100,2)] ["Form","Rows"])
      (.ok (.fired .value)) ∧
    partialMatches (partialLeaf "[D] == \"01.02.2024\"" {} (selectedCoverage 1) 99 .unchanged [(100,2)] ["Form","Rows"])
      (.ok .unknown) := by native_decide

example : ["[Rows/D For Key] == \"01.02.2024\"", "[Rows/D For \"B\"] == \"01.02.2024\"",
    "DayFromDate(Rows/D For Key) == 1"].all (fun condition =>
    partialRule condition { firstId := "B" }
      (coverage [fieldRelevant "Key", rowField "Id" (some 2), rowField "D" (some 2)]) == some (.fired .value)) = true := by native_decide

example : ["MinValue", "MaxValue"].all (fun operator =>
    let condition := operator ++ "(Rows/D For Key,Low) == \"01.03.2024\""
    partialRule condition { key := "Z" }
      (coverage [fieldRelevant "Key", fieldRelevant "Low", rowField "Id" (some 2), rowField "D"]) == some .unknown &&
    partialRule condition { key := "Z" }
      (coverage [fieldRelevant "Key", fieldRelevant "Low", rowField "Id", rowField "D" (some 2)]) == some .unknown) = true := by native_decide

private def partialRepeated (text : String) (scenario : Scenario := {})
    (scope : ValidationRelevanceScope := .full) : Option (List (Option Verdict)) := do
  let document ← checked scenario
  let rule ← (checkRule { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
    .english {
      name := "RowsTemporal", group := ["Form", "Rows"], errorCode := "PROBE"
      errorEntityRelPath := "../N", condition := "FieldFilled(N) And (" ++ text ++ ")", severity := "ERROR" } world).toOption
  match ← (rule.evalOrdinaryRepeatablePartial document scope (some world)).toOption with
  | .skipped => none
  | .evaluated rows => pure (rows.map fun (_, result) => match result with
      | .skipped => none
      | .evaluated outcome => some outcome.verdict)

example : partialRepeated "HoursFromTime(T) == 3" == some [some .notFired, some (.fired .value)] ∧
    partialRepeated "HoursFromTime(T) == 3" {} (selectedCoverage) == some [none, some (.fired .value)] ∧
    partialRepeated "Time(HoursFromTime(T),../Bad) == \"03:04:00\" And FieldNotFilled(N)" {}
      (coverage [fieldRelevant "Bad", rowField "N"]) == some [some (.fired .value)] ∧
    partialRepeated "Time(HoursFromTime(T),../Bad) == \"03:04:00\" And FieldNotFilled(N)" { bad := "1" }
      (coverage [fieldRelevant "Bad", rowField "N"]) == some [some .notFired, some .notFired] := by native_decide

example : (do
    let document ← checked
    let rule ← ruleFor "MinValue(Rows*/D Having [Rows/D] == [Rows/D]) == \"01.01.2024\""
    let result ← (rule.evalAddressedPartial document .full (some world)).toOption
    pure (rule.hasHaving && match result with | .skipped => true | _ => false)) = some true := by native_decide

private def mixedPrecision (operator : String) (scope : ValidationRelevanceScope) : Option (Verdict × Verdict) := do
  let fixture := { model with fields := model.fields.map fun field => if field.id == 6 then
    { field with
      policy := { kind := .temporal .date { TemporalComponents.fullDate with year := false } }
      temporalTargetPolicy := some { format := "MM-dd" } } else field }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler fixture).toOption
  let raw ← (readDocument { flat := fixture, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
    (input { date := "02-01", firstDate := "01-01" })).toOption
  let document ← (checkDocument prepared "en_US" raw.data).toOption
  let expected := if operator == "MinValue" then "01.02.2024" else "01.03.2024"
  let parsed ← (parseText .english (operator ++ "(Rows/D For Key,Low) == \"" ++ expected ++ "\"")).toOption
  let condition ← (lowerCondition fixture ["Form"] false parsed.body (world := world)).toOption
  let .leaf leaf := condition.core | none
  let context : AddressedValidationEvaluationContext fixture := {
    scalar := { fields := document.flatContext.withWorld world, groups := GroupPresenceContext.unavailable },
    outer := [], input := .checked document }
  let full ← (condition.core.evalAddressed context).toOption
  let part ← (← leaf.evalAddressedPartial? context scope (fun field => scope.coversField fixture field [])
    (fun _ _ => .error (.checkedDocumentRequired [])) none).toOption
  pure (full, part)

example : ["MinValue", "MaxValue"].all (fun operator =>
    mixedPrecision operator (selectedCoverage) == some (.fired .value, .fired .value) &&
    mixedPrecision operator (coverage [fieldRelevant "Key", rowField "Id", fieldRelevant "Low"]) ==
      some (.fired .value, .unknown)) = true := by native_decide

end A12Kernel.Dm.PartialTemporalLocks
