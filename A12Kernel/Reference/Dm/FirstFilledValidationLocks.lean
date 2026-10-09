import A12Kernel.Reference.Dm.Replay
import A12Kernel.Reference.Dm.LowerDocument

namespace A12Kernel.Dm.FirstFilledValidationLocks

open Lean A12Kernel A12Kernel.Dm

private def runOutcomes (prototype : FlatFieldDecl) (condition : String)
    (first second : Option String) (fallback : Option String := none)
    (rows : List (Option String × Option String) := []) (bound : Bool := false) (partialScope : Option ValidationRelevanceScope := none)
    (descendantError : Bool := false) : Option (List Verdict) := do
  let model : FlatModel := {
    timeZoneId := "Europe/Berlin"
    fields := [
      { id := 1, groupPath := ["Form"], name := "Error", policy := { kind := .string } },
      { prototype with id := 2, groupPath := ["Form", "Values"], name := "A" },
      { prototype with id := 3, groupPath := ["Form", "Values"], name := "B" },
      { prototype with id := 4, groupPath := ["Form"], name := "Fallback" },
      { prototype with id := 5, groupPath := ["Form", "Rows"], name := "A", repeatableScope := [10] },
      { prototype with id := 6, groupPath := ["Form", "Rows"], name := "B", repeatableScope := [10] }]
    repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 2 }] }
  let dm : DmModel := {
    flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let pair := fun (a b : Option String) => Json.mkObj (
    a.toList.map (fun value => ("A", Json.str value)) ++
    b.toList.map (fun value => ("B", Json.str value)))
  let input ← (readDocument dm (Json.mkObj [("Form", Json.mkObj (
    [("Error", Json.str "ready"), ("Values", pair first second),
      ("Rows", Json.arr (rows.map (fun (a, b) => pair a b)).toArray)] ++
    fallback.toList.map (fun value => ("Fallback", Json.str value))))])).toOption
  let world : World := {
    now := { epochMillis := 0 }
    customFieldValidator? := fun name => if name == "Code" then some (fun _ _ => none) else none }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let document ← (checkDocument prepared "en_US" input.data).toOption
  let rule ← (checkRule dm .english {
    group := if bound then ["Form", "Rows"] else ["Form"], name := "Selected", errorCode := "SELECTED",
    errorEntityRelPath := if descendantError then "../Rows/B" else if bound then "../B" else "../Error",
    condition := (if bound then "FieldFilled(B) And (" else "FieldFilled(Error) And (") ++ condition ++ ")", severity := "ERROR" }).toOption
  if let some scope := partialScope then
    match rule.ordinaryIterationPlan with
    | .scalar =>
        match ← (rule.evalAddressedPartial document scope (some world)).toOption with
        | .skipped => return []
        | .evaluated outcome => return [outcome.verdict]
    | .once _ =>
        match ← (rule.evalOrdinaryOncePartial document scope (some world)).toOption with
        | .skipped => return []
        | .evaluated _ outcome => return [outcome.verdict]
    | .rows _ =>
        match ← (rule.evalOrdinaryRepeatablePartial document scope (some world)).toOption with
        | .skipped => return []
        | .evaluated rows => return rows.filterMap fun (_, result) =>
            match result with | .skipped => none | .evaluated outcome => some outcome.verdict
  let context : AddressedValidationEvaluationContext model := {
    scalar := { fields := document.flatContext.withWorld world, groups := GroupPresenceContext.unavailable }
    outer := [], input := .checked document }
  match rule.ordinaryIterationPlan with
  | .scalar => pure [(← (rule.evalAddressedFull context true).toOption).verdict]
  | .once _ => pure [(← (rule.evalOrdinaryOnceFull document (some world)).toOption).2.verdict]
  | .rows _ => pure ((← (rule.evalOrdinaryRepeatableFull document (some world)).toOption).map (·.2.verdict))

private def run (prototype : FlatFieldDecl) (condition : String)
    (first second : Option String) (fallback : Option String := none)
    (rows : List (Option String × Option String) := []) (bound : Bool := false) : Option Verdict := do
  (← runOutcomes prototype condition first second fallback rows bound).head?

private def number : FlatFieldDecl := {
  id := 0, groupPath := ["Form"], name := "N", policy := { kind := .number { scale := 0, signed := true } } }

private def text : FlatFieldDecl := {
  id := 0, groupPath := ["Form"], name := "T", policy := { kind := .string } }

example : run number "FirstFilledValue(Values) == 7" (some "7") (some "bad") =
      some (.fired .value) ∧
    run number "FirstFilledValue(Values, Fallback) == 9" none none (some "9") =
      some (.fired .omission) ∧
    run number "FirstFilledValue(Values) == 0" (some "bad") none = some .unknown := by native_decide

example : run text "FirstFilledValue(Values) == \"first\"" (some "first") (some "later") =
      some (.fired .value) ∧
    run text "FirstFilledValue(Values, Rows*, Fallback) == \"last\"" none none (some "last") =
      some (.fired .omission) := by native_decide

example : run text "FirstFilledValue(Rows*) == \"selected\"" none none none
      [(none, some "selected"), (some "later", none)] = some .notFired ∧
    run number "FirstFilledValue(Rows*) == 3" none none none
      [(none, some "3"), (some "2", none)] = some .notFired := by native_decide

example : run text "FirstFilledValue(A, B) == \"selected\"" none none none
      [(none, some "selected")] true = some (.fired .omission) ∧
    run text "FirstFilledValue(A, B) == \"selected\"" none none none
      [(some "selected", some "other")] true = some (.fired .value) := by native_decide

private def boolean : FlatFieldDecl := {
  id := 0, groupPath := ["Form"], name := "B", policy := { kind := .boolean } }

private def date : FlatFieldDecl := {
  id := 0, groupPath := ["Form"], name := "D",
  policy := { kind := .temporal .date TemporalComponents.fullDate },
  temporalTargetPolicy := some { format := "yyyy-MM-dd" } }

private def range : FlatFieldDecl := {
  id := 0, groupPath := ["Form"], name := "R", policy := { kind := .dateRange },
  dateRangePolicy := some { format := "yyyy-MM-dd", separator := "/" } }

example : run boolean "FirstFilledValue(Values) == False" (some "false") (some "true") =
      some (.fired .value) ∧
    run boolean "FirstFilledValue(Values, Fallback) == True" none none (some "true") =
      some (.fired .omission) := by native_decide

example : run date "FirstFilledValue(Values) == [Fallback]" none (some "2024-03-05")
      (some "2024-03-05") = some (.fired .omission) ∧
    run date "FirstFilledValue(Values) == \"05.03.2024\"" (some "2024-03-05") (some "bad") =
      some (.fired .value) := by native_decide

example : run range "FirstFilledValue(Values) == [Fallback]" none (some "2024-03-05/2024-04-06")
      (some "2024-03-05/2024-04-06") = some (.fired .omission) := by native_decide

private def time : FlatFieldDecl := {
  id := 0, groupPath := ["Form"], name := "T",
  policy := { kind := .temporal .time TemporalComponents.time },
  temporalTargetPolicy := some { format := "HH:mm:ss" } }

private def stamp : FlatFieldDecl := {
  id := 0, groupPath := ["Form"], name := "S",
  policy := { kind := .temporal .dateTime TemporalComponents.now },
  temporalTargetPolicy := some { format := "yyyy-MM-dd'T'HH:mm:ss" } }

private def fragment : FlatFieldDecl := {
  id := 0, groupPath := ["Form"], name := "F",
  policy := { kind := .temporal .date (TemporalComponents.ofFormat "MM-dd") },
  temporalTargetPolicy := some { format := "MM-dd" } }

example : run time "FirstFilledValue(Values) < [Fallback]" (some "03:04:05") (some "bad")
      (some "04:04:05") = some (.fired .value) ∧
    run stamp "FirstFilledValue(Values) == [Fallback]" (some "2024-03-05T03:04:05") none
      (some "2024-03-05T03:04:05") = some (.fired .value) ∧
    run fragment "FirstFilledValue(Values) == [Fallback]" none (some "03-05")
      (some "03-05") = some (.fired .omission) := by native_decide

example : [boolean, date, range, time, stamp, fragment].all (fun prototype =>
    run prototype "FirstFilledValue(Values) == [Fallback]" none none none == some .notFired &&
    run prototype "FirstFilledValue(Values) == [Fallback]" (some "bad") none none == some .unknown) := by
  native_decide

example : run boolean "FirstFilledValue(Rows*) == False" none none none
      [(none, some "true"), (some "false", none)] = some (.fired .omission) ∧
    run date "FirstFilledValue(A, B) == [B]" none none none
      [(none, some "2024-03-05")] true = some (.fired .omission) ∧
    run range "FirstFilledValue(Rows*, Fallback) == FirstFilledValue(Values)" (some "2024-03-05/2024-04-06") none
      (some "2024-03-05/2024-04-06") = some (.fired .omission) := by native_decide

private def typedAdmission (a b : FlatFieldDecl) (root : Bool := false) :
    Except FirstFilledComparisonElabError Unit := do
  let group := if root then ["Form"] else ["Form", "Values"]
  let model : FlatModel := {
    fields := [{ a with id := 1, groupPath := group, name := "A" },
      { b with id := 2, groupPath := group, name := "B" }], timeZoneId := "Europe/Berlin" }
  let reference : SurfaceFieldPath := { base := .absolute, groups := group, field := "A" }
  let _ ← elaborateFirstFilledComparison model ["Form"] ["Form"] .equal
    (.firstFilled { first := .group (.path { base := .absolute, groups := group }), rest := [] })
    (.field reference)
  pure ()

example : (typedAdmission boolean boolean).isOk ∧
    (typedAdmission date date).isOk ∧ (typedAdmission range range).isOk ∧
    (match typedAdmission boolean boolean true with | .error (.shape (.rootGroupOperand _)) => true | _ => false : Bool) ∧
    (match typedAdmission date { date with temporalTargetPolicy := some { format := "dd.MM.yyyy" } } with
      | .error .varyingProfiles => true | _ => false : Bool) ∧
    (match typedAdmission range { range with dateRangePolicy := some { format := "dd.MM.yyyy", separator := "-" } } with
      | .error .varyingProfiles => true | _ => false : Bool) ∧
    !(typedAdmission boolean { boolean with policy := { kind := .confirm } }).isOk := by native_decide

example : run boolean "FirstFilledValue(Rows*/A Having FieldFilled(Rows/B)) == False" none none none
      [(some "true", none), (some "false", some "true")] = some (.fired .omission) ∧
    run date "FirstFilledValue(Values) != [Fallback]" (some "2024-03-05") none (some "2024-03-06") =
      some (.fired .value) ∧
    run range "FirstFilledValue(Values) != [Fallback]" (some "2024-03-05/2024-04-06") none
      (some "2024-03-05/2024-04-07") = some (.fired .value) := by native_decide

example : run stamp "FirstFilledValue(Values) < \"31.03.2024T02:30:00\"" (some "bad") none =
      some (.fired .value) ∧
    runOutcomes stamp "FirstFilledValue(A, B) < \"31.03.2024T02:30:00\"" none none none
      [(some "2024-03-05T03:04:05", some "2024-03-05T03:04:05"),
       (some "2024-03-05T03:04:05", some "2024-03-05T03:04:05")] true =
      some [.fired .value] := by native_decide

private def coverage (paths : List (List String)) : ValidationRelevanceScope :=
  .partialSet (paths.map fun path => { path, indices := path.map fun _ => .all })

example : runOutcomes boolean "FirstFilledValue(Values) == True" (some "true") none
      (partialScope := some (coverage [["Form", "Error"], ["Form", "Values", "A"]])) =
      some [.fired .value] ∧
    runOutcomes boolean "FirstFilledValue(Values) == True" none (some "true")
      (partialScope := some (coverage [["Form", "Error"], ["Form", "Values", "B"]])) =
      some [.unknown] ∧
    runOutcomes boolean "FirstFilledValue(Values) == True" none (some "true")
      (partialScope := some .full) = some [.fired .omission] := by native_decide

example : runOutcomes date "FirstFilledValue(Values) == [Fallback]" none (some "2024-03-05") (some "2024-03-05")
      (partialScope := some .full) = some [.fired .omission] ∧
    runOutcomes range "FirstFilledValue(Values) == [Fallback]" none (some "2024-03-05/2024-04-06")
      (some "2024-03-05/2024-04-06") (partialScope := some .full) = some [.fired .omission] := by native_decide

private def localRead (unavailable : Bool) : Option Verdict := do
  let model : FlatModel := {
    fields := [{ boolean with id := 1, groupPath := ["Form", "Values"], name := "A" },
      { boolean with id := 2, groupPath := ["Form", "Values"], name := "B" }] }
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } } builtinStringPatternCompiler model).toOption
  let document ← (checkDocument prepared "en_US" { instantiatedRows := [], cells := [
    { address := { field := 1, path := [] }, stored := "true", raw := .parsed (.bool true) }] }).toOption
  let comparison ← (elaborateFirstFilledComparison model ["Form"] ["Form"] .equal
    (.firstFilled { first := .group (.path { base := .absolute, groups := ["Form", "Values"] }), rest := [] })
    (.boolean true)).toOption
  let result ← comparison.evaluatePartial? document [] document.flatContext .full fun _ field =>
    if field == 1 then pure (if unavailable then none else some (checkAdmittedRawCell (.parsed (.bool true))))
    else .error (.partialUnavailable [] field)
  result.toOption

example : localRead false = some (.fired .value) ∧ localRead true = some .unknown := by native_decide

example : runOutcomes stamp "FirstFilledValue(Values) < \"31.03.2024T02:30:00\"" (some "bad") none
      (partialScope := some .full) = some [.fired .value] ∧
    runOutcomes boolean "FirstFilledValue(Rows*/A Having FieldFilled(Rows/B)) == False" none none none
      [(some "false", some "true")] (partialScope := some .full) = some [] := by native_decide

example : [(number, "7", "7"), (text, "selected", "\"selected\"")].all (fun (prototype, value, literal) =>
    let condition := "FirstFilledValue(Values) == " ++ literal
    runOutcomes prototype condition (some value) none
      (partialScope := some (coverage [["Form", "Error"], ["Form", "Values", "A"]])) == some [.fired .value] &&
    runOutcomes prototype condition none (some value)
      (partialScope := some (coverage [["Form", "Error"], ["Form", "Values", "B"]])) == some [.unknown] &&
    runOutcomes prototype condition none (some value) (partialScope := some .full) == some [.fired .omission]) := by
  native_decide

example : run text "FirstFilledValue(Values) == [Fallback]" none (some "selected") (some "selected") =
      some (.fired .omission) ∧
    runOutcomes text "[Fallback] != FirstFilledValue(Values)" (some "selected") none (some "different")
      (partialScope := some .full) = some [.fired .value] := by native_decide

private def selectedReadback (prototype : FlatFieldDecl) (stored : String) (value : Value)
    (condition : String) (unavailable : Bool) : Option Verdict := do
  let model : FlatModel := {
    fields := [{ prototype with id := 1, groupPath := ["Form", "Values"], name := "A" },
      { prototype with id := 2, groupPath := ["Form", "Values"], name := "B" }] }
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } } builtinStringPatternCompiler model).toOption
  let document ← (checkDocument prepared "en_US" { instantiatedRows := [], cells := [
    { address := { field := 1, path := [] }, stored, raw := .parsed value }] }).toOption
  let parsed ← (parseText .english condition).toOption
  let checked ← (lowerCondition model ["Form"] false parsed.body).toOption
  let .leaf leaf := checked.core | none
  let context : AddressedValidationEvaluationContext model := {
    scalar := { fields := document.flatContext, groups := GroupPresenceContext.unavailable }, outer := []
    input := .partialView document fun _ field =>
      if field == 1 then pure (if unavailable then none else some (checkAdmittedRawCell (.parsed value)))
      else .error (.partialUnavailable [] field) }
  let result ← leaf.evalAddressedPartial? context .full (fun _ => true)
    (fun _ _ => .error (.checkedDocumentRequired [])) none
  result.toOption

example : selectedReadback number "7" (.num 7) "FirstFilledValue(Values) == 7" false = some (.fired .value) ∧
    selectedReadback number "7" (.num 7) "FirstFilledValue(Values) == 7" true = some .unknown := by native_decide

example : selectedReadback text "selected" (.str "selected") "FirstFilledValue(Values) == \"selected\"" false = some (.fired .value) ∧
    selectedReadback text "selected" (.str "selected") "FirstFilledValue(Values) == \"selected\"" true = some .unknown := by native_decide

private def enumeration : FlatFieldDecl := {
  id := 0, groupPath := ["Form"], name := "E", policy := { kind := .enumeration },
  enumeration := some { storedTokens := ["A", "B"], categories := [] } }

example : run enumeration "FirstFilledValue(Values) == [Fallback]" none (some "A") (some "A") =
      some (.fired .omission) ∧
    runOutcomes enumeration "FirstFilledValue(Values) != [Fallback]" (some "A") none (some "B")
      (partialScope := some .full) = some [.fired .value] ∧
    runOutcomes enumeration "FirstFilledValue(Values) == [Fallback]" (some "invalid") (some "A") (some "A")
      (partialScope := some .full) = some [.unknown] := by native_decide

private def custom : FlatFieldDecl := { text with customType := some { name := "Code" } }

example : [(number, "7"), (text, "selected"), (enumeration, "A"), (custom, "code"),
    (boolean, "false"), (date, "2024-03-05"), (fragment, "03-05"), (time, "03:04:05"),
    (stamp, "2024-03-05T03:04:05"), (range, "2024-03-05/2024-04-06")].all (fun (prototype, value) => [none, some ValidationRelevanceScope.full].all fun partialScope =>
      runOutcomes prototype "FirstFilledValue(A, B) == [B]" none none none
        [(none, some value), (some value, some value)] true (partialScope := partialScope) ==
          some [.fired .omission, .fired .value]) := by native_decide

example : run date "FirstFilledValue(Values) == Date(DayFromDate(Fallback), \"03\", \"2024\")"
      (some "2024-03-05") none (some "bad") = some .unknown := by native_decide

private def shortTime : FlatFieldDecl := { time with
  policy := { kind := .temporal .time (TemporalComponents.ofFormat "HH:mm") },
  temporalTargetPolicy := some { format := "HH:mm" } }

example : !(typedAdmission shortTime shortTime).isOk := by native_decide

example : [none, some ValidationRelevanceScope.full].all (fun partialScope =>
    runOutcomes text "FirstFilledValue(Rows/A, Rows/B) == \"x\"" none none none
      [(none, some "x"), (some "y", some "x")] (partialScope := partialScope)
      (descendantError := true) == some [.fired .omission, .notFired]) := by native_decide

example : [none, some ValidationRelevanceScope.full].all (fun partialScope =>
    runOutcomes enumeration "FieldFilled(Rows/B) And (FieldFilled(Fallback) Or FirstFilledValue(Rows/A, Rows/B) != \"A\")" none none none
      [(some "B", some "A"), (some "A", some "B")] (partialScope := partialScope)
      (descendantError := true) == some [.fired .value, .notFired]) := by native_decide

private def selectedOutcome (prototype : FlatFieldDecl) (value : String) (operand : String)
    (first : String) (paths : List (List String)) (partialRun : Bool := true) : Option Verdict := do
  let model : FlatModel := {
    timeZoneId := "Europe/Berlin"
    fields := [
      { id := 1, groupPath := ["Form"], name := "Error", policy := { kind := .string } },
      { id := 2, groupPath := ["Form", "Rows"], name := "Code", repeatableScope := [10], policy := { kind := .string } },
      { prototype with id := 3, groupPath := ["Form", "Rows", "Body"], name := "A", repeatableScope := [10] },
      { prototype with id := 4, groupPath := ["Form", "Rows", "Body"], name := "B", repeatableScope := [10] },
      { prototype with id := 5, groupPath := ["Form"], name := "Fallback" }]
    repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 2, indexField := some 2 }] }
  let input ← (readDocument { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
    (Json.mkObj [("Form", Json.mkObj [("Error", .str "ready"), ("Fallback", .str value),
      ("Rows", .arr #[Json.mkObj [("Code", .str "R1"), ("Body", Json.mkObj [("A", .str first), ("B", .str "bad")])]])])])).toOption
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } } builtinStringPatternCompiler model).toOption
  let document ← (checkDocument prepared "en_US" input.data).toOption
  let parsed ← (parseText .english ("FieldFilled(Error) And FirstFilledValue(" ++ operand ++ ") == [Fallback]")).toOption
  let condition ← (lowerCondition model ["Form"] false parsed.body).toOption
  let rule ← (assembleResolvedValidationRule model condition 1 "PARTIAL_FIRST" .error { parts := [] }).toOption
  if !partialRun then
    return (← (rule.evalAddressedFull {
      scalar := { fields := document.flatContext, groups := GroupPresenceContext.unavailable }
      outer := [], input := .checked document } true).toOption).verdict
  let scope := coverage ((["Form", "Error"] :: ["Form", "Fallback"] :: ["Form", "Rows", "Code"] :: paths))
  match ← (rule.evalAddressedPartial document scope).toOption with
  | .skipped => none
  | .evaluated result => some result.verdict

example : [(boolean, "false"), (date, "2024-03-05"), (time, "03:04:05"),
    (stamp, "2024-03-05T03:04:05"), (range, "2024-03-05/2024-04-06")].all (fun (prototype, value) =>
    selectedOutcome prototype value "Rows/Body For \"R1\"" value [["Form", "Rows", "Body", "A"]] == some (.fired .value) &&
    selectedOutcome prototype value "Rows/Body/A For \"R1\",Fallback" value [["Form", "Rows", "Body", "A"]] == some (.fired .value) &&
    selectedOutcome prototype value "Rows/Body For \"R1\"" value [["Form", "Rows", "Body", "B"]] == some .unknown &&
    selectedOutcome prototype value "Rows/Body For \"R1\"" "" [["Form", "Rows", "Body", "A"]] == some .unknown &&
    selectedOutcome prototype value "Rows/Body For \"missing\",Fallback" value [["Form", "Rows", "Body"]] == some (.fired .omission)) = true := by native_decide

example : [(boolean, "false"), (date, "2024-03-05"), (time, "03:04:05"),
    (stamp, "2024-03-05T03:04:05"), (range, "2024-03-05/2024-04-06")].all (fun (prototype, value) =>
    selectedOutcome prototype value "Rows/Body For \"R1\"" value [] false == some (.fired .value) &&
    selectedOutcome prototype value "Rows/Body/A For \"R1\",Fallback" value [] false == some (.fired .value) &&
    selectedOutcome prototype value "Rows/Body For \"missing\",Fallback" value [] false == some (.fired .omission) &&
    selectedOutcome prototype value "Rows/Body For \"R1\"" "" [["Form", "Rows", "Body"]] == some .unknown &&
    selectedOutcome prototype value "Fallback,Rows/Body For \"missing\"" value [] == some (.fired .value)) = true := by native_decide

end A12Kernel.Dm.FirstFilledValidationLocks
