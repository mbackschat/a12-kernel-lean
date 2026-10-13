import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Document
import A12Kernel.Reference.Dm.Validate

namespace A12Kernel.Dm.RangeExpressionLocks

open Lean

private def model (format : String) (baseYear : Option Int := none) : FlatModel := {
  fields := [
    { id := 0, groupPath := ["Form"], name := "Range", policy := { kind := .dateRange },
      dateRangePolicy := some { format, separator := "/" } },
    { id := 1, groupPath := ["Form"], name := "Result",
      policy := { kind := .temporal .date (TemporalComponents.ofFormat
        (if (TemporalComponents.ofFormat format).year || baseYear.isSome then "yyyy-MM-dd" else "MM-dd")) },
      temporalTargetPolicy := some { format :=
        if (TemporalComponents.ofFormat format).year || baseYear.isSome then "yyyy-MM-dd" else "MM-dd" } }]
  timeZoneId := "UTC", baseYear }

private def admitted (model : FlatModel) (operation : String) : Bool :=
  (lowerComputation model .english {
    group := ["Form"], name := "ResultComp", targetRelPath := "../Result"
    commonPrecondition := none, alternatives := [{ precondition := none, operation }]
    errorCodesToSuppress := [] }).isOk

-- KF201 separates extraction from the consuming format gate; all five profiles reach both bounds.
example : ["yyyy-MM-dd", "yyyy", "yyyy-MM", "MM", "MM-dd"].all (fun format =>
    [none, some 2024].all (fun year =>
      ["StartOfDateRange(Range)", "EndOfDateRange(Range)",
       "Max(StartOfDateRange(Range),EndOfDateRange(Range))"].all
        (admitted (model format year)))) := by native_decide

example : admitted (model "yyyy" (some 2024)) "EndOfDateRange(BaseYear)" := by native_decide

private def comparisonAdmitted (model : FlatModel) (condition : String) : Bool :=
  match parseText .english condition with
  | .ok parsed => (lowerCondition model ["Form"] false parsed.body).isOk
  | .error _ => false

-- The static grid separates entity syntax, range kind, Base Year and consumer component gates.
example : ["StartOfDateRange", "EndOfDateRange"].all (fun op =>
    [none, some 2024].all (fun year =>
      let m := model "MM" year
      comparisonAdmitted m s!"{op}(Range) == [Result]" &&
      !comparisonAdmitted m s!"{op}([Range]) == [Result]" &&
      !comparisonAdmitted m s!"{op}(Result) == [Result]" &&
      !comparisonAdmitted m s!"AddDays({op}(Range),1) > [Result]" &&
      comparisonAdmitted m s!"AddMonths({op}(Range),1) > [Result]" &&
      (comparisonAdmitted m s!"{op}(BaseYear) == [Result]" == year.isSome))) := by
  native_decide

private def run (format : String) (year : Option Int) (text operation : String) : Option String := do
  let model := model format year
  let dm : DmModel := { flat := model, computations := [], rules := [], conditionLanguage := "en_US", refusals := [] }
  let input ← (readDocument dm (Lean.Json.mkObj [("Form", Lean.Json.mkObj [
    ("Range", Lean.toJson text), ("Result", Lean.toJson
      (if (TemporalComponents.ofFormat format).year || year.isSome then "2001-12-25" else "12-25"))])])).toOption
  if !input.refusals.isEmpty then none
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  let (_, step) ← (lowerComputation model .english {
    group := ["Form"], name := "ResultComp", targetRelPath := "../Result"
    commonPrecondition := none, alternatives := [{ precondition := none, operation }]
    errorCodesToSuppress := [] }).toOption
  pure (← (← (runComputations world prepared checked [step]).toOption).head?).outcome

-- Both endpoints keep positional completion rather than reusing a field's earliest-date default.
example :
    run "yyyy" none "2023/2024" "StartOfDateRange(Range)" = some "value 2023-01-01" ∧
    run "yyyy" none "2023/2024" "EndOfDateRange(Range)" = some "value 2024-12-31" ∧
    run "MM" none "01/02" "EndOfDateRange(Range)" = some "value 02-29" ∧
    run "MM" (some 2023) "01/02" "EndOfDateRange(Range)" = some "value 2023-02-28" ∧
    run "MM" (some 2024) "01/02" "EndOfDateRange(Range)" = some "value 2024-02-29" := by
  native_decide

example : run "yyyy" none "" "EndOfDateRange(Range)" = some "cleared" := by native_decide

-- Dependency omission would let a consumer run before its range producer or admit a target self-read.
example :
    (do
      let parsed ← (parseText .english "Max(StartOfDateRange(Range),EndOfDateRange(Range))").toOption
      let surface ← (lowerScalarTemporalExpression (model "yyyy") ["Form"] parsed.body).toOption
      let checked ← (elaborateScalarTemporalExpression (model "yyyy") ["Form"] surface).toOption
      pure checked.fieldIds) = some [0, 0] := by native_decide

private inductive IndexKind where
  | string
  | number

private def IndexKind.fieldKind : IndexKind → FieldKind
  | .string => .string
  | .number => .number { scale := 0, signed := true }

private def IndexKind.keys : IndexKind → String × String
  | .string => ("a", "b")
  | .number => ("1", "2")

private def selectionModel (kind : IndexKind) : FlatModel :=
  let key (id : FieldId) (name : String) (path : GroupPath := ["Form"])
      (scope : List RepeatableLevel := []) : FlatFieldDecl := {
    id, name, groupPath := path, repeatableScope := scope
    policy := { kind := kind.fieldKind } }
  let endpoint (id : FieldId) (name : String) : FlatFieldDecl := {
    id, name, groupPath := ["Form", "Rows"], repeatableScope := [10]
    policy := { kind := .temporal .date (TemporalComponents.ofFormat "yyyy-MM") }
    temporalTargetPolicy := some { format := "yyyy-MM" } }
  { fields := [key 1 "KeyStart", key 2 "KeyFinish", key 3 "Id" ["Form", "Rows"] [10],
      endpoint 4 "Start", endpoint 5 "Finish",
      { id := 6, name := "Range", groupPath := ["Form"], policy := { kind := .dateRange }
        dateRangePolicy := some { format := "yyyy-MM", separator := "/" } },
      { id := 7, name := "Month", groupPath := ["Form"]
        policy := { kind := .number { scale := 0, signed := true } } },
      { id := 8, name := "Guard", groupPath := ["Form"]
        policy := { kind := .number { scale := 0, signed := true } } },
      { id := 9, name := "Next", groupPath := ["Form"]
        policy := { kind := .number { scale := 0, signed := true } } }]
    repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 2, indexField := some 3 }]
    timeZoneId := "UTC" }

private inductive KeyMode where
  | literal
  | field

private inductive SelectionScenario where
  | ordinary
  | missing
  | duplicate
  | selectedInvalid
  | unselectedInvalid
  | selectedEmpty
  | emptyKey

private def selectionInput (kind : IndexKind) (scenario : SelectionScenario)
    (computedKey : Bool) (rangeStored : String := "2000-01/2000-02") : Json :=
  let (firstKey, secondKey) := kind.keys
  let (firstId, firstStart, secondStart, includeSecond, startKey) := match scenario with
    | .ordinary => (firstKey, "2024-01", "2024-02", true, secondKey)
    | .missing => (firstKey, "2024-01", "2024-02", false, secondKey)
    | .duplicate => (secondKey, "2024-01", "2024-02", true, secondKey)
    | .selectedInvalid => (firstKey, "2024-01", "bad", true, secondKey)
    | .unselectedInvalid => (firstKey, "bad", "2024-02", true, secondKey)
    | .selectedEmpty => (firstKey, "2024-01", "", true, secondKey)
    | .emptyKey => (firstKey, "2024-01", "2024-02", true, "")
  let row (id start finish : String) := Json.mkObj [
    ("Id", .str id), ("Start", .str start), ("Finish", .str finish)]
  Json.mkObj [("Form", Json.mkObj [
    ("KeyStart", .str (if computedKey then firstKey else startKey)),
    ("KeyFinish", .str firstKey), ("Range", .str rangeStored), ("Month", .str "99"),
    ("Guard", .str "99"), ("Next", .str "99"),
    ("Rows", .arr (([row firstId firstStart "2024-06"] ++
      if includeSecond then [row secondKey secondStart "2024-03"] else []).toArray))])]

private def selectionWorld : World := {
  now := { epochMillis := 0 }, modelZoneRules := ModelZone.concreteRules }

private def selectionDm (kind : IndexKind) : DmModel := {
  flat := selectionModel kind, computations := [], rules := [], conditionLanguage := "en_US", refusals := [] }

private def selectionChecked (kind : IndexKind) (scenario : SelectionScenario)
    (computedKey : Bool := false) (rangeStored : String := "2000-01/2000-02") :
    Option (PreparedFlatStringContext (selectionModel kind) builtinStringPatternCompiler ×
      CheckedDocument (selectionModel kind)) := do
  let input ← (readDocument (selectionDm kind)
    (selectionInput kind scenario computedKey rangeStored)).toOption
  if !input.refusals.isEmpty then none
  let prepared ← (prepareFlatStringContext selectionWorld builtinStringPatternCompiler
    (selectionModel kind)).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  pure (prepared, checked)

private def selectedRangeOperation (kind : IndexKind) (mode : KeyMode) : String :=
  let (firstKey, secondKey) := kind.keys
  let (startKey, finishKey) := match mode with
    | .literal => (s!"\"{secondKey}\"", s!"\"{firstKey}\"")
    | .field => ("KeyStart", "KeyFinish")
  s!"DateRange(Rows/Start For {startKey},Rows/Finish For {finishKey})"

private def selectedRangeRun (kind : IndexKind) (mode : KeyMode)
    (scenario : SelectionScenario) (computedKey : Bool := false) :
    Option (String × String) := do
  let model := selectionModel kind
  let (prepared, checked) ← selectionChecked kind scenario computedKey
  let secondKey := kind.keys.2
  let rangeOperation := selectedRangeOperation kind mode
  let keyOperation := match kind with
    | .string => s!"\"{secondKey}\""
    | .number => secondKey
  let authored := [("Month", "MonthFromDate(EndOfDateRange(Range))"), ("Range", rangeOperation)] ++
    if computedKey then [("KeyStart", keyOperation)] else []
  let steps ← authored.mapM fun (target, operation) =>
    (lowerComputation model .english {
      group := ["Form"], name := target ++ "Comp", targetRelPath := "../" ++ target
      commonPrecondition := none, alternatives := [{ precondition := none, operation }]
      errorCodesToSuppress := [] }).toOption.map (·.2)
  let outcomes ← (runComputations selectionWorld prepared checked steps).toOption
  let range ← (outcomes.find? (·.pointer == "Form/Range")).map (·.outcome)
  let month ← (outcomes.find? (·.pointer == "Form/Month")).map (·.outcome)
  pure (range, month)

private def selectionExpected (mode : KeyMode) : SelectionScenario → String × String
  | .ordinary | .unselectedInvalid => ("value 2024-02/2024-06", "value 6")
  | .missing | .selectedEmpty => ("cleared", "value 0")
  | .duplicate | .selectedInvalid => ("cleared", "cleared")
  | .emptyKey => match mode with
      | .literal => ("value 2024-02/2024-06", "value 6")
      | .field => ("cleared", "value 0")

-- The selected-key distinction survives the DateRange completion and dependency read (spec/08 §4.2, spec/05 §8).
example : [IndexKind.string, .number].all (fun kind =>
    [KeyMode.literal, .field].all fun mode =>
      [SelectionScenario.ordinary, .missing, .duplicate, .selectedInvalid,
        .unselectedInvalid, .selectedEmpty, .emptyKey].all fun scenario =>
          selectedRangeRun kind mode scenario == some (selectionExpected mode scenario)) := by
  native_decide

example : [IndexKind.string, .number].all (fun kind =>
    selectedRangeRun kind .field .ordinary true ==
      some ("value 2024-02/2024-06", "value 6")) := by native_decide

private inductive ComparisonShape where
  | constructedStored
  | storedConstructed
  | constructedPair

private def selectedComparison (kind : IndexKind) (mode : KeyMode) : ComparisonShape → String
  | .constructedStored => selectedRangeOperation kind mode ++ " == [Range]"
  | .storedConstructed => "[Range] == " ++ selectedRangeOperation kind mode
  | .constructedPair => selectedRangeOperation kind mode ++ " == " ++ selectedRangeOperation kind mode

private def selectionRule (kind : IndexKind) (mode : KeyMode) (shape : ComparisonShape) :=
  checkRule (selectionDm kind) .english {
    group := ["Form"], name := "SelectedComparison", errorCode := "SELECTED"
    errorEntityRelPath := "../Month", severity := "ERROR"
    condition := "FieldFilled(Month) And (" ++ selectedComparison kind mode shape ++ ")" } selectionWorld

private def selectedComparisonRun (kind : IndexKind) (mode : KeyMode)
    (shape : ComparisonShape) (scenario : SelectionScenario) :
    Option (Verdict × String × String) := do
  let model := selectionModel kind
  let (_, original) ← selectionChecked kind scenario (rangeStored := "2024-02/2024-06")
  let preliminary ← original.applyFullIndexPreliminary.toOption
  let validation := preliminary.computationInput
  let rule ← (selectionRule kind mode shape).toOption
  let context : AddressedValidationEvaluationContext model := {
    scalar := {
      fields := validation.flatContext.withWorld selectionWorld
      groups := GroupPresenceContext.unavailable }
    outer := [], input := .checked validation }
  let verdict := (← (rule.evalAddressedFull context true).toOption).verdict
  let (prepared, checked) ← selectionChecked kind scenario
  let authored := [("Next", none, "[Guard] + 1"),
      ("Guard", some (selectedComparison kind mode shape), "1")] ++
    match shape with
    | .constructedPair => []
    | .constructedStored | .storedConstructed => [("Range", none, selectedRangeOperation kind mode)]
  let steps ← authored.mapM fun (target, guard, operation) =>
    (lowerComputation model .english {
      group := ["Form"], name := target ++ "Comp", targetRelPath := "../" ++ target
      commonPrecondition := guard, alternatives := [{ precondition := none, operation }]
      errorCodesToSuppress := [] }).toOption.map (·.2)
  let outcomes ← (runComputations selectionWorld prepared checked steps).toOption
  let guard ← (outcomes.find? (·.pointer == "Form/Guard")).map (·.outcome)
  let next ← (outcomes.find? (·.pointer == "Form/Next")).map (·.outcome)
  pure (verdict, guard, next)

private def comparisonExpected (mode : KeyMode) : SelectionScenario → Verdict × String × String
  | .ordinary | .unselectedInvalid => (.fired .value, "value 1", "value 2")
  | .missing | .selectedEmpty => (.notFired, "cleared", "value 1")
  | .duplicate | .selectedInvalid => (.unknown, "cleared", "cleared")
  | .emptyKey => match mode with
      | .literal => (.fired .value, "value 1", "value 2")
      | .field => (.notFired, "cleared", "value 1")

example : [IndexKind.string, .number].all (fun kind =>
    [KeyMode.literal, .field].all fun mode =>
      [ComparisonShape.constructedStored, .storedConstructed, .constructedPair].all fun shape =>
        [SelectionScenario.ordinary, .missing, .duplicate, .selectedInvalid,
          .unselectedInvalid, .selectedEmpty, .emptyKey].all fun scenario =>
            selectedComparisonRun kind mode shape scenario == some (comparisonExpected mode scenario)) := by
  native_decide

private def selectedReferences : Option (List String × Bool × Bool × Bool × Bool) := do
  let model := selectionModel .number
  let (_, checked) ← selectionChecked .number .ordinary (rangeStored := "2024-02/2024-06")
  let rule ← (selectionRule .number .field .constructedStored).toOption
  let preliminary ← checked.applyFullIndexPreliminary.toOption
  let inputs ← preliminary.messageReferenceInputs.toOption
  let pointers ← (rule.condition.core.referencePointers [] (some inputs)).toOption
  let parsed ← (parseText .english "Rows/Start For KeyStart").toOption
  let surface ← (lowerDateRangeEndpoint model ["Form"] parsed.body).toOption
  let source ← (elaborateDateRangeEndpointSource model ["Form"] [] surface).toOption
  pure ((pointers.map (renderPointer model)).eraseDups.mergeSort (fun a b => decide (a ≤ b)),
    source.referencesField 3, source.referencesErrorField 3,
    source.referencesErrorField 4, source.referencesErrorField 1)

example : selectedReferences = some ([
    "Form/KeyFinish", "Form/KeyStart", "Form/Month", "Form/Range",
    "Form/Rows/Finish", "Form/Rows/Id", "Form/Rows[2]/Id", "Form/Rows[2]/Start"],
    true, false, true, true) := by native_decide

private def endpointAdmission (wrongKind wrongKey : Bool) :
    Option (Bool × Option KernelStaticDiagnostic) := do
  let base := selectionModel .number
  let model := if wrongKey then { base with fields := base.fields.map fun field =>
    if field.id == 1 then { field with policy := { kind := .string } } else field } else base
  let parsed ← (parseText .english
    ((if wrongKind then "Rows/Id" else "Rows/Start") ++ " For KeyStart")).toOption
  let surface ← (lowerDateRangeEndpoint model ["Form"] parsed.body).toOption
  pure (match elaborateDateRangeEndpointSource model ["Form"] [] surface with
    | .ok _ => (true, none)
    | .error error => (false, error.diagnostic?))

example : endpointAdmission false false = some (true, none) ∧
    endpointAdmission true false = some (false, some .wrongDateFormatForOp) ∧
    endpointAdmission false true = some (false, some .indexTypeInconsistent) ∧
    endpointAdmission true true = some (false, some .indexTypeInconsistent) ∧
    comparisonAdmitted (selectionModel .number)
      "DateRange(Rows/Start For \"bad\",Rows/Finish For \"1\") == [Range]" = false := by native_decide

private def virtualModel : FlatModel :=
  let base := selectionModel .number
  let fields := base.fields.map (fun field =>
      if field.id == 1 || field.id == 2 then
        { field with groupPath := ["Form", "Calls"], repeatableScope := [11] }
      else field)
  { base with fields, repeatableGroups := base.repeatableGroups ++ [
      { level := 11, path := ["Form", "Calls"], repeatability := some 2 }] }
private def virtualInput : Json := Json.mkObj [("Form", Json.mkObj [
  ("Calls", .arr #[Json.mkObj [("KeyStart", .str "2"), ("KeyFinish", .str "1")]]),
  ("Rows", .arr #[
    Json.mkObj [("Id", .str "1"), ("Start", .str "2024-01"), ("Finish", .str "2024-06")],
    Json.mkObj [("Id", .str "2"), ("Start", .str "2024-02"), ("Finish", .str "2024-03")]])])]
private def implicitSelection (phase : Phase) (row : Nat := 2) : Option DateRangeConstructionObservation := do
  let dm : DmModel := { flat := virtualModel, computations := [], rules := [], conditionLanguage := "en_US", refusals := [] }
  let raw ← (readDocument dm virtualInput).toOption
  if !raw.refusals.isEmpty then none
  let prepared ← (prepareFlatStringContext selectionWorld builtinStringPatternCompiler virtualModel).toOption
  let checked ← (checkDocument prepared "en_US" raw.data).toOption
  let endpoint (name : String) := do
    let parsed ← (parseText .english ("Rows/" ++ name ++ " For Calls/Key" ++ name)).toOption
    let surface ← (lowerDateRangeEndpoint virtualModel ["Form"] parsed.body).toOption
    (elaborateDateRangeEndpointSource virtualModel ["Form"] [11] surface).toOption
  let construction ← (checkDateRangeConstructionEndpoints (← endpoint "Start") (← endpoint "Finish")).toOption
  (construction.evaluateAt phase checked [(11, row)]).toOption

-- Full validation visits capacity rows absent from the document (spec/07 §1); their keys are clean empty.
example : implicitSelection .validation = some { start := .empty, finish := .empty } ∧
    implicitSelection .computation = some { start := .poison .malformed, finish := .poison .malformed } ∧
    (implicitSelection .validation 1).map (fun result => match result.comparisonOperand with
      | .value _ _ => true
      | _ => false) = some true := by native_decide

end A12Kernel.Dm.RangeExpressionLocks
