import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Document
import A12Kernel.Reference.Dm.LowerValidation
import A12Kernel.Elaboration.ScalarComputationRun
import A12Kernel.Elaboration.GeneratedComputationValidation.Assembly

namespace A12Kernel.Dm.IndexedTokenLocks

private def model (enumeration : Bool) : FlatModel :=
  let token (id : FieldId) (name : String) (path : GroupPath := ["Form"])
      (scope : List RepeatableLevel := []) : FlatFieldDecl := {
    id, name, groupPath := path, repeatableScope := scope
    policy := { kind := if enumeration then .enumeration else .string }
    stringPolicy := if enumeration then {} else { maxLength := some 1 }
    enumeration := if enumeration then some { storedTokens := ["A", "B"] } else none }
  { fields := [
      { id := 1, name := "Out", groupPath := ["Form"], policy := { kind := .number { scale := 0, signed := true } } },
      token 2 "TextOut", token 4 "Ref",
      { id := 3, name := "Key", groupPath := ["Form"], policy := { kind := .string } },
      { id := 5, name := "Code", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .string } },
      token 6 "A" ["Form", "Rows", "Body"] [10], token 7 "B" ["Form", "Rows", "Body"] [10],
      token 8 "Value" ["Form", "Rows", "Children"] [10,20],
      { id := 9, name := "Out", groupPath := ["Form", "Rows"], repeatableScope := [10],
        policy := { kind := .number { scale := 0, signed := true } } },
      token 10 "TextOut" ["Form", "Rows"] [10]]
    repeatableGroups := [
      { level := 10, path := ["Form", "Rows"], repeatability := some 3, indexField := some 5 },
      { level := 20, path := ["Form", "Rows", "Children"], repeatability := some 3 }] }

private structure Scenario where
  key : String := "R1"
  firstA : String := "A"
  secondCode : String := "R2"
  children : List String := ["A", "B"]
  tokenTarget : Bool := false
  producer : Option (String × String) := none
  secondB : String := "B"
  distinctEnumerationDomain : Bool := false
  mixedTokenKinds : Bool := false
  scalarPlan : Bool := false
  rowTarget : Bool := false
  wideTarget : Bool := false
  displaySecond : Bool := false
  validSecond : Bool := false
  fixedRows : Bool := false
  stringExpressionTarget : Bool := false
  category : Bool := false

private def input (scenario : Scenario) : Lean.Json :=
  let row (key a b : String) (children : List String) := Lean.Json.mkObj [
    ("Out", .str "99"), ("TextOut", .str "B"),
    ("Code", .str key), ("Body", Lean.Json.mkObj [("A", .str a), ("B", .str b)]),
    ("Children", .arr (children.map fun value => Lean.Json.mkObj [("Value", .str value)]).toArray)]
  Lean.Json.mkObj [("Form", Lean.Json.mkObj [
    ("Out", .str "99"), ("TextOut", .str "B"), ("Ref", .str "A"), ("Key", .str scenario.key),
    ("Rows", if scenario.fixedRows then row "R1" scenario.firstA scenario.secondB scenario.children
      else .arr #[row "R1" scenario.firstA scenario.secondB scenario.children, row scenario.secondCode (if scenario.validSecond then "A" else "bad")
        (if scenario.validSecond then "B" else "bad") (if scenario.validSecond then ["A"] else ["bad"])])])]

private def scenarioModel (enumeration : Bool) (scenario : Scenario) : FlatModel :=
  let model := model enumeration
  let model : FlatModel := { model with fields := model.fields.map fun field =>
    if scenario.stringExpressionTarget && (field.id == 2 || field.id == 10) then
      { field with policy := { kind := .string }, enumeration := none, stringPolicy := {} }
    else if scenario.category then
      { field with enumeration := field.enumeration.map fun specification =>
          { specification with categories := [{ name := "Kind", tokens := ["alpha", "beta"] }] } }
    else field }
  let model := if scenario.distinctEnumerationDomain then
    { model with fields := model.fields.map fun field =>
        if field.id == 7 then { field with enumeration := some { storedTokens := ["C", "D"] } } else field }
    else model
  let model := if scenario.mixedTokenKinds then
    { model with fields := model.fields.map fun field =>
        if field.id == 7 then { field with policy := { kind := .string }, enumeration := none } else field }
    else model
  let model := { model with fields := model.fields.map fun field =>
    if scenario.wideTarget && (field.id == 2 || field.id == 10) then
      { field with enumeration := some { storedTokens := ["A", "B", "C", "D"] } }
    else if scenario.displaySecond && field.id == 7 then
      { field with enumeration := field.enumeration.map fun specification =>
          { specification with displayFacts := [{ locale := "en", stored := "A", display := "Alpha" },
            { locale := "en", stored := "B", display := "Beta" }] } }
    else field }
  if scenario.fixedRows then
    { model with fields := model.fields.map fun field => { field with repeatableScope := field.repeatableScope.filter (· != 10) }
                 repeatableGroups := model.repeatableGroups.filter (·.level != 10) }
  else model

private def evaluate (enumeration : Bool) (expression : String) (computation : Bool)
    (guard : Option String := none) (scenario : Scenario := {}) : Option (Sum Verdict String) := do
  let model := scenarioModel enumeration scenario
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let document ← (readDocument {
    flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] } (input scenario)).toOption
  let document ← (checkDocument prepared "en_US" document.data).toOption
  if computation then
    let target := if scenario.tokenTarget then "TextOut" else "Out"
    let step ← (lowerComputation model .english {
      name := "Result", group := ["Form"], targetRelPath := "../" ++ (if scenario.rowTarget then "Rows/" else "") ++ target,
      commonPrecondition := guard, alternatives := [{ precondition := none, operation := expression }],
      errorCodesToSuppress := [] }).toOption
    let producers : List (FlatFieldDecl × LoweredComputation model) ← scenario.producer.toList.mapM fun (target, operation) =>
      (lowerComputation model .english {
        name := "Producer", group := ["Form"], targetRelPath := "../" ++ target,
        commonPrecondition := none, alternatives := [{ precondition := none, operation }], errorCodesToSuppress := [] }).toOption
    if scenario.scalarPlan then
      let .number table false := step.2 | none
      let plan ← (certifyScalarComputationPlan [.number table]).toOption
      let [.number 1 (.accepted value)] ← (plan.execute world prepared.patterns document).toOption | none
      return .inr ("value " ++ value.render)
    let results ← (runComputations world prepared document (step.2 :: producers.map (·.2))).toOption
    pure (.inr (String.intercalate "," ((results.filter (·.pointer.endsWith ("/" ++ target))).map (·.outcome))))
  else
    let parsed ← (parseText .english expression).toOption
    let condition ← (lowerCondition model ["Form"] false parsed.body).toOption
    Sum.inl <$> (condition.core.evalAddressed {
      scalar := { fields := document.flatContext, groups := GroupPresenceContext.unavailable },
      outer := [], input := .checked document }).toOption

private def operands : List String := ["Rows/Body For Key", "Rows/Children*/Value For Key",
  "Rows/Children* For Key", "Rows/Body/A For Key,Rows/Body/B For Key"]

example : [false, true].all (fun enumeration => operands.all fun operands =>
    [("NumberOfDifferentValues(" ++ operands ++ ")", "2"),
      ("NumberOfValueInFields(\"A\" In " ++ operands ++ ")", "1")].all fun (expression, expected) =>
        evaluate enumeration (expression ++ " == " ++ expected) false ==
          some (.inl (.fired (if operands.contains '*' then .omission else .value))) &&
        evaluate enumeration expression true == some (.inr ("value " ++ expected))) = true := by native_decide

example : [false, true].all (fun enumeration => operands.all fun operands =>
    evaluate enumeration ("FieldValuesNotUnique(" ++ operands ++ ")") false == some (.inl .notFired) &&
    evaluate enumeration "1" true (some ("FieldValuesNotUnique(" ++ operands ++ ")"))
      { firstA := "B", children := ["B", "B"] } == some (.inr "value 1")) =
    true := by native_decide

example : [false, true].all (fun enumeration => operands.all fun operands =>
    evaluate enumeration ("FirstFilledValue(" ++ operands ++ ") == \"A\"") false == some (.inl (.fired .value)) &&
    evaluate enumeration ("FirstFilledValue(" ++ operands ++ ")") true none { tokenTarget := true } ==
      some (.inr "value A")) = true := by native_decide

example : [false, true].all (fun enumeration => operands.all fun operands =>
    evaluate enumeration ("AtLeastOneFieldValueIncludedInValueList(" ++ operands ++ " In Ref)") false ==
      some (.inl (.fired .value)) &&
    evaluate enumeration "1" true (some ("AtLeastOneFieldValueIncludedInValueList(" ++ operands ++ " In Ref)")) ==
      some (.inr "value 1")) = true := by native_decide

example : [false, true].all (fun enumeration =>
    [("AtLeastOneFieldValueIncludedInValueList", true), ("NoFieldValueIncludedInValueList", false),
      ("NotAllFieldValuesIncludedInValueList", true)].all fun (operator, fires) =>
      let expression := operator ++ "(Rows/Body For Key In Ref)"
      evaluate enumeration expression false == some (.inl (if fires then .fired .value else .notFired)) &&
      evaluate enumeration "1" true (some expression) == some (.inr (if fires then "value 1" else "cleared"))) = true := by native_decide

example : [false, true].all (fun enumeration =>
    evaluate enumeration "AtLeastOneFieldValueIncludedInValueList(Ref In Rows/Body For Key)" false ==
      some (.inl (.fired .value)) &&
    evaluate enumeration "1" true (some "AtLeastOneFieldValueIncludedInValueList(Ref In Rows/Body For Key)") ==
      some (.inr "value 1") &&
    evaluate enumeration "AtLeastOneFieldValueIncludedInValueList(Rows/Body For Key In \"A\")" false ==
      some (.inl (.fired .value))) = true := by native_decide

example : [false, true].all (fun enumeration =>
    evaluate enumeration "NumberOfDifferentValues(Rows/Body For Key) == 0" false none { key := "missing" } ==
      some (.inl (.fired .omission)) &&
    evaluate enumeration "NumberOfDifferentValues(Rows/Body For Key)" true none { key := "missing" } == some (.inr "value 0") &&
    [({ firstA := "bad" } : Scenario), { secondCode := "R1" }].all (fun scenario =>
      evaluate enumeration "NumberOfDifferentValues(Rows/Body For Key) == 2" false none scenario == some (.inl .unknown) &&
      evaluate enumeration "NumberOfDifferentValues(Rows/Body For Key)" true none scenario == some (.inr "cleared")) &&
    evaluate enumeration "NumberOfDifferentValues(Rows/Body For Key) == 2" false none { secondCode := "" } ==
      some (.inl (.fired .value)) &&
    evaluate enumeration "NumberOfDifferentValues(Rows/Body For Key)" true none { secondCode := "" } == some (.inr "cleared")) = true := by native_decide

example : [false, true].all (fun enumeration =>
    evaluate enumeration "NumberOfDifferentValues(Rows/Body For Key)" true none
      { key := "missing", producer := some ("Key", "\"R1\"") } == some (.inr "value 2") &&
    evaluate enumeration "NumberOfDifferentValues(Rows/Body For Key)" true none
      { firstA := "bad", producer := some ("Rows/Body/A", "[Ref]") } == some (.inr "value 2") &&
    evaluate enumeration "1" true (some "AtLeastOneFieldValueIncludedInValueList(Rows/Body For Key In Ref)")
      { scalarPlan := true } == some (.inr "value 1")) = true := by native_decide

example : evaluate true "NumberOfDifferentValues(Rows/Body For Key)" true none
    { distinctEnumerationDomain := true, secondB := "C" } = some (.inr "value 2") ∧
    evaluate true "FirstFilledValue(Rows/Body For Key) == \"C\"" false none
    { distinctEnumerationDomain := true, firstA := "", secondB := "C" } = some (.inl (.fired .omission)) := by native_decide

example : evaluate false "FirstFilledValue(Rows/Children*/Value For Key)" true none
    { tokenTarget := true, children := ["A", "bad"] } = some (.inr "value A") ∧
    evaluate false "FirstFilledValue(Rows/Children*/Value For Key)" true none
    { tokenTarget := true, children := ["bad", "A"] } = some (.inr "cleared") := by native_decide

example : [false, true].all (fun enumeration =>
    ["NumberOfDifferentValues(Rows For Key)", "NumberOfDifferentValues(Rows/Body/A For Key)",
      "NumberOfDifferentValues(Rows/Body/A For Key,Rows/Body/A For Key)"].all fun expression =>
      evaluate enumeration (expression ++ " == 1") false == none && evaluate enumeration expression true == none) = true := by native_decide

private def generated (expression : String) (guard : Option String := none) (key : String := "R1") : Option Verdict := do
  let m := model false
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler m).toOption
  let data ← (readDocument {
    flat := m, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] } (input { key })).toOption
  let document ← (checkDocument prepared "en_US" data.data).toOption
  let (_, .number table false) ← (lowerComputation m .english {
    name := "Result", group := ["Form"], targetRelPath := "../Out", commonPrecondition := guard
    alternatives := [{ precondition := none, operation := expression }], errorCodesToSuppress := [] }).toOption | none
  let generated : GeneratedComputationTable (CheckedNumericComputationOperation m) (CheckedComputationCondition m) := {
    targetField := 1, name := "Result", alternatives := .singleton {
      precondition := table.first.precondition, operation := table.first.operation.operation }, messagePlan := { parts := [] } }
  let rule ← (assembleGeneratedNumericOperationTableRule m generated).toOption
  pure (← (rule.evalAddressedFull {
    scalar := { fields := document.flatContext, groups := GroupPresenceContext.unavailable }
    outer := [], input := .checked document } true).toOption).verdict

example : generated "NumberOfDifferentValues(Rows/Body For Key)" = some (.fired .value) ∧
    generated "1" (some "AtLeastOneFieldValueIncludedInValueList(Rows/Body For Key In Ref)") = some (.fired .value) ∧
    generated "1" (some "AtLeastOneFieldValueIncludedInValueList(Rows/Body For Key In Ref)") "missing" = some .notFired := by native_decide

private def ordinaryRule (selected partialRun : Bool) (scope : ValidationRelevanceScope := .full)
    (enumeration : Bool := false) (scenario : Scenario := {}) (operandOverride : Option String := none) (conditionOverride : Option String := none) :
    Option (Except OrdinaryRepeatableRuleEvaluationError (Option Verdict)) := do
  let m := scenarioModel enumeration scenario
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler m).toOption
  let data ← (readDocument {
    flat := m, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] } (input scenario)).toOption
  let document ← (checkDocument prepared "en_US" data.data).toOption
  let operands := operandOverride.getD (if selected then "Rows/Body For Key" else "Ref,TextOut")
  let parsed ← (parseText .english ("FieldFilled(Ref) And (" ++ conditionOverride.getD ("FirstFilledValue(" ++ operands ++ ") == \"A\"") ++ ")")).toOption
  let condition ← (lowerCondition m ["Form"] false parsed.body).toOption
  let rule ← (assembleResolvedValidationRule m condition 4 "SELECTED" .error { parts := [] }).toOption
  if partialRun then
    pure ((rule.evalAddressedPartial document scope).map fun
      | .skipped => none
      | .evaluated outcome => some outcome.verdict)
  else
    pure (((rule.evalAddressedFull {
      scalar := { fields := document.flatContext, groups := GroupPresenceContext.unavailable }
      outer := [], input := .checked document } true).mapError .conditionAddressing).map (some ∘ FlatRuleOutcome.verdict))

example : [(true, false), (false, true), (true, true)].all (fun (selected, partialRun) =>
    match ordinaryRule selected partialRun with
    | some (.ok (some (.fired .value))) => true
    | _ => false) = true := by native_decide

private def partialSelected (enumeration : Bool) (operand : String)
    (paths : List (List String)) (scenario : Scenario := {}) : Option Verdict := do
  let scope := ValidationRelevanceScope.partialSet ((["Ref"] :: ["Key"] :: ["Rows", "Code"] :: paths).map fun path =>
    { path := "Form" :: path, indices := ("Form" :: path).map fun _ => .all })
  (← ordinaryRule true true scope enumeration scenario (some operand)).toOption.join

example : [false, true].all (fun enumeration =>
    partialSelected enumeration "Rows/Body For Key" [["Rows", "Body", "A"]] == some (.fired .value) &&
    partialSelected enumeration "Rows/Body/A For Key,Ref" [["Rows", "Body", "A"]] == some (.fired .value) &&
    partialSelected enumeration "Rows/Children*/Value For Key" [["Rows", "Children", "Value"]] == some (.fired .value) &&
    partialSelected enumeration "Rows/Body For Key" [["Rows", "Body", "B"]] == some .unknown &&
    partialSelected enumeration "Rows/Body For Key" [["Rows", "Body", "A"]] { firstA := "" } == some .unknown &&
    partialSelected enumeration "Rows/Body For Key,Ref" [["Rows", "Body"]] { key := "missing" } == some (.fired .omission) &&
    partialSelected enumeration "Rows/Body For Key,Ref" [] { key := "missing" } == some .unknown &&
    partialSelected enumeration "Ref,Rows/Body For Key" [] { key := "missing" } == some (.fired .value)) = true := by native_decide

example : [false, true].all (fun enumeration => [("Rows/Body For Key", Polarity.value), ("Rows/Children*/Value For Key", Polarity.omission)].all fun (operand, polarity) =>
    let expression := some ("NumberOfValueInFields(\"A\" In " ++ operand ++ ") == 1")
    match ordinaryRule true true .full enumeration {} none expression,
        ordinaryRule true false .full enumeration {} none expression with
    | some (.ok (some partialResult)), some (.ok (some fullResult)) =>
        partialResult == .fired polarity && fullResult == partialResult
    | _, _ => false) = true := by native_decide

private def tokenPartialCount (enumeration : Bool) (operand : String) (expected : Nat)
    (scope : ValidationRelevanceScope) (scenario : Scenario := {}) : Option Verdict := do
  (← ordinaryRule true true scope enumeration scenario none
    (some ("NumberOfValueInFields(\"A\" In " ++ operand ++ ") == " ++ toString expected))).toOption.join

private def tokenCountCoverage (paths : List (List String)) : ValidationRelevanceScope :=
  .partialSet ((["Ref"] :: ["Key"] :: ["Rows", "Code"] :: paths).map fun path =>
    { path := "Form" :: path, indices := ("Form" :: path).map fun _ => .all })

example : [false, true].all (fun enumeration =>
    tokenPartialCount enumeration "Rows/Body For Key" 1 (tokenCountCoverage [["Rows", "Body", "A"]]) == some .unknown &&
    tokenPartialCount enumeration "Rows/Body For Key" 1 (tokenCountCoverage [["Rows", "Body"]]) == some (.fired .value) &&
    tokenPartialCount enumeration "Rows/Body/A For Key,Ref" 2 (tokenCountCoverage [["Rows", "Body", "A"]]) == some (.fired .value) &&
    tokenPartialCount enumeration "Rows/Children*/Value For Key" 0 .full { key := "missing" } == some (.fired .value) &&
    tokenPartialCount enumeration "Rows/Children*/Value For Key" 0 (tokenCountCoverage []) { key := "missing" } == some .unknown &&
    tokenPartialCount enumeration "Rows/Body For Key" 1 .full { secondB := "bad" } == some .unknown &&
    tokenPartialCount enumeration "Ref,TextOut" 1 .full == some (.fired .value)) = true := by native_decide

private def boundCount (enumeration numeric partialRun : Bool) (distinct : Bool := false) : Option (List Verdict) := do
  let m := model enumeration
  let m := if numeric then { m with fields := m.fields.map fun field =>
    if field.id == 6 || field.id == 7 then
      { field with policy := { kind := .number { scale := 0, signed := true } }, enumeration := none, stringPolicy := {} }
    else field } else m
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } } builtinStringPatternCompiler m).toOption
  let data ← (readDocument { flat := m, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
    (input { firstA := if numeric then "1" else "A", secondB := if numeric then "2" else "B" })).toOption
  let document ← (checkDocument prepared "en_US" data.data).toOption
  let literal := if numeric then "1" else "\"A\""
  let expression := if distinct then "NumberOfDifferentValues(Body/A,Body/B) == 2"
    else "NumberOfValueInFields(" ++ literal ++ " In Body/A,Body/B) == 1"
  let parsed ← (parseText .english ("FieldFilled(TextOut) And " ++ expression)).toOption
  let condition ← (lowerCondition m ["Form", "Rows"] false parsed.body).toOption
  let rule ← (assembleResolvedValidationRule m condition 10 "BOUND_COUNT" .error { parts := [] }).toOption
  if partialRun then
    match ← (rule.evalOrdinaryRepeatablePartial document .full).toOption with
    | .skipped => pure []
    | .evaluated rows => pure (rows.filterMap fun (_, result) =>
        match result with | .skipped => none | .evaluated outcome => some outcome.verdict)
  else pure ((← (rule.evalOrdinaryRepeatableFull document).toOption).map (·.2.verdict))

example : [(false, false), (true, false), (false, true)].all (fun (enumeration, numeric) =>
    boundCount enumeration numeric false == some [.fired .value, .unknown, .notFired] &&
    boundCount enumeration numeric true == some [.fired .value, .unknown]) = true := by native_decide

private def selectedSource : Option (CheckedTokenEntitySource (model false)) := do
  let parsed ← (parseText .english "FirstFilledValue(Rows/Body For Key)").toOption
  let .call _ arguments none none := parsed.body | none
  let source ← (lowerEntitySource (model false) ["Form"] arguments).toOption
  (elaborateFirstFilledTokenSource (model false) ["Form"] source).toOption

example : selectedSource.any (fun source => source.referencesField 3 && source.referencesField 5 &&
    source.referencesField 6 && source.referencesField 7 && source.bindingScopes.all List.isEmpty) = true := by native_decide

example : selectedSource.any (fun source => match source.first.referencePointers [] with
    | .error .missingIndexContext => true
    | _ => false) = true ∧
    selectedSource.any (fun source => match source.first with
      | .selected selection => match selection.sideAt .computation { read := fun _ => malformedCheckedCell } with
        | .error (.checkedDocumentRequired path) => path == ["Form", "Rows", "Body"]
        | _ => false
      | _ => false) = true := by native_decide

example : [false, true].all (fun enumeration =>
    evaluate enumeration "NumberOfDifferentValues(Rows/Body For Key)" true none { rowTarget := true } ==
      some (.inr "value 2,value 2") &&
    evaluate enumeration "1" true (some "AtLeastOneFieldValueIncludedInValueList(Rows/Body For Key In Ref)")
      { rowTarget := true } == some (.inr "value 1,value 1")) = true ∧
    evaluate false "FirstFilledValue(Rows/Body For Key)" true none { tokenTarget := true, rowTarget := true } =
      some (.inr "value A,value A") := by native_decide

example : evaluate true "NumberOfDifferentValues(Rows/Body For Key)" true none { mixedTokenKinds := true } = some (.inr "value 2") ∧
    evaluate true "FieldValuesNotUnique(Rows/Body For Key)" false none { mixedTokenKinds := true } = none ∧
    evaluate true "1" true (some "FieldValuesNotUnique(Rows/Body For Key)") { mixedTokenKinds := true } = none := by native_decide

example : [false, true].all (fun enumeration =>
    evaluate enumeration "1" true
      (some "FieldFilled(Ref) Or AtLeastOneFieldValueIncludedInValueList(Rows/Body For Key In Ref)")
      { secondCode := "" } == some (.inr "value 1") &&
    evaluate enumeration "1" true
      (some "AtLeastOneFieldValueIncludedInValueList(Rows/Body For Key In Ref) Or FieldFilled(Ref)")
      { secondCode := "" } == some (.inr "cleared")) = true := by native_decide

example : operands.all (fun operands => [false, true].all fun repeated =>
    evaluate true ("FirstFilledValue(" ++ operands ++ ")") true none
      { tokenTarget := true, rowTarget := repeated } ==
        some (.inr (if repeated then "value A,value A" else "value A"))) = true := by native_decide

example : [false, true].all (fun repeated =>
    [({ tokenTarget := true, key := "missing", producer := some ("Key", "\"R1\"") } : Scenario),
      { tokenTarget := true, firstA := "bad", producer := some ("Rows/Body/A", "[Ref]") }].all fun scenario =>
        evaluate true "FirstFilledValue(Rows/Body For Key)" true none { scenario with rowTarget := repeated } ==
          some (.inr (if repeated then "value A,value A" else "value A"))) = true := by native_decide

example : [({ key := "missing" } : Scenario), { secondCode := "R1" }, { secondCode := "" },
    { firstA := "bad" }].all (fun scenario =>
      evaluate true "FirstFilledValue(Rows/Body For Key)" true none { scenario with tokenTarget := true } ==
        some (.inr "cleared")) = true ∧
    evaluate true "FirstFilledValue(Rows/Body For Key)" true none { tokenTarget := true, firstA := "", secondB := "A" } =
      some (.inr "value A") := by native_decide

example : evaluate true "FirstFilledValue(Rows/Children*/Value For Key)" true none
    { tokenTarget := true, children := ["A", "bad"] } = some (.inr "value A") ∧
    evaluate true "FirstFilledValue(Rows/Children*/Value For Key)" true none
    { tokenTarget := true, children := ["bad", "A"] } = some (.inr "cleared") ∧
    evaluate true "FirstFilledValue(Rows/Children*/Value For Key,Ref)" true none
    { tokenTarget := true, children := [] } = some (.inr "value A") := by native_decide

example : [({ distinctEnumerationDomain := true } : Scenario), { displaySecond := true },
    { mixedTokenKinds := true }].all (fun scenario =>
      evaluate true "FirstFilledValue(Rows/Body For Key)" true none { scenario with tokenTarget := true } == none) = true ∧
    evaluate true "FirstFilledValue(Rows/Body For Key)" true none
      { tokenTarget := true, distinctEnumerationDomain := true, wideTarget := true, firstA := "", secondB := "C" } =
        some (.inr "value C") := by native_decide

private def selectedEnumerationSource : Option (CheckedEnumerationFirstFilledSource (model true) []) := do
  let parsed ← (parseText .english "FirstFilledValue(Rows/Body For Key)").toOption
  let .call _ arguments none none := parsed.body | none
  let source ← (lowerEnumerationFirstFilledSource (model true) ["Form"] arguments).toOption
  (elaborateEnumerationFirstFilledSource (model true) ["Form"] [] source ["Form"]).toOption

example : selectedEnumerationSource.any (fun source =>
    [3,5,6,7].all source.referencesField && !source.referencesField 2 &&
    match source.evaluate { instantiatedRows := [], rawCells := fun _ => none } [] { read := fun _ => .empty } (fun _ _ => malformedCheckedCell)
        (fun _ _ => .empty) with
    | .error (.unsupportedGroupOperand path) => path == ["Form", "Rows", "Body"]
    | _ => false) = true := by native_decide

example : ["FirstFilledValue(Rows/Body/A For Key)",
    "FirstFilledValue(Rows/Body/A For Key,Rows/Body/A For Key)",
    "FirstFilledValue(Rows/TextOut For Key,Ref)"].all (fun expression =>
      evaluate true expression true none { tokenTarget := true, rowTarget := true } == none) = true := by native_decide

private def selectedAssignmentWithRead (enumeration : Bool) (operand : String)
    (oldKey newKey : String) : Option StringTargetOutcome := do
  let m := model enumeration
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler m).toOption
  let data ← (readDocument { flat := m, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
    (input { key := oldKey })).toOption
  let document ← (checkDocument prepared "en_US" data.data).toOption
  let parsed ← (parseText .english ("FirstFilledValue(" ++ operand ++ ")")).toOption
  let .call _ arguments none none := parsed.body | none
  let read := fun address =>
    if address.field == 3 then pure { rawPresent := true, parsed := some (.str newKey), findings := [] }
    else document.read address
  if enumeration then
    let authored ← (lowerEnumerationFirstFilledSource m ["Form"] arguments).toOption
    let source ← (elaborateEnumerationFirstFilledSource m ["Form"] [] authored ["Form"]).toOption
    pure (← (source.evaluateCheckedDocumentWithRead document read []).toOption).asComputationResult.asExactStringTargetOutcome
  else
    let authored ← (lowerEntitySource m ["Form"] arguments).toOption
    let operation ← (checkStringFirstFilledComputation m ["Form"] 2 authored).toOption
    pure (← (operation.evaluateAt none document read []).toOption).outcome

example : [false, true].all (fun enumeration =>
    ["Rows/Body For Key", "Rows/Children*/Value For Key"].all fun operand =>
      selectedAssignmentWithRead enumeration operand "missing" "R1" == some (.accepted ⟨"A", by decide⟩) &&
      selectedAssignmentWithRead enumeration operand "R1" "missing" == some .noValue) = true := by native_decide

private def tokenListVerdict (enumeration : Bool) (expression : String)
    (scope : ValidationRelevanceScope := .full) (scenario : Scenario := {}) (partialRun : Bool := true) : Option Verdict := do
  (← ordinaryRule true partialRun scope enumeration scenario none (some expression)).toOption.join

example : [false, true].all (fun enumeration =>
    [("AtLeastOneFieldValueIncludedInValueList", Verdict.fired .value),
      ("NoFieldValueIncludedInValueList", .notFired), ("NotAllFieldValuesIncludedInValueList", .fired .value)].all
    fun (operator, expected) => [false, true].all fun partialRun =>
      tokenListVerdict enumeration (operator ++ "(Rows/Body For Key In Ref)")
        (partialRun := partialRun) == some expected) = true := by native_decide

example : [false, true].all (fun enumeration =>
    tokenListVerdict enumeration "AtLeastOneFieldValueIncludedInValueList(Rows/Body For Key In Ref)"
      (tokenCountCoverage [["Rows", "Body", "A"]]) == some (.fired .value) &&
    tokenListVerdict enumeration "NoFieldValueIncludedInValueList(Rows/Body For Key In Ref)"
      (tokenCountCoverage [["Rows", "Body", "A"]]) == some .unknown &&
    tokenListVerdict enumeration "NotAllFieldValuesIncludedInValueList(Rows/Body For Key In Ref)"
      (tokenCountCoverage [["Rows", "Body", "B"]]) == some (.fired .value)) = true := by native_decide

example : [false, true].all (fun enumeration =>
    tokenListVerdict enumeration "AtLeastOneFieldValueIncludedInValueList(Ref In Rows/Body For Key)"
      (tokenCountCoverage [["Rows", "Body", "A"]]) == some (.fired .value) &&
    tokenListVerdict enumeration "NoFieldValueIncludedInValueList(Ref In Rows/Body For Key)"
      (tokenCountCoverage [["Rows", "Body", "A"]]) == some .unknown &&
    tokenListVerdict enumeration "NotAllFieldValuesIncludedInValueList(TextOut In Rows/Body For Key)"
      (tokenCountCoverage [["TextOut"], ["Rows", "Body", "A"]]) == some .unknown &&
    tokenListVerdict enumeration "AtLeastOneFieldValueIncludedInValueList(Rows/Children*/Value For Key In \"A\")"
      .full == some (.fired .value)) = true := by native_decide

example : [false, true].all (fun enumeration =>
    tokenListVerdict enumeration "AtLeastOneFieldValueIncludedInValueList(Rows/Body For Key In TextOut)"
      .full { firstA := "bad" } == some (.fired .value) &&
    tokenListVerdict enumeration "NoFieldValueIncludedInValueList(Rows/Body For Key In TextOut)"
      .full { firstA := "bad" } == some .unknown &&
    tokenListVerdict enumeration "NotAllFieldValuesIncludedInValueList(Rows/Body For Key In Ref)"
      .full { firstA := "bad" } == some (.fired .value) &&
    tokenListVerdict enumeration "NotAllFieldValuesIncludedInValueList(Ref In Rows/Body For Key)"
      .full { firstA := "bad" } == some .unknown) = true := by native_decide

example : [false, true].all (fun enumeration =>
    tokenListVerdict enumeration "NoFieldValueIncludedInValueList(Rows/Children*/Value For Key In Ref)"
      .full { key := "missing" } == some (.fired .value) &&
    tokenListVerdict enumeration "NoFieldValueIncludedInValueList(Rows/Children*/Value For Key In Ref)"
      (tokenCountCoverage []) { key := "missing" } == some .unknown &&
    tokenListVerdict enumeration "AtLeastOneFieldValueIncludedInValueList(Rows/Body For Key In Ref)"
      .full { secondCode := "R1" } == some .notFired) = true := by native_decide

example : [false, true].all (fun enumeration =>
    tokenListVerdict enumeration "AtLeastOneFieldValueIncludedInValueList(Rows/Body/A For Key,TextOut In Ref)" == some (.fired .value) &&
    tokenListVerdict enumeration "AtLeastOneFieldValueIncludedInValueList(Rows*/Body In Ref)" == some (.fired .value) &&
    tokenListVerdict enumeration "AtLeastOneFieldValueIncludedInValueList(Rows/Children*/Value For Key In Ref)" == some (.fired .value) &&
    tokenListVerdict enumeration "AtLeastOneFieldValueIncludedInValueList(Ref In TextOut)" == some .notFired) = true := by native_decide

example : [false, true].all (fun enumeration =>
    match ordinaryRule true true .full enumeration {} none
      (some "FieldFilled(Ref) Or AtLeastOneFieldValueIncludedInValueList(Rows*/Body/A Having ([Rows/Body/A] == \"A\") In Ref)") with
    | some (.ok none) => true
    | _ => false) = true := by native_decide

example : [false, true].all (fun enumeration =>
    tokenListVerdict enumeration "FieldValuesNotUnique(Rows/Body For Key)" .full { secondB := "A" } == some (.fired .value) &&
    tokenListVerdict enumeration "FieldValuesNotUnique(Rows/Body For Key)" .full == some .notFired &&
    tokenListVerdict enumeration "FieldValuesNotUnique(Rows/Body For Key,Ref)"
      (tokenCountCoverage [["Rows", "Body", "A"]]) == some (.fired .value) &&
    tokenListVerdict enumeration "FieldValuesNotUnique(Rows/Body For Key,TextOut)"
      .full { firstA := "bad" } == some (.fired .value) &&
    tokenListVerdict enumeration "FieldValuesNotUnique(Rows/Children*/Value For Key)"
      .full { children := ["A", "A"] } == some (.fired .value) &&
    tokenListVerdict enumeration "FieldValuesNotUnique(Rows/Children*/Value For Key)"
      .full { key := "missing" } == some .notFired) = true := by native_decide

example : [false, true].all (fun enumeration =>
    tokenListVerdict enumeration "FieldValuesNotUnique(Rows/Body For Key,Ref)" .full { secondB := "bad" } == some (.fired .value) &&
    tokenListVerdict enumeration "FieldValuesNotUnique(Rows/Body For Key)" .full { secondCode := "R1", secondB := "A" } == some .notFired &&
    tokenListVerdict enumeration "FieldValuesNotUnique(Ref,TextOut)" == some .notFired &&
    tokenListVerdict enumeration "FieldValuesNotUnique(Rows*/Body)" == some .notFired &&
    tokenListVerdict enumeration "FieldValuesNotUnique(Rows*/Children*/Value)" .full { children := ["A", "A"] } == some (.fired .value)) = true := by native_decide

example : [false, true].all (fun enumeration =>
    match ordinaryRule true true .full enumeration {} none
      (some "FieldFilled(Ref) Or FieldValuesNotUnique(Rows*/Body/A Having ([Rows/Body/A] == \"A\"))") with
    | some (.ok none) => true
    | _ => false) = true := by native_decide

example : [false, true].all (fun enumeration =>
    ["Ref,TextOut", "Rows/Body For Key", "Rows/Body/A For Key,Rows/Body/B For Key",
      "Rows/Children*/Value For Key", "Rows/Children* For Key"].all fun operand =>
      let condition := "NumberOfDifferentValues(" ++ operand ++ ") == 2"
      let expected := if operand == "Rows/Children*/Value For Key" || operand == "Rows/Children* For Key"
        then Polarity.omission else .value
      tokenListVerdict enumeration condition .full {} false == some (.fired expected) &&
      tokenListVerdict enumeration condition == some (.fired expected)) = true := by native_decide

example : [false, true].all (fun enumeration =>
    tokenListVerdict enumeration "NumberOfDifferentValues(Rows/Body For Key) == 2"
      (tokenCountCoverage [["Rows", "Body", "A"]]) == some .unknown &&
    tokenListVerdict enumeration "NumberOfDifferentValues(Rows/Body For Key) == 2"
      (tokenCountCoverage [["Rows", "Body"]]) == some (.fired .value)) = true := by native_decide

example : [false, true].all (fun enumeration =>
    ["Rows*/Body", "Rows*/Children*/Value", "Rows*/Children*"].all fun operand =>
      let condition := "NumberOfDifferentValues(" ++ operand ++ ") == 2"
      tokenListVerdict enumeration condition .full { validSecond := true } == some (.fired .omission) &&
      tokenListVerdict enumeration condition .full { validSecond := true } false == some (.fired .omission)) = true := by native_decide

example : [false, true].all (fun enumeration =>
    ["Rows/Body For Key", "Rows/Children*/Value For Key", "Rows/Children* For Key",
      "Rows/Body/A For Key,Rows/Body/B For Key"].all fun operand =>
      let condition := "NumberOfDifferentValues(" ++ operand ++ ") == 0"
      let expected := if operand == "Rows/Body For Key" || operand == "Rows/Body/A For Key,Rows/Body/B For Key"
        then Polarity.omission else .value
      tokenListVerdict enumeration condition .full { key := "missing" } == some (.fired expected) &&
      tokenListVerdict enumeration condition .full { key := "missing" } false == some (.fired expected) &&
      tokenListVerdict enumeration condition (tokenCountCoverage []) { key := "missing" } == some .unknown) = true := by native_decide

example : [false, true].all (fun enumeration =>
    tokenListVerdict enumeration "NumberOfDifferentValues(Rows/Body For Key) == 2" .full { secondCode := "R1" } == some .unknown &&
    tokenListVerdict enumeration "NumberOfDifferentValues(Rows/Body For Key) == 2" .full { firstA := "bad" } == some .unknown &&
    tokenListVerdict enumeration "NumberOfDifferentValues(Rows/Children*/Value For Key) == 0" .full { children := [] } == some (.fired .omission) &&
    boundCount enumeration false true true == some [.fired .value, .unknown] &&
    boundCount enumeration false false true == some [.fired .value, .unknown, .notFired]) = true := by native_decide

example : tokenListVerdict true "NumberOfDifferentValues(Rows/Body For Key) == 2" .full
      { distinctEnumerationDomain := true, secondB := "C" } = some (.fired .value) ∧
    tokenListVerdict true "NumberOfDifferentValues(Rows/Body For Key) == 2" .full
      { mixedTokenKinds := true } = some (.fired .value) := by native_decide

example : [false, true].all (fun enumeration =>
    let fieldWildcard : RelevantEntityPattern := {
      path := ["Form", "Rows", "Children", "Value"], indices := [.all, .all, .all, .concrete 1] }
    let concreteGroup : RelevantEntityPattern := {
      path := ["Form", "Rows", "Children"], indices := [.all, .concrete 1, .concrete 1] }
    let concreteField := { fieldWildcard with indices := [.all, .concrete 1, .concrete 1, .concrete 1] }
    let base := [["Ref"], ["Key"], ["Rows", "Code"]].map fun path =>
      { path := "Form" :: path, indices := ("Form" :: path).map fun _ => RelevanceIndex.all }
    let scope := ValidationRelevanceScope.partialSet (fieldWildcard :: concreteGroup :: base)
    tokenListVerdict enumeration "NumberOfDifferentValues(Rows/Children*/Value For Key) == 2" scope == some .unknown &&
    tokenListVerdict enumeration "NumberOfDifferentValues(Rows/Children*/Value For Key) == 2"
      (.partialSet (fieldWildcard :: concreteField :: base)) == some (.fired .omission) &&
    tokenPartialCount enumeration "Rows/Children*/Value For Key" 1 scope == some (.fired .omission)) = true := by native_decide

example : (match ordinaryRule true true .full false {} none
    (some "FieldFilled(Ref) Or NumberOfDifferentValues(Rows*/Body/A Having (FieldFilled(Rows/Body/A))) == 2") with
    | some (.ok none) => true | _ => false) = true := by native_decide

private def distinctReadback (enumeration : Bool) (operands : String) (expected : Nat)
    (changes : List (FieldId × Except CheckedAddressingError (Option CheckedCell))) :
    Option (Sum Verdict (List String)) := do
  let m := model enumeration
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } } builtinStringPatternCompiler m).toOption
  let data ← (readDocument { flat := m, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
    (input {})).toOption
  let document ← (checkDocument prepared "en_US" data.data).toOption
  let parsed ← (parseText .english ("NumberOfDifferentValues(" ++ operands ++ ") == " ++ toString expected)).toOption
  let condition ← (lowerCondition m ["Form"] false parsed.body).toOption
  let .leaf leaf := condition.core | none
  let context : AddressedValidationEvaluationContext m := {
    scalar := { fields := document.flatContext, groups := GroupPresenceContext.unavailable }, outer := []
    input := .partialView document fun environment field => match changes.find? (·.1 == field) with
      | some (_, result) => result
      | none => (fun addressed => some addressed.cell) <$> document.addressedCell environment field }
  let result ← leaf.evalAddressedPartial? context .full (fun _ => true)
    (fun _ _ => .error (.checkedDocumentRequired [])) none
  pure (match result with
    | .ok verdict => .inl verdict
    | .error (.checkedDocumentRequired path) => .inr path
    | .error _ => .inr ["unexpected failure"])

example : [false, true].all (fun enumeration =>
    ["Rows/Body For Key", "Rows/Body/A For Key,Rows/Body/B For Key"].all fun operands =>
      let replacement := checkAdmittedRawCell (.parsed (if enumeration then .enum "B" else .str "B"))
      distinctReadback enumeration operands 1 [(6, .ok (some replacement))] == some (.inl (.fired .value)) &&
      distinctReadback enumeration operands 2 [(6, .ok none)] == some (.inl .unknown) &&
      distinctReadback enumeration operands 2 [(6, .error (.partialUnavailable [] 6))] == some (.inl .unknown) &&
      distinctReadback enumeration operands 2 [(6, .ok (some malformedCheckedCell)),
        (7, .error (.checkedDocumentRequired ["injected"]))] == some (.inl .unknown) &&
      distinctReadback enumeration operands 2 [(6, .error (.checkedDocumentRequired ["injected"])),
        (7, .ok (some malformedCheckedCell))] == some (.inr ["injected"]) &&
      distinctReadback enumeration operands 0 [(3, .ok (some (checkAdmittedRawCell (.parsed (.str "missing")))))] ==
        some (.inl (.fired .omission))) = true := by native_decide

example : [false, true].all (fun enumeration =>
    tokenListVerdict enumeration "NumberOfDifferentValues(Rows/Body/A,Rows/Body/B) == 2" == none) = true := by native_decide

example : [false, true].all (fun enumeration =>
    tokenListVerdict enumeration "NumberOfDifferentValues(Rows/Body) == 2" .full { fixedRows := true } ==
      some (.fired .value) &&
    tokenListVerdict enumeration "NumberOfDifferentValues(Rows/Body) == 2" .full { fixedRows := true } false ==
      some (.fired .value)) = true := by native_decide


example : [false, true].all (fun enumeration =>
    evaluate enumeration "[Rows/Body/A For Key] + \"!\" == \"A!\"" false == some (.inl (.fired .value)) &&
    evaluate enumeration "[Rows/Body/A For Key] + \"!\"" true none
      { tokenTarget := true, stringExpressionTarget := true } == some (.inr "value A!") &&
    evaluate enumeration "1" true (some "[Rows/Body/A For Key] + \"!\" == \"A!\"") == some (.inr "value 1") &&
    evaluate enumeration "[Rows/Body/A For \"R1\"] + [Rows/Body/A For \"R2\"] == \"BA\"" false none
      { firstA := "B", validSecond := true } == some (.inl (.fired .value))) = true := by native_decide

example : evaluate false "RangeAsString(Rows/Body/A For Key,1,1) + \"x\" == \"Ax\"" false == some (.inl (.fired .value)) ∧
    evaluate false "RangeAsString(Rows/Body/A For Key,1,1) + \"x\"" true none
      { tokenTarget := true, stringExpressionTarget := true, rowTarget := true } == some (.inr "value Ax,value Ax") ∧
    evaluate true "[Rows/Body/A ->Kind For Key] + \"!\" == \"alpha!\"" false none
      { category := true } == some (.inl (.fired .value)) := by native_decide


example : [false, true].all (fun enumeration =>
    [(({ key := "missing" } : Scenario), Verdict.fired .omission, "value !"),
      ({ firstA := "" }, .fired .omission, "value !"),
      ({ firstA := "bad" }, .unknown, "cleared"), ({ secondCode := "R1" }, .unknown, "cleared")].all
      fun (scenario, verdict, result) =>
        evaluate enumeration "[Rows/Body/A For Key] + \"!\" == \"!\"" false none scenario == some (.inl verdict) &&
        evaluate enumeration "[Rows/Body/A For Key] + \"!\"" true none
          { scenario with tokenTarget := true, stringExpressionTarget := true } == some (.inr result)) = true := by native_decide

example : evaluate false "RangeAsString(Rows/Body/A For Key,1,2) + \"!\" == \"!\"" false == some (.inl (.fired .value)) ∧
    evaluate false "RangeAsString(Rows/Body/A For Key,1,2) + \"!\" == \"!\"" false none
      { firstA := "" } == some (.inl (.fired .omission)) ∧
    evaluate true "[Rows/Body/B ->Kind For Key] + \"!\" == \"beta!\"" false none
      { category := true, displaySecond := true } == some (.inl (.fired .value)) := by native_decide

example : [false, true].all (fun repeated =>
    let expected value := some (.inr (if repeated then value ++ "," ++ value else value))
    evaluate false "[Rows/Body/A For Key] + \"!\"" true none
      { tokenTarget := true, stringExpressionTarget := true, rowTarget := repeated,
        key := "missing", firstA := "B", producer := some ("Key", "\"R1\"") } == expected "value B!" &&
    evaluate false "[Rows/Body/A For Key] + \"!\"" true none
      { tokenTarget := true, stringExpressionTarget := true, rowTarget := repeated,
        firstA := "bad", producer := some ("Rows/Body/A", "[Ref]") } == expected "value A!") = true := by native_decide

example : evaluate false "\"ok\"" true (some "[Rows/Body/A For Key] + \"!\" == \"A!\"")
    { tokenTarget := true, stringExpressionTarget := true } == some (.inr "value ok") ∧
    evaluate false "FieldValueAsString(Out) + [Rows/Body/A For Key]" true none
      { tokenTarget := true, stringExpressionTarget := true } == some (.inr "value 99A") := by native_decide

example : ["RangeAsString([Rows/Body/A For Key],1,1) + \"!\"", "RangeAsString(Rows/Body/A For Key,0,1)",
    "[Rows/Body/A For 1] + \"!\"", "FieldValueAsString([Rows/Out For Key]) + \"!\""].all
    (fun expression => (evaluate false expression true none
      { tokenTarget := true, stringExpressionTarget := true }).isNone) = true ∧
    (evaluate true "RangeAsString(Rows/Body/A For Key,1,1) + \"!\"" false).isNone = true ∧
    (evaluate true "[Rows/Body/B For Key] + \"!\" == \"B!\"" false none { displaySecond := true }).isNone = true ∧
    (evaluate false "[Rows/TextOut For Key] + \"!\"" true none
      { tokenTarget := true, stringExpressionTarget := true, rowTarget := true }).isNone = true := by native_decide


example : evaluate true "[Rows/Body/A ->Kind For Key] == \"alpha\"" false none
    { category := true } == some (.inl (.fired .value)) ∧
    evaluate true "1" true (some "[Rows/Body/B ->Kind For Key] == \"beta\"")
      { category := true } == some (.inr "value 1") := by native_decide

example : ["[Rows/Body/A ->Kind For Key] == \"outside\"", "\"A\" != [Rows/Body/A ->Kind For Key]"].all
    (fun condition => (evaluate true condition false none { category := true }).isNone &&
      (evaluate true "1" true (some condition) { category := true }).isNone) = true := by native_decide

example : ["[Rows/Body/A ->Kind For Key] == [Rows/Body/B For Key]",
    "[Rows/Body/B For Key] == [Rows/Body/A ->Kind For Key]"].all (fun condition =>
      evaluate true condition false none { category := true, displaySecond := true } == some (.inl .notFired) &&
      evaluate true "1" true (some condition) { category := true, displaySecond := true } == some (.inr "cleared")) = true := by native_decide

example : evaluate true "{[Rows/Body/B For Key]} + \"!\" == \"B!\"" false none
      { displaySecond := true } = some (.inl (.fired .value)) ∧
    evaluate true "\"!\" + {{[Rows/Body/B For Key]}}" true none
      { displaySecond := true, tokenTarget := true, stringExpressionTarget := true } = some (.inr "value !B") ∧
    (evaluate true "{[Rows/Body/B For Key] + \"!\"} == \"B!\"" false none
      { displaySecond := true }).isNone = true := by native_decide

private def selectedStringBindings (expression : String) : Option (List FieldId × List FieldId) := do
  let m := model false
  let parsed ← (parseText .english expression).toOption
  let surface ← (lowerSelectedStringExpr m ["Form"] parsed.body).toOption
  let checked ← (elaborateSelectedBoundStringExpression m ["Form"] ["Form"] surface).toOption
  pure (checked.declarations.map (·.id), checked.boundDeclarations.map (·.id))

example : selectedStringBindings "[Rows/Body/A For Key] + \"!\"" = some ([3, 5, 6], [3]) ∧
    selectedStringBindings "[Rows/Body/A For \"R1\"] + [Ref]" = some ([5, 6, 4], [4]) ∧
    selectedStringBindings "[Rows/Body/A] + [Ref]" = none := by native_decide

private def stringPartialAdmission (condition : String) : Option Bool := do
  let m := model false
  let parsed ← (parseText .english condition).toOption
  let checked ← (lowerCondition m ["Form"] false parsed.body).toOption
  let .leaf leaf := checked.core | none
  pure leaf.supportsAddressedPartial

example : stringPartialAdmission "[Rows/Body/A For Key] + \"!\" == \"A!\"" = some true ∧
    stringPartialAdmission "[Ref] + \"!\" == \"A!\"" = some true := by native_decide

end A12Kernel.Dm.IndexedTokenLocks
