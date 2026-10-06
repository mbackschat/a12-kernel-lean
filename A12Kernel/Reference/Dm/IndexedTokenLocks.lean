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

private def input (scenario : Scenario) : Lean.Json :=
  let row (key a b : String) (children : List String) := Lean.Json.mkObj [
    ("Out", .str "99"), ("TextOut", .str "B"),
    ("Code", .str key), ("Body", Lean.Json.mkObj [("A", .str a), ("B", .str b)]),
    ("Children", .arr (children.map fun value => Lean.Json.mkObj [("Value", .str value)]).toArray)]
  Lean.Json.mkObj [("Form", Lean.Json.mkObj [
    ("Out", .str "99"), ("TextOut", .str "B"), ("Ref", .str "A"), ("Key", .str scenario.key),
    ("Rows", .arr #[row "R1" scenario.firstA scenario.secondB scenario.children, row scenario.secondCode "bad" "bad" ["bad"]])])]

private def evaluate (enumeration : Bool) (expression : String) (computation : Bool)
    (guard : Option String := none) (scenario : Scenario := {}) : Option (Sum Verdict String) := do
  let model := model enumeration
  let model := if scenario.distinctEnumerationDomain then
    { model with fields := model.fields.map fun field =>
        if field.id == 7 then { field with enumeration := some { storedTokens := ["C", "D"] } } else field }
    else model
  let model := if scenario.mixedTokenKinds then
    { model with fields := model.fields.map fun field =>
        if field.id == 7 then { field with policy := { kind := .string }, enumeration := none } else field }
    else model
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
      (if enumeration then none else some (.inr "value A"))) = true := by native_decide

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

private def ordinaryRule (selected partialRun : Bool) :
    Option (Except OrdinaryRepeatableRuleEvaluationError (Option Verdict)) := do
  let m := model false
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler m).toOption
  let data ← (readDocument {
    flat := m, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] } (input {})).toOption
  let document ← (checkDocument prepared "en_US" data.data).toOption
  let operands := if selected then "Rows/Body For Key" else "Ref,TextOut"
  let parsed ← (parseText .english ("FieldFilled(Ref) And FirstFilledValue(" ++ operands ++ ") == \"A\"")).toOption
  let condition ← (lowerCondition m ["Form"] false parsed.body).toOption
  let rule ← (assembleResolvedValidationRule m condition 4 "SELECTED" .error { parts := [] }).toOption
  if partialRun then
    pure ((rule.evalAddressedPartial document .full).map fun
      | .skipped => none
      | .evaluated outcome => some outcome.verdict)
  else
    pure (((rule.evalAddressedFull {
      scalar := { fields := document.flatContext, groups := GroupPresenceContext.unavailable }
      outer := [], input := .checked document } true).mapError .conditionAddressing).map (some ∘ FlatRuleOutcome.verdict))

example : [(true, false), (false, true)].all (fun (selected, partialRun) =>
    match ordinaryRule selected partialRun with
    | some (.ok (some (.fired .value))) => true
    | _ => false) = true ∧
    (match ordinaryRule true true with
    | some (.error (.conditionAddressing (.addressing (.unsupportedGroupOperand path)))) => path == ["Form", "Rows", "Body"]
    | _ => false) = true := by native_decide

private def selectedSource : Option (CheckedTokenEntitySource (model false)) := do
  let parsed ← (parseText .english "FirstFilledValue(Rows/Body For Key)").toOption
  let .call _ arguments none none := parsed.body | none
  let source ← (lowerEntitySource (model false) ["Form"] arguments).toOption
  (elaborateFirstFilledTokenSource (model false) ["Form"] source).toOption

example : selectedSource.any (fun source => source.referencesField 3 && source.referencesField 5 &&
    source.referencesField 6 && source.referencesField 7 && source.bindingScopes.isEmpty) = true := by native_decide

example : selectedSource.any (fun source => match source.first.referencePointers [] with
    | .error .unclassifiedOperand => true
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

end A12Kernel.Dm.IndexedTokenLocks
