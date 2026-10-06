import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Document
import A12Kernel.Elaboration.GeneratedComputationValidation

namespace A12Kernel.Dm.IndexedPatternLocks

private def model : FlatModel :=
  let number (id : FieldId) (name : String) : FlatFieldDecl := {
    id, name, groupPath := ["Form"], policy := { kind := .number { scale := 0, signed := true } } }
  let enumeration (id : FieldId) (name : String) (path : GroupPath) (scope : List RepeatableLevel) : FlatFieldDecl := {
    id, name, groupPath := path, repeatableScope := scope, policy := { kind := .enumeration }
    enumeration := some { storedTokens := ["123", "x12"], categories := [{ name := "Kind", tokens := ["digits", "mixed"] }], displayFacts := [
      { locale := "en_US", stored := "123", display := "digits" }, { locale := "en_US", stored := "x12", display := "mixed" }] } }
  { fields := [number 0 "Out", number 1 "After",
      { id := 2, name := "Key", groupPath := ["Form"], policy := { kind := .string } },
      { id := 3, name := "Id", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .string } },
      { id := 4, name := "Text", groupPath := ["Form", "Rows"], repeatableScope := [10],
        policy := { kind := .string }, stringPolicy := { maxLength := some 3 } },
      enumeration 5 "Enum" ["Form", "Rows"] [10],
      { id := 6, name := "Fresh", groupPath := ["Form"], policy := { kind := .string } },
      { number 7 "RowOut" with groupPath := ["Form", "Rows"], repeatableScope := [10] },
      { id := 8, name := "Clock", groupPath := ["Form"], policy := { kind := .temporal .time .time },
        temporalTargetPolicy := some { format := "HH:mm:ss" } },
      { id := 9, name := "Raw", groupPath := ["Form", "Rows"], repeatableScope := [10],
        policy := { kind := .string }, stringValueMode := .raw, stringPolicy := { lineBreaksPermitted := true } }]
    repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 2, indexField := some 3 }]
    timeZoneId := "UTC" }

private def world : World := { now := { epochMillis := 0 } }

private structure Scenario where
  key : String := "B"
  firstId : String := "A"
  selected : String := "123"
  unselected : String := "x12"
  omitted : Bool := false

private def input (scenario : Scenario) : Lean.Json :=
  let row (id value : String) (omitted : Bool) := Lean.Json.mkObj
    ([("Id", .str id), ("RowOut", .str "9")] ++
      if omitted then [] else [("Text", .str value), ("Enum", .str value)])
  Lean.Json.mkObj [("Form", Lean.Json.mkObj [
    ("Key", .str scenario.key), ("Fresh", .str "y"), ("Out", .str "9"), ("After", .str "9"), ("Clock", .str "09:08:07"),
    ("Rows", .arr #[row scenario.firstId scenario.unselected false, row "B" scenario.selected scenario.omitted])])]

private def checked (scenario : Scenario := {}) : Option (CheckedDocument model) := do
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let raw ← (readDocument { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
    (input scenario)).toOption
  (checkDocument prepared "en_US" raw.data).toOption

private def guards : List String := ["PatternMatched", "PatternViolated"].flatMap fun op =>
  ["Key", "\"B\""].map fun key => s!"[Rows/Text For {key}] {op} \"[0-9]+\""

private def validate (guard : String) (scenario : Scenario := {}) : Option Verdict := do
  let document ← checked scenario
  let parsed ← (parseText .english guard).toOption
  let condition ← (lowerCondition model ["Form"] false parsed.body (world := world)).toOption
  (condition.core.evalAddressed {
    scalar := { fields := document.flatContext.withWorld world, groups := GroupPresenceContext.unavailable }
    outer := [], input := .checked document }).toOption

example : guards.all (fun guard =>
    validate guard == some (if guard.contains 'M' then .fired .value else .notFired)) = true := by native_decide

example : validate "[Fresh] PatternViolated \"[0-9]+\"" = some (.fired .value) ∧
    validate "[Out] PatternMatched \"[0-9]+\"" = none := by native_decide

private def run (guard : String) (scenario : Scenario := {})
    (alternative : Bool := false) (target : String := "Out") (producer : Option (String × String) := none) :
    Option (List String) := do
  let world := world
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let document ← checked scenario
  let definitions : List DmComputation := [
    { name := "Dependent", group := ["Form"], targetRelPath := "../After",
      commonPrecondition := if target == "Clock" then some "FieldNotFilled(Clock)" else none,
      alternatives := [{ precondition := none, operation := if target == "Clock" then "1" else "[Out]+1" }], errorCodesToSuppress := [] },
    { name := "Consumer", group := ["Form"], targetRelPath := "../" ++ target,
      commonPrecondition := if alternative then none else some guard,
      alternatives := [{
        precondition := if alternative then some guard else none
        operation := if target == "Clock" then "Time(\"1\",\"2\",\"3\")" else "1" }] ++
        if alternative then [{ precondition := some "FieldFilled(Key)", operation := "2" }] else [], errorCodesToSuppress := [] }] ++
      producer.toList.map (fun (field, operation) => {
        name := "Producer", group := ["Form"], targetRelPath := "../" ++ field, commonPrecondition := none,
        alternatives := [{ precondition := none, operation }], errorCodesToSuppress := [] })
  let lowered ← definitions.mapM fun definition => (lowerComputation model .english definition).toOption
  let results ← (runComputations world prepared document (lowered.map (·.2))).toOption
  pure ((results.filter (fun result => result.pointer == "Form/After" || result.pointer == "Form/" ++ target)).map
    (fun result => result.pointer ++ ":" ++ result.outcome)).mergeSort

private inductive State where
  | matched | violated | empty | missing | duplicate | malformed | unselectedMalformed | omitted | emptyKey | emptyIndex
  deriving BEq

private def states : List State := [.matched, .violated, .empty, .missing, .duplicate, .malformed,
  .unselectedMalformed, .omitted, .emptyKey, .emptyIndex]
private def scenarioFor : State → Scenario
  | .matched => {}
  | .violated => { selected := "x12" }
  | .empty => { selected := "" }
  | .missing => { key := "Z" }
  | .duplicate => { firstId := "B" }
  | .malformed => { selected := "long" }
  | .unselectedMalformed => { unselected := "long" }
  | .omitted => { omitted := true }
  | .emptyKey => { key := "" }
  | .emptyIndex => { firstId := "" }

private def variableGuards := guards.filter (fun guard => !guard.contains 'B')
private def isMatched (guard : String) := guard.contains 'M'
private def unavailable (state : State) := state == .duplicate || state == .malformed
private def holds (guard : String) (state : State) :=
  if state == .matched || state == .unselectedMalformed || state == .emptyIndex then isMatched guard
  else if state == .violated then !isMatched guard else false
private def validationVerdict (guard : String) (state : State) : Verdict :=
  if unavailable state then .unknown else if holds guard state then .fired .value else .notFired
private def computeResults (guard : String) (state : State) (alternative : Bool) : List String :=
  if unavailable state || state == .emptyIndex then ["Form/After:cleared", "Form/Out:cleared"]
  else if holds guard state then ["Form/After:value 2", "Form/Out:value 1"]
  else if alternative && state != .emptyKey then ["Form/After:value 3", "Form/Out:value 2"]
  else ["Form/After:value 1", "Form/Out:cleared"]

example : states.all (fun state => variableGuards.all fun guard =>
    validate guard (scenarioFor state) == some (validationVerdict guard state) &&
    run guard (scenarioFor state) == some (computeResults guard state false) &&
    run guard (scenarioFor state) true == some (computeResults guard state true)) = true := by native_decide

private def ruleMessages (guard : String) (scenario : Scenario := {}) : Option (List String) := do
  let document ← checked scenario
  let rule ← (checkRule { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
    .english {
      name := "Rule", group := ["Form"], errorCode := "PROBE", errorEntityRelPath := "../Key"
      condition := "FieldFilled(Key) And " ++ guard, severity := "ERROR" } world).toOption
  let messages ← (runRule world document rule).toOption
  pure (messages.map fun message => (observe model message).messageType)

example : states.all (fun state => variableGuards.all fun guard =>
    ruleMessages guard (scenarioFor state) == some (if holds guard state then ["VALUE_ERROR"] else [])) = true := by native_decide

example : ["PatternMatched", "PatternViolated"].all (fun op =>
    ["[Rows/Enum For Key]", "[Rows/Enum For Key->Kind]", "[Rows/Raw For Key]",
      "[Rows/RowOut For Key]", "[Rows For Key]", "[Rows*/Text For Key]", "Rows/Text For Key",
      "{[Rows/Text For Key]}", "[Rows/Text For Key]+\"x\"", "[Rows/Text For Out]"].all (fun left =>
      (validate s!"{left} {op} \"[0-9]+\"").isNone && (run s!"{left} {op} \"[0-9]+\"").isNone) &&
    (validate s!"[Rows/Text For Key] {op} [Key]").isNone && (run s!"[Rows/Text For Key] {op} [Key]").isNone &&
    validate ("[Rows/Text For Key] " ++ op ++ " {{\"[0-9]+\"}}") == some (validationVerdict s!"{op}" .matched)) = true := by native_decide

private inductive ReadChange where
  | unchanged | unavailable | malformed | value (text : String) | structural | unavailableError

private def partialLeaf (guard : String) (scenario : Scenario := {})
    (scope : ValidationRelevanceScope := .full) (field : FieldId := 4)
    (change : ReadChange := .unchanged) : Option (Except CheckedAddressingError Verdict) := do
  let document ← checked scenario
  let parsed ← (parseText .english guard).toOption
  let condition ← (lowerCondition model ["Form"] false parsed.body (world := world)).toOption
  let .leaf leaf := condition.core | none
  let context : AddressedValidationEvaluationContext model := {
    scalar := { fields := document.flatContext.withWorld world, groups := GroupPresenceContext.unavailable }
    outer := []
    input := .partialView document fun row current =>
      if current != field then (document.fullValidationAddressedCell row current).map (fun addressed => some addressed.cell)
      else match change with
      | .unchanged => (document.fullValidationAddressedCell row current).map (fun addressed => some addressed.cell)
      | .unavailable => pure none
      | .malformed => pure (some malformedCheckedCell)
      | .value text => pure (some (checkAdmittedRawCell (.parsed (.str text))))
      | .structural => .error (.checkedDocumentRequired ["injected"])
      | .unavailableError => .error (.partialUnavailable row current) }
  leaf.evalAddressedPartial? context scope (fun _ => true)
    (fun _ _ => .error (.checkedDocumentRequired [])) none

private def keyRelevant : RelevantEntityPattern := { path := ["Form", "Key"], indices := [.all, .all] }
private def rowsRelevant : RelevantEntityPattern := { path := ["Form", "Rows"], indices := [.all, .all] }
private def rowRelevant (row : Nat) : RelevantEntityPattern := { path := ["Form", "Rows"], indices := [.all, .concrete row] }

private def partialMatches (actual : Option (Except CheckedAddressingError Verdict))
    (expected : Except CheckedAddressingError Verdict) : Bool :=
  match actual, expected with
  | some (.ok actual), .ok expected => actual == expected
  | some (.error actual), .error expected => decide (actual = expected)
  | _, _ => false

example : states.all (fun state => variableGuards.all fun guard =>
    partialMatches (partialLeaf guard (scenarioFor state)) (.ok (validationVerdict guard state))) = true := by native_decide

example : variableGuards.all (fun guard =>
    partialMatches (partialLeaf guard {} .full 2 (.value "A")) (.ok (validationVerdict guard .violated)) &&
    partialMatches (partialLeaf guard {} .full 4 (.value "x12")) (.ok (validationVerdict guard .violated)) &&
    partialMatches (partialLeaf guard {} .full 4 .unavailable) (.ok .unknown) &&
    partialMatches (partialLeaf guard {} .full 4 .malformed) (.ok .unknown) &&
    partialMatches (partialLeaf guard {} .full 4 .structural) (.error (.checkedDocumentRequired ["injected"])) &&
    partialMatches (partialLeaf guard {} .full 2 .structural) (.error (.checkedDocumentRequired ["injected"])) &&
    partialMatches (partialLeaf guard {} .full 4 .unavailableError) (.error (.partialUnavailable [(10,2)] 4)) &&
    partialMatches (partialLeaf guard {} .full 2 .unavailableError) (.ok .unknown) &&
    partialMatches (partialLeaf guard { firstId := "B" } (.partialSet [keyRelevant, rowsRelevant])) (.ok .unknown) &&
    partialMatches (partialLeaf guard { firstId := "B" } (.partialSet [keyRelevant, rowRelevant 2])) (.ok (validationVerdict guard .matched)) &&
    partialMatches (partialLeaf guard {} (.partialSet [rowsRelevant])) (.ok .unknown) &&
    partialMatches (partialLeaf guard {} (.partialSet [keyRelevant, { path := ["Form", "Rows", "Id"], indices := [.all, .all, .all] }])) (.ok .unknown)) = true := by native_decide

private def partialRule (guard : String) (scenario : Scenario) (coverage : List RelevantEntityPattern) : Option Verdict := do
  let document ← checked scenario
  let parsed ← (parseText .english ("FieldFilled(Key) And " ++ guard)).toOption
  let condition ← (lowerCondition model ["Form"] false parsed.body).toOption
  let rule ← (assembleResolvedValidationRule model condition 2 "PARTIAL_PATTERN" .error { parts := [] }).toOption
  let result ← (rule.evalAddressedPartial document (.partialSet (keyRelevant :: coverage))).toOption
  match result with
  | .evaluated result => some result.verdict
  | .skipped => none

example : variableGuards.all (fun guard =>
    partialRule guard {} [rowsRelevant] == some (validationVerdict guard .matched) &&
    partialRule guard { firstId := "B" } [rowsRelevant] == some .unknown &&
    partialRule guard { firstId := "B" } [rowRelevant 2] == some (validationVerdict guard .matched) &&
    partialRule guard { key := "Z" } [rowsRelevant] == some .notFired &&
    partialRule guard { key := "Z" } [rowRelevant 2] == some .unknown &&
    partialRule guard { key := "" } [rowsRelevant] == some .notFired &&
    partialRule guard {} [{ path := ["Form", "Rows", "Id"], indices := [.all, .all, .all] }] == some .unknown) = true := by native_decide

private def selectedGuard (guardText : String) : Option (CheckedComputationPredicate model) := do
  let parsed ← (parseText .english guardText).toOption
  let surface ← (lowerGuard model ["Form"] false parsed.body (some ["Form"])).toOption
  let .predicate surface := surface | none
  (model.elaborateComputationPredicate ["Form"] ["Form"] surface).toOption

private def currentRead : Option Bool := do
  let document ← checked {}
  let predicate ← selectedGuard "[Rows/Text For Key] PatternViolated \"[0-9]+\""
  let context := document.indexedScalarComputationContext world
  let some addressed := context.addressed | none
  let current := { addressed with read := fun row field =>
    if row == [(10,2)] && field == 4 then checkAdmittedRawCell (.parsed (.str "x12")) else addressed.read row field }
  let currentHolds := match predicate.evalChecked { context with addressed := some current } with
    | .ok .holds => true | _ => false
  let missingAddressed := match predicate.evalChecked { context with addressed := none } with
    | .error .contextRequired => true | _ => false
  pure (predicate.referencesField 2 && predicate.referencesField 3 && predicate.referencesField 4 &&
    predicate.rowBoundBool [] && currentHolds && missingAddressed)

example : currentRead = some true := by native_decide

private def metadata (guardText : String) : Option Bool := do
  let parsed ← (parseText .english guardText).toOption
  let condition ← (lowerCondition model ["Form"] false parsed.body).toOption
  let document ← checked {}
  let rootOnly := match condition.core.ordinaryIterationScope with | .ok none => true | _ => false
  let pointerRefusal := match condition.core.referencePointers [] with | .error .unclassifiedOperand => true | _ => false
  let missingDocument := match condition.core.evalAddressed {
      scalar := { fields := document.flatContext, groups := GroupPresenceContext.unavailable }
      outer := [], input := .legacy document.source.toDocument (fun _ _ => malformedCheckedCell) } with
    | .error (.checkedDocumentRequired ["Form", "Rows"]) => true | _ => false
  pure (condition.core.requiresAddressedValidation && rootOnly && pointerRefusal && missingDocument &&
    condition.core.referencesField 2 && condition.core.referencesField 3 && condition.core.referencesField 4)

example : variableGuards.all (fun guard => metadata guard == some true) = true := by native_decide

example : variableGuards.all (fun guard =>
    run guard {} false "Clock" == some (if isMatched guard then ["Form/After:cleared", "Form/Clock:value 01:02:03"]
      else ["Form/After:value 1", "Form/Clock:cleared"]) &&
    run guard { key := "Z" } false "Out" (some ("Key", "\"B\"")) == some (computeResults guard .matched false) &&
    run guard {} false "Out" (some ("Rows/Text", if isMatched guard then "\"x12\"" else "\"123\"")) ==
      some ["Form/After:value 1", "Form/Out:cleared"]) = true := by native_decide

private def repeatedTarget (guardText : String) : Option (List String) := do
  let document ← checked {}
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let lowered ← (lowerComputation model .english {
    name := "Repeated", group := ["Form"], targetRelPath := "../Rows/RowOut", commonPrecondition := some guardText
    alternatives := [{ precondition := none, operation := "1" }], errorCodesToSuppress := [] }).toOption
  pure ((← (runComputations world prepared document [lowered.2]).toOption).map (·.outcome))

example : variableGuards.all (fun guard => repeatedTarget guard == some
    (if isMatched guard then ["value 1", "value 1"] else ["cleared", "cleared"])) = true := by native_decide

private def literalChecks (guardText : String) : Option Bool := do
  let predicate ← selectedGuard guardText
  let parsed ← (parseText .english guardText).toOption
  let condition ← (lowerCondition model ["Form"] false parsed.body).toOption
  let scenario : Scenario := { key := "Z", selected := if isMatched guardText then "123" else "x12" }
  let document ← checked scenario
  let context := document.indexedScalarComputationContext world
  let ignoresKeyFailure := match predicate.evalChecked { context with
      read := fun field => if field == 2 then malformedCheckedCell else context.read field
      storedText := fun field => if field == 2 then none else context.storedText field } with
    | .ok .holds => true | _ => false
  pure (ignoresKeyFailure && !predicate.referencesField 2 && predicate.referencesField 3 && predicate.referencesField 4 &&
    !condition.core.referencesField 2 && condition.core.referencesField 3 && condition.core.referencesField 4 &&
    run guardText scenario == some ["Form/After:value 2", "Form/Out:value 1"] &&
    partialMatches (partialLeaf guardText scenario (.partialSet [rowsRelevant]) 2 .structural) (.ok (.fired .value)) &&
    partialMatches (partialLeaf guardText scenario (.partialSet [rowsRelevant]) 2 .unavailableError) (.ok (.fired .value)))

example : (guards.filter (fun guard => guard.contains 'B')).all (fun guard => literalChecks guard == some true) = true := by native_decide

private def generated (guardText : String) (custom : Bool) (state : State := .matched) : Option (Bool × Verdict) := do
  let parsed ← (parseText .english guardText).toOption
  let .predicate surface ← (lowerGuard model ["Form"] false parsed.body (some ["Form"])).toOption | none
  let compiler : StringPatternCompiler := if custom then
    (fun source => if source == "[0-9]+" then some (fun text => text == "x12") else none) else builtinStringPatternCompiler
  let predicate ← (model.elaborateComputationPredicate ["Form"] ["Form"] surface compiler).toOption
  let guard : CheckedComputationCondition model := .leaf (.predicate predicate)
  let operation ← (elaborateCompleteNumericComputationOperation model ["Form"] 0
    (.literal { value := 1, authoredScale := 0 }) false).toOption
  let table : GeneratedComputationTable (CheckedNumericComputationOperation model) (CheckedComputationCondition model) := {
    targetField := 0, name := "Computed", commonPrecondition := some guard
    alternatives := .singleton { operation }, messagePlan := { parts := [] } }
  let document ← checked (scenarioFor state)
  let holds := isMatched guardText != custom
  let exact := match table.executeNumericTargetResult world document with
    | .ok run => if unavailable state || state == .emptyIndex then
        match run.targetCheck with | .supported (.inheritedPoison _) => true | _ => false
      else run.targetCheck == .supported (if holds then .accepted { unscaled := 1, scale := 0 } else .noValue)
    | _ => false
  let rule ← (assembleGeneratedNumericOperationTableRule model table).toOption
  let outcome ← (rule.evalAddressedFull {
    scalar := { fields := document.flatContext.withWorld world, groups := GroupPresenceContext.unavailable }
    outer := [], input := .checked document } true).toOption
  pure (exact, match outcome with | .fired _ => .fired .value | .notFired => .notFired | .unknown => .unknown)

example : guards.all (fun guard => [false, true].all fun custom =>
    generated guard custom == some (true, if isMatched guard != custom then .fired .value else .notFired)) = true := by native_decide

example : variableGuards.all (fun guard =>
    generated guard false .emptyIndex == some (true, validationVerdict guard .emptyIndex) &&
    generated guard false .duplicate == some (true, .unknown) &&
    (parseText .english ("[Rows/Enum For Key->Kind] " ++ (if isMatched guard then "PatternMatched" else "PatternViolated") ++
      " \"[0-9]+\"")).isOk) = true := by native_decide

end A12Kernel.Dm.IndexedPatternLocks
