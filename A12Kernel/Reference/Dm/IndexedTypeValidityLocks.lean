import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Document
import A12Kernel.Elaboration.GeneratedComputationValidation

namespace A12Kernel.Dm.IndexedTypeValidityLocks

private def model : FlatModel :=
  let number (id : FieldId) (name : String) : FlatFieldDecl := {
    id, name, groupPath := ["Form"], policy := { kind := .number { scale := 0, signed := true } } }
  let enumeration (id : FieldId) (name : String) (path : GroupPath) (scope : List RepeatableLevel) : FlatFieldDecl := {
    id, name, groupPath := path, repeatableScope := scope, policy := { kind := .enumeration }
    enumeration := some { storedTokens := ["x", "y"], displayFacts := [
      { locale := "en_US", stored := "x", display := "y" }, { locale := "en_US", stored := "y", display := "x" }] } }
  { fields := [number 0 "Out", number 1 "After",
      { id := 2, name := "Key", groupPath := ["Form"], policy := { kind := .string } },
      { id := 3, name := "Id", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .string } },
      { id := 4, name := "Text", groupPath := ["Form", "Rows"], repeatableScope := [10],
        policy := { kind := .string }, stringPolicy := { maxLength := some 1 } },
      enumeration 5 "Enum" ["Form", "Rows"] [10],
      { id := 6, name := "Fresh", groupPath := ["Form"], policy := { kind := .string } },
      { number 7 "RowOut" with groupPath := ["Form", "Rows"], repeatableScope := [10] },
      { id := 8, name := "Clock", groupPath := ["Form"], policy := { kind := .temporal .time .time },
        temporalTargetPolicy := some { format := "HH:mm:ss" } }, enumeration 9 "FreshEnum" ["Form"] []]
    repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 2, indexField := some 3 }]
    timeZoneId := "UTC" }

private def world (registered : Bool := false) : World := {
  now := { epochMillis := 0 }
  customFieldValidator? := fun name => if registered && name == "Code" then
    some (fun value context => if value == "x" && context == explicitCustomFieldValidationContext then none
      else some { projectCode := "TYPE_REJECTED" }) else none }

private structure Scenario where
  key : String := "B"
  firstId : String := "A"
  selected : String := "x"
  unselected : String := "y"
  omitted : Bool := false

private def input (scenario : Scenario) : Lean.Json :=
  let row (id value : String) (omitted : Bool) := Lean.Json.mkObj
    ([("Id", .str id), ("RowOut", .str "9")] ++
      if omitted then [] else [("Text", .str value), ("Enum", .str value)])
  Lean.Json.mkObj [("Form", Lean.Json.mkObj [
    ("Key", .str scenario.key), ("Fresh", .str "y"), ("FreshEnum", .str "y"), ("Out", .str "9"), ("After", .str "9"), ("Clock", .str "09:08:07"),
    ("Rows", .arr #[row scenario.firstId scenario.unselected false, row "B" scenario.selected scenario.omitted])])]

private def checked (scenario : Scenario := {}) (registered : Bool := false) : Option (CheckedDocument model) := do
  let prepared ← (prepareFlatStringContext (world registered) builtinStringPatternCompiler model).toOption
  let raw ← (readDocument { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
    (input scenario)).toOption
  (checkDocument prepared "en_US" raw.data).toOption

private def guards : List String := ["Valid", "Invalid"].flatMap fun op =>
  ["Text", "Enum"].flatMap fun field => ["Key", "\"B\""].map fun key => s!"{op}(Rows/{field} For {key},\"Code\")"

private def validate (guard : String) (scenario : Scenario := {}) (registered : Bool := false) : Option Verdict := do
  let document ← checked scenario registered
  let parsed ← (parseText .english guard).toOption
  let condition ← (lowerCondition model ["Form"] false parsed.body (world := world registered)).toOption
  (condition.core.evalAddressed {
    scalar := { fields := document.flatContext.withWorld (world registered), groups := GroupPresenceContext.unavailable }
    outer := [], input := .checked document }).toOption

example : guards.all (fun guard => validate guard == some (.fired .value)) = true := by native_decide

example : validate "Valid(Key,\"Code\")" = some (.fired .value) ∧
    validate "Invalid(Out,\"Code\")" = none := by native_decide

private def run (guard : String) (scenario : Scenario := {}) (registered : Bool := false)
    (alternative : Bool := false) (target : String := "Out") (producer : Option (String × String) := none) :
    Option (List String) := do
  let world := world registered
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let document ← checked scenario registered
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
  | known | empty | missing | duplicate | malformed | unselectedMalformed | omitted | emptyKey | emptyIndex
  deriving BEq

private def states : List State := [.known, .empty, .missing, .duplicate, .malformed, .unselectedMalformed, .omitted, .emptyKey, .emptyIndex]

private def scenarioFor : State → Scenario
  | .known => {}
  | .empty => { selected := "" }
  | .missing => { key := "Z" }
  | .duplicate => { firstId := "B" }
  | .malformed => { selected := "long" }
  | .unselectedMalformed => { unselected := "long" }
  | .omitted => { omitted := true }
  | .emptyKey => { key := "" }
  | .emptyIndex => { firstId := "" }

private def reached (state : State) := state == .known || state == .unselectedMalformed || state == .emptyIndex
private def poisoned (state : State) := reached state || state == .duplicate || state == .malformed
private def variableGuards : List String := guards.filter (fun guard => !guard.contains 'B')

example : states.all (fun state => variableGuards.all fun guard =>
    validate guard (scenarioFor state) == some (if reached state then .fired .value else .unknown) &&
    run guard (scenarioFor state) == some ["Form/After:" ++ (if poisoned state then "cleared" else "value 1"), "Form/Out:cleared"] &&
    run guard (scenarioFor state) false true == some (if poisoned state then ["Form/After:cleared", "Form/Out:cleared"]
      else if state == .emptyKey then ["Form/After:value 1", "Form/Out:cleared"] else ["Form/After:value 3", "Form/Out:value 2"])) = true := by native_decide

example : ["Text", "Enum"].all (fun field => ["x", "y"].all fun value => ["Valid", "Invalid"].all fun op =>
    let guard := s!"{op}(Rows/{field} For Key,\"Code\")"
    let holds := (op == "Valid") == (value == "x")
    validate guard { selected := value } true == some (if holds then .fired .value else .notFired) &&
    run guard { selected := value } true == some (if holds then ["Form/After:value 2", "Form/Out:value 1"] else ["Form/After:value 1", "Form/Out:cleared"]) &&
    run guard { selected := value } true true == some (if holds then ["Form/After:value 2", "Form/Out:value 1"] else ["Form/After:value 3", "Form/Out:value 2"])) = true := by native_decide

example : variableGuards.all (fun guard =>
    run guard {} true false "Clock" == some (if guard.startsWith "Valid" then ["Form/After:cleared", "Form/Clock:value 01:02:03"] else ["Form/After:value 1", "Form/Clock:cleared"]) &&
    run guard {} false false "Clock" == some ["Form/After:cleared", "Form/Clock:cleared"]) = true := by native_decide

example : ["Text", "Enum"].all (fun field =>
    run s!"Valid(Rows/{field} For Key,\"Code\")" { key := "Z" } true false "Out" (some ("Key", "\"B\"")) == some ["Form/After:value 2", "Form/Out:value 1"] &&
    run s!"Invalid(Rows/{field} For Key,\"Code\")" {} true false "Out" (some ("Rows/" ++ field, if field == "Enum" then "[FreshEnum]" else "[Fresh]")) == some ["Form/After:value 2", "Form/Out:value 1"]) = true := by native_decide

private def ruleMessages (guard : String) (scenario : Scenario := {}) (registered : Bool := false) : Option (List String) := do
  let world := world registered
  let document ← checked scenario registered
  let rule ← (checkRule { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
    .english {
      name := "Rule", group := ["Form"], errorCode := "PROBE", errorEntityRelPath := "../Key"
      condition := "FieldFilled(Key) And " ++ guard, severity := "ERROR" } world).toOption
  let messages ← (runRule world document rule).toOption
  pure (messages.map fun message => (observe model message).messageType)

example : states.all (fun state => variableGuards.all fun guard =>
    ruleMessages guard (scenarioFor state) == some (if reached state then ["VALUE_ERROR"] else [])) = true := by native_decide

example : ["Rows/RowOut For Key", "Rows For Key", "Rows*/Text", "Rows/Text For Out"].all (fun source =>
    (validate s!"Valid({source},\"Code\")").isNone && (run s!"Invalid({source},\"Code\")").isNone) &&
    (validate "Valid(Rows/Text For Key,\"\")").isNone && (run "Invalid(Rows/Text For Key,\"\")").isNone = true := by native_decide

private inductive ReadChange where
  | unchanged | unavailable | malformed | value (text : String) | structural | unavailableError

private def partialLeaf (guard : String) (scenario : Scenario := {})
    (scope : ValidationRelevanceScope := .full) (field : FieldId := 4)
    (change : ReadChange := .unchanged) (registered : Bool := false) : Option (Except CheckedAddressingError Verdict) := do
  let document ← checked scenario registered
  let parsed ← (parseText .english guard).toOption
  let condition ← (lowerCondition model ["Form"] false parsed.body (world := world registered)).toOption
  let .leaf leaf := condition.core | none
  let context : AddressedValidationEvaluationContext model := {
    scalar := { fields := document.flatContext.withWorld (world registered), groups := GroupPresenceContext.unavailable }
    outer := []
    input := .partialView document fun row current =>
      if current != field then (document.fullValidationAddressedCell row current).map (fun addressed => some addressed.cell)
      else match change with
      | .unchanged => (document.fullValidationAddressedCell row current).map (fun addressed => some addressed.cell)
      | .unavailable => pure none
      | .malformed => pure (some malformedCheckedCell)
      | .value text => pure (some (checkAdmittedRawCell (.parsed (if field == 5 then .enum text else .str text))))
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
    partialMatches (partialLeaf guard (scenarioFor state)) (.ok (if reached state then .fired .value else .unknown))) = true := by native_decide

example : ["Text", "Enum"].all (fun field =>
    let source := if field == "Enum" then 5 else 4
    let valid := s!"Valid(Rows/{field} For Key,\"Code\")"
    let invalid := s!"Invalid(Rows/{field} For Key,\"Code\")"
    partialMatches (partialLeaf valid {} .full 2 (.value "A") true) (.ok .notFired) &&
    partialMatches (partialLeaf invalid {} .full source (.value "y") true) (.ok (.fired .value)) &&
    partialMatches (partialLeaf valid {} .full source .unavailable) (.ok .unknown) &&
    partialMatches (partialLeaf valid {} .full source .malformed) (.ok .unknown) &&
    partialMatches (partialLeaf valid {} .full source .structural) (.error (.checkedDocumentRequired ["injected"])) &&
    partialMatches (partialLeaf valid {} .full 2 .structural) (.error (.checkedDocumentRequired ["injected"])) &&
    partialMatches (partialLeaf valid {} .full 2 .unavailableError) (.ok .unknown)) = true := by native_decide

example : variableGuards.all (fun guard =>
    partialMatches (partialLeaf guard { firstId := "B" } (.partialSet [keyRelevant, rowsRelevant])) (.ok .unknown) &&
    partialMatches (partialLeaf guard { firstId := "B" } (.partialSet [keyRelevant, rowRelevant 2])) (.ok (.fired .value)) &&
    partialMatches (partialLeaf guard {} (.partialSet [rowsRelevant])) (.ok .unknown) &&
    partialMatches (partialLeaf guard {} (.partialSet [keyRelevant, { path := ["Form", "Rows", "Id"], indices := [.all, .all, .all] }])) (.ok .unknown) &&
    partialMatches (partialLeaf guard { key := "Z" } (.partialSet [keyRelevant, rowRelevant 2])) (.ok .unknown) &&
    partialMatches (partialLeaf guard { key := "" } (.partialSet [keyRelevant, rowsRelevant])) (.ok .unknown)) = true := by native_decide

private def partialRule (guard : String) (scenario : Scenario) (coverage : List RelevantEntityPattern) : Option Verdict := do
  let document ← checked scenario
  let parsed ← (parseText .english ("FieldFilled(Key) And " ++ guard)).toOption
  let condition ← (lowerCondition model ["Form"] false parsed.body).toOption
  let rule ← (assembleResolvedValidationRule model condition 2 "PARTIAL_TYPE" .error { parts := [] }).toOption
  let result ← (rule.evalAddressedPartial document (.partialSet (keyRelevant :: coverage))).toOption
  match result with
  | .evaluated result => some result.verdict
  | .skipped => none

example : variableGuards.all (fun guard =>
    partialRule guard {} [rowsRelevant] == some (.fired .value) &&
    partialRule guard { firstId := "B" } [rowsRelevant] == some .unknown &&
    partialRule guard { firstId := "B" } [rowRelevant 2] == some (.fired .value) &&
    partialRule guard { key := "Z" } [rowsRelevant] == some .unknown &&
    partialRule guard { key := "" } [rowsRelevant] == some .notFired) = true := by native_decide

example : variableGuards.all (fun guard =>
    let field := if guard.contains 'E' then 5 else 4
    partialMatches (partialLeaf guard {} .full field .unavailableError)
      (.error (.partialUnavailable [(10,2)] field)) &&
    partialRule guard {} [{ path := ["Form", "Rows", "Id"], indices := [.all, .all, .all] }] == some .unknown) = true := by native_decide

private def generated (guardText : String) (registered : Bool) : Option (Bool × Bool) := do
  let parsed ← (parseText .english guardText).toOption
  let targetGroup := ["Form"]
  let target := 0
  let surface ← (lowerGuard model ["Form"] false parsed.body (some targetGroup)).toOption
  let guard ← (model.elaborateCheckedComputationCondition ["Form"] targetGroup surface).toOption
  let operation ← (elaborateCompleteNumericComputationOperation model ["Form"] target
    (.literal { value := 1, authoredScale := 0 }) false).toOption
  let table : GeneratedComputationTable (CheckedNumericComputationOperation model) (CheckedComputationCondition model) := {
    targetField := target, name := "Computed", commonPrecondition := some guard
    alternatives := .singleton { operation }, messagePlan := { parts := [.text "type result"] } }
  let requiresWorld := match assembleGeneratedNumericOperationTableRule model table with
    | .error .typeValidityRequiresWorld => true
    | _ => false
  let world := world registered
  let document ← checked {} registered
  let holds := guardText.startsWith "Valid"
  let agrees := fun actual => match actual with
    | .error (.operation .guardValueFailure) => !registered
    | .ok value => registered && value ==
        (if holds then .supported (.accepted { unscaled := 1, scale := 0 }) else .supported .noValue)
    | _ => false
  let context := { (document.indexedComputationContextAt []) with world := some world }
  let routed := agrees (table.evaluateNumericTarget context)
  let documentRouted := agrees ((table.executeNumericTargetResult world document).map (·.targetCheck))
  let rule ← (assembleGeneratedNumericOperationTableRule model table (some world)).toOption
  let outcome ← (rule.evalAddressedFull {
    scalar := { fields := document.flatContext.withWorld world, groups := GroupPresenceContext.unavailable }
    outer := [], input := .checked document } true).toOption
  pure (requiresWorld && routed && documentRouted, match outcome with | .fired _ => true | _ => false)

example : variableGuards.all (fun guard =>
    generated guard false == some (true, true) &&
    generated guard true == some (true, guard.startsWith "Valid")) = true := by native_decide

private def selectedGuard (guardText : String) : Option (CheckedComputationPredicate model) := do
  let parsed ← (parseText .english guardText).toOption
  let surface ← (lowerGuard model ["Form"] false parsed.body (some ["Form"])).toOption
  let .predicate surface := surface | none
  (model.elaborateComputationPredicate ["Form"] ["Form"] surface).toOption

private def currentStored (fieldName : String) (isEnum : Bool) : Option Bool := do
  let document ← checked {} true
  let predicate ← selectedGuard s!"Invalid(Rows/{fieldName} For Key,\"Code\")"
  let field := if isEnum then 5 else 4
  let context := document.indexedScalarComputationContext (world true)
  let some addressed := context.addressed | none
  let current := { addressed with
    read := fun row current => if row == [(10,2)] && current == field then
      checkAdmittedRawCell (.parsed (if isEnum then .enum "y" else .str "y")) else addressed.read row current
    storedText := fun row current => if row == [(10,2)] && current == field then some "y" else addressed.storedText row current }
  let currentHolds := match predicate.evalChecked { context with addressed := some current } with
    | .ok .holds => true
    | _ => false
  let missingAddressed := match predicate.evalChecked { context with addressed := none } with
    | .error .contextRequired => true
    | _ => false
  pure (predicate.referencesField 2 && predicate.referencesField 3 && predicate.referencesField field &&
    predicate.rowBoundBool [] && currentHolds && missingAddressed)

example : currentStored "Text" false = some true ∧ currentStored "Enum" true = some true := by native_decide

private def metadata (guardText : String) : Option Bool := do
  let parsed ← (parseText .english guardText).toOption
  let condition ← (lowerCondition model ["Form"] false parsed.body).toOption
  let document ← checked {}
  let rootOnly := match condition.core.ordinaryIterationScope with | .ok none => true | _ => false
  let pointerRefusal := match condition.core.referencePointers [] with | .error .unclassifiedOperand => true | _ => false
  let missingDocument := match condition.core.evalAddressed {
      scalar := { fields := document.flatContext, groups := GroupPresenceContext.unavailable }
      outer := [], input := .legacy document.source.toDocument (fun _ _ => malformedCheckedCell) } with
    | .error (.checkedDocumentRequired ["Form", "Rows"]) => true
    | _ => false
  pure (condition.core.requiresAddressedValidation && rootOnly && pointerRefusal && missingDocument &&
    condition.core.referencesField 2 && condition.core.referencesField 3 &&
    condition.core.referencesField (if guardText.contains 'E' then 5 else 4))

example : variableGuards.all (fun guard => metadata guard == some true) = true := by native_decide

private def partialObservation (scenario : Scenario) (scope : ValidationRelevanceScope) : Option (Option CellObservation) := do
  let document ← checked scenario
  let predicate ← selectedGuard "Valid(Rows/Text For Key,\"Code\")"
  let .indexedTypeValidity _ source _ := predicate | none
  (source.selection.observePartialDocument document scope [] fun row field =>
    (document.fullValidationAddressedCell row field).map (fun addressed => some addressed.cell)).toOption

example : ["", "Z"].all (fun key =>
    partialObservation { key } (.partialSet [keyRelevant, rowsRelevant]) == some (some .empty) &&
    partialObservation { key } (.partialSet [keyRelevant, rowRelevant 2]) == some none) = true := by native_decide

private def repeatedTarget (guardText : String) (registered : Bool) : Option (List String) := do
  let document ← checked {} registered
  let prepared ← (prepareFlatStringContext (world registered) builtinStringPatternCompiler model).toOption
  let lowered ← (lowerComputation model .english {
    name := "Repeated", group := ["Form"], targetRelPath := "../Rows/RowOut", commonPrecondition := some guardText
    alternatives := [{ precondition := none, operation := "1" }], errorCodesToSuppress := [] }).toOption
  pure ((← (runComputations (world registered) prepared document [lowered.2]).toOption).map (·.outcome))

example : variableGuards.all (fun guard =>
    repeatedTarget guard false == some ["cleared", "cleared"] &&
    repeatedTarget guard true == some (if guard.startsWith "Valid" then ["value 1", "value 1"] else ["cleared", "cleared"])) = true := by native_decide

private def literalGuardChecks (guardText : String) : Option Bool := do
  let predicate ← selectedGuard guardText
  let parsed ← (parseText .english guardText).toOption
  let condition ← (lowerCondition model ["Form"] false parsed.body (world := world true)).toOption
  let field := if guardText.contains 'E' then 5 else 4
  let scenario : Scenario := { key := "Z", selected := if guardText.startsWith "Valid" then "x" else "y" }
  pure (!predicate.referencesField 2 && predicate.referencesField 3 && predicate.referencesField field &&
    !condition.core.referencesField 2 && condition.core.referencesField 3 && condition.core.referencesField field &&
    run guardText scenario true == some ["Form/After:value 2", "Form/Out:value 1"] &&
    partialMatches (partialLeaf guardText scenario (.partialSet [rowsRelevant]) 2 .structural true) (.ok (.fired .value)) &&
    partialMatches (partialLeaf guardText scenario (.partialSet [rowsRelevant]) 2 .unavailableError true) (.ok (.fired .value)))

example : (guards.filter (fun guard => guard.contains 'B')).all (fun guard => literalGuardChecks guard == some true) = true := by native_decide

end A12Kernel.Dm.IndexedTypeValidityLocks
