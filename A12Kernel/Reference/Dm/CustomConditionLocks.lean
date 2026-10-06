import A12Kernel.Reference.Dm.Validate
import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Document
import A12Kernel.Reference.Dm.Print
import A12Kernel.Reference.Dm.LowerValidation

namespace A12Kernel.Dm.CustomConditionLocks

private def model : FlatModel := {
  fields := [
    { id := 1, groupPath := ["Form"], name := "Error", policy := { kind := .string } },
    { id := 2, groupPath := ["Form"], name := "Other", policy := { kind := .number { scale := 0, signed := true } } }] }

private def admitted (text : String) (language : Language := .english) : Bool :=
  ((parseText language text).toOption.bind fun parsed =>
    (lowerCondition model ["Form"] false parsed.body).toOption).isSome

example : admitted "FieldFilled(Error) And CustomCondition Check" ∧
    admitted "CustomCondition 'True' Or FieldFilled(Error)" ∧
    admitted "CustomCondition 123 Or FieldFilled(Error)" ∧
    admitted "CustomCondition 123Check Or FieldFilled(Error)" ∧
    admitted "CustomCondition Own:Check Or FieldFilled(Error)" ∧
    admitted "FeldAngegeben(Error) Und ApplikationsBedingung Pruefung" .german := by native_decide

example : !admitted "CustomCondition True" ∧ !admitted "CustomCondition '123'" ∧
    !admitted "CustomCondition 'bad.name'" := by native_decide

private def checkedInput (dm : DmModel) (data : Lean.Json) : Option (CheckedDocument dm.flat) := do
  let input ← (readDocument dm data).toOption
  if !input.refusals.isEmpty then none
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } } builtinStringPatternCompiler dm.flat).toOption
  (checkDocument prepared "en_US" input.data).toOption

private def run (text : String) (registered : Bool := false) : Option String := do
  let dm : DmModel := { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let document ← checkedInput dm (Lean.Json.mkObj [("Form", Lean.Json.mkObj [
    ("Error", Lean.Json.str "ready")])])
  let parsed ← (parseText .english text).toOption
  let condition ← (lowerCondition model ["Form"] false parsed.body).toOption
  let context : AddressedValidationEvaluationContext model := {
    scalar := {
      fields := document.flatContext
      groups := GroupPresenceContext.unavailable
      customConditions := fun name => if registered && name == "Check" then .ok true
        else .error (.missingRegistration name) }
    outer := [], input := .checked document }
  let result := match condition.core with
    | .leaf leaf => leaf.evalAddressed context
    | _ => condition.core.evalAddressed context
  pure (match result with
    | .ok (.fired .value) => "value"
    | .ok (.fired .omission) => "omission"
    | .ok .notFired => "notFired"
    | .ok .unknown => "unknown"
    | .error (.customCondition (.missingRegistration name)) => "missing:" ++ name
    | .error _ => "other-error")

example : run "FieldFilled(Error) And CustomCondition Check" true = some "value" ∧
    run "FieldFilled(Error) Or CustomCondition Missing" = some "value" ∧
    run "FieldFilled(Other) And CustomCondition Missing" = some "notFired" := by native_decide

example : run "FieldNotFilled(Other) Or CustomCondition Missing" = some "missing:Missing" ∧
    run "CustomCondition First And CustomCondition Second" = some "missing:First" ∧
    run "CustomCondition Second Or CustomCondition First" = some "missing:Second" := by native_decide

private def fullRule (content : Bool := true)
    (conditionText : String := "FieldFilled(Error) And CustomCondition Check") : Option Verdict := do
  let dm : DmModel := { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let document ← checkedInput dm (Lean.Json.mkObj [("Form", Lean.Json.mkObj [
    ("Error", Lean.Json.str (if content then "ready" else ""))])])
  let rule ← (checkRule dm .english {
    group := ["Form"], name := "Custom", errorCode := "CUSTOM", errorEntityRelPath := "../Error",
    condition := conditionText, severity := "ERROR" }).toOption
  let context : AddressedValidationEvaluationContext model := {
    scalar := { fields := document.flatContext, groups := GroupPresenceContext.unavailable }
    outer := [], input := .checked document }
  let result ← (rule.evalAddressedFull context content (registry := {
    configured := some fun name => if name == "Check" then some fun input =>
      input.errorPointer == MessagePointer.ofCellAddr { field := 1, path := [] } &&
      input.formallyIncorrect.isEmpty && input.data.checkedCells.any (·.address.field == 1) &&
      (match input.relevance with | .all => true | .partialEntities _ => false)
    else none })).toOption
  pure result.verdict

example : fullRule = some (.fired .value) ∧
    fullRule false = some .notFired ∧
    fullRule false "CustomCondition Check Or FieldFilled(Error)" = some (.fired .value) := by native_decide

private def partialRule (scope : ValidationRelevanceScope) : Option (Option Verdict) := do
  let dm : DmModel := { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let document ← checkedInput dm (Lean.Json.mkObj [("Form", Lean.Json.mkObj [
    ("Error", Lean.Json.str "ready"), ("Other", Lean.Json.str "bad")])])
  let rule ← (checkRule dm .english {
    group := ["Form"], name := "Custom", errorCode := "CUSTOM", errorEntityRelPath := "../Error",
    condition := "FieldFilled(Error) And CustomCondition Check", severity := "ERROR" }).toOption
  let registry : CustomValidationRegistry model := {
    configured := some fun name => if name == "Check" then some fun input =>
      input.errorPointer == MessagePointer.ofCellAddr { field := 1, path := [] } &&
      input.formallyIncorrect == [{ field := 2, path := [] }] &&
      input.data.storedTextAt { field := 1, path := [] } == some "ready" &&
      (match input.relevance with | .all => false | .partialEntities actual => actual == scope)
    else none }
  match ← (rule.evalAddressedPartial document scope (registry := registry)).toOption with
  | .skipped => pure none
  | .evaluated result => pure (some result.verdict)

example : partialRule (.partialSet [{ path := ["Form", "Error"], indices := [.all, .all] }]) =
    some (some (.fired .value)) ∧ partialRule (.partialSet []) = some none := by native_decide

example : (lowerComputation model .english {
    group := ["Form"], name := "Guard", targetRelPath := "../Other", commonPrecondition := none,
    alternatives := [{ precondition := some "CustomCondition Check", operation := "1" }],
    errorCodesToSuppress := [] }).isOk = false := by native_decide

example : (checkRule { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
    .english {
      group := ["Form"], name := "Bare", errorCode := "BARE", errorEntityRelPath := "../Error",
      condition := "CustomCondition Check", severity := "ERROR" }).isOk = false := by native_decide

private def repeatedModel : FlatModel := {
  model with
  fields := model.fields ++ [{
    id := 3, groupPath := ["Form", "Rows"], name := "Error",
    policy := { kind := .string }, repeatableScope := [10] }]
  repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 3 }] }

private def repeatedRule (isPartial : Bool) : Option (List MessagePointer) := do
  let dm : DmModel := { flat := repeatedModel, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let row := fun value => Lean.Json.mkObj [("Error", Lean.Json.str value)]
  let document ← checkedInput dm (Lean.Json.mkObj [("Form", Lean.Json.mkObj [
    ("Other", Lean.Json.str "bad"), ("Rows", Lean.Json.arr #[row "a", row "b"])])])
  let rule ← (checkRule dm .english {
    group := ["Form", "Rows"], name := "Custom", errorCode := "CUSTOM", errorEntityRelPath := "../Error",
    condition := "FieldFilled(Error) And CustomCondition Check", severity := "ERROR" }).toOption
  let scope := ValidationRelevanceScope.partialSet [{
    path := ["Form", "Rows", "Error"], indices := [.all, .concrete 2, .all] }]
  let registry : CustomValidationRegistry repeatedModel := {
    configured := some fun name => if name == "Check" then some fun input =>
      input.errorPointer == MessagePointer.ofCellAddr { field := 3, path := [2] } &&
      input.data.storedTextAt { field := 3, path := [2] } == some "b" &&
      input.formallyIncorrect == [{ field := 2, path := [] }] &&
      (match input.relevance with | .all => !isPartial | .partialEntities actual => isPartial && actual == scope)
    else none }
  let unbound := rule.withCustomConditions {
    scalar := { fields := document.flatContext, groups := GroupPresenceContext.unavailable }
    outer := [], input := .checked document } .all {
      configured := some fun _ => some fun input =>
        input.errorPointer == { field := 3, coordinates := [.unknown] } }
  if (unbound.scalar.customConditions "Check").toOption != some true then none
  let outcomes ← if isPartial then do
    match ← (rule.evalOrdinaryRepeatablePartial document scope (registry := registry)).toOption with
    | .skipped => none
    | .evaluated rows => pure (rows.filterMap fun (_, result) =>
        match result with | .skipped => none | .evaluated outcome => some outcome)
  else pure ((← (rule.evalOrdinaryRepeatableFull document (registry := registry)).toOption).map (·.2))
  pure (outcomes.filterMap (fun outcome => outcome.message?.map (·.errorAddress)))

example : repeatedRule false = some [{ field := 3, coordinates := [.concrete 2] }] ∧
    repeatedRule true = some [{ field := 3, coordinates := [.concrete 2] }] := by native_decide

private def filterAdmitted (condition : String) : Bool :=
  ((parseText .english s!"FieldValuesNotUnique(Rows*/Error Having {condition})").toOption.bind fun parsed =>
    (lowerCondition repeatedModel ["Form"] false parsed.body).toOption).isSome

example : filterAdmitted "FieldFilled(Rows/Error)" ∧
    !filterAdmitted "FieldFilled(Rows/Error) And CustomCondition Check" := by native_decide

example : run "FieldFilled(Error) And CustomCondition 'Check'" true = some "value" ∧
    run "FieldFilled(Error) And CustomCondition 'True'" = some "missing:True" := by native_decide

example : run "CustomCondition Missing" = some "missing:Missing" ∧
    run "CustomCondition Check" true = some "value" := by native_decide


private def printedCustom (text : String) (language : Language := .english) : Option String := do
  let parsed ← (parseText .english text).toOption
  let rendered := printText language parsed
  let reparsed ← (parseText language rendered).toOption
  let _ ← (lowerCondition model ["Form"] false reparsed.body).toOption
  pure rendered

example : printedCustom "CustomCondition 123" = some "CustomCondition 123" ∧
    printedCustom "CustomCondition 123Check" = some "CustomCondition 123Check" ∧
    printedCustom "CustomCondition Own:Check" = some "CustomCondition Own:Check" ∧
    printedCustom "CustomCondition Wahr" .german = some "ApplikationsBedingung 'Wahr'" := by native_decide

private def generatedModel : FlatModel := {
  model with
  fields := model.fields ++ [
    { id := 3, groupPath := ["Form"], name := "Required", policy := { kind := .string },
      requiredness := some .absoluteOrNearestRepeatableAncestor },
    { id := 4, groupPath := ["Form", "Rows"], name := "Key",
      policy := { kind := .number { scale := 0, signed := true } }, repeatableScope := [10] }]
  repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 2, indexField := some 4 }] }

private def generatedFormalInputs (includeGenerated : Bool) : Option Verdict := do
  let dm : DmModel := { flat := generatedModel, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let row := Lean.Json.mkObj [("Key", Lean.Json.str "5")]
  let document ← checkedInput dm (Lean.Json.mkObj [("Form", Lean.Json.mkObj [
    ("Error", Lean.Json.str "ready"), ("Other", Lean.Json.str "bad"), ("Rows", Lean.Json.arr #[row, row])])])
  let rule ← (checkRule dm .english {
    group := ["Form"], name := "Custom", errorCode := "CUSTOM", errorEntityRelPath := "../Error",
    condition := "FieldFilled(Error) And CustomCondition Check", severity := "ERROR" }).toOption
  let scope := ValidationRelevanceScope.partialSet [
    if includeGenerated then { path := ["Form"], indices := [.all] }
    else { path := ["Form", "Error"], indices := [.all, .all] }]
  let registry : CustomValidationRegistry generatedModel := {
    configured := some fun _ => some fun input =>
      input.formallyIncorrect.contains { field := 2, path := [] } &&
      input.formallyIncorrect.contains { field := 3, path := [] } == includeGenerated &&
      input.formallyIncorrect.contains { field := 4, path := [1] } == includeGenerated &&
      input.formallyIncorrect.contains { field := 4, path := [2] } == includeGenerated &&
      input.formallyIncorrect.length == (if includeGenerated then 4 else 1) }
  match ← (rule.evalAddressedPartial document scope (registry := registry)).toOption with
  | .skipped => none
  | .evaluated result => pure result.verdict

example : generatedFormalInputs true = some (.fired .value) ∧
    generatedFormalInputs false = some (.fired .value) := by native_decide

end A12Kernel.Dm.CustomConditionLocks
