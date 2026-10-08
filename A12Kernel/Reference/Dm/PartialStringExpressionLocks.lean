import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Document

namespace A12Kernel.Dm.PartialStringExpressionLocks

private def model : FlatModel := {
  fields := [
    { id := 1, name := "Key", groupPath := ["Form"], policy := { kind := .string } },
    { id := 2, name := "S", groupPath := ["Form"], policy := { kind := .string } },
    { id := 3, name := "Code", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .string } },
    { id := 4, name := "Amount", groupPath := ["Form", "Rows"], repeatableScope := [10],
      policy := { kind := .number { scale := 2, signed := true } },
      numericTargetConstraints := { minFractionalDigits := 2, leadingZerosAllowed := true } },
    { id := 5, name := "S", groupPath := ["Form", "Rows"], repeatableScope := [10],
      policy := { kind := .string }, stringPolicy := { maxLength := some 2 } },
    { id := 6, name := "E", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .enumeration },
      enumeration := some { storedTokens := ["a", "b"], categories := [{ name := "Kind", tokens := ["group", "other"] }] } },
    { id := 7, name := "Ref", groupPath := ["Form"], policy := { kind := .number { scale := 0, signed := true } } },
    { id := 8, name := "Ref", groupPath := ["Form", "Rows"], repeatableScope := [10],
      policy := { kind := .number { scale := 0, signed := true } } }]
  repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 3, indexField := some 3 }] }

private def world : World := { now := { epochMillis := 0 } }

private structure Scenario where
  key : String := "R1"
  firstCode : String := "R1"
  firstText : String := "ab"
  secondText : String := "cd"
  firstEnum : String := "a"
  secondEnum : String := "b"
  amount : Lean.Json := .str "01.50"
  omitted : Bool := false

private def input (scenario : Scenario) : Lean.Json :=
  let row (code text token : String) (amount : Lean.Json) (omitted : Bool) := Lean.Json.mkObj
    ([("Code", .str code), ("E", .str token), ("Amount", amount), ("Ref", .str "1")] ++
      if omitted then [] else [("S", .str text)])
  Lean.Json.mkObj [("Form", Lean.Json.mkObj [("Key", .str scenario.key), ("S", .str "!"), ("Ref", .str "1"),
    ("Rows", .arr #[row scenario.firstCode scenario.firstText scenario.firstEnum scenario.amount scenario.omitted,
      row "R2" scenario.secondText scenario.secondEnum (.str "02.50") false])])]

private def checked (scenario : Scenario := {}) : Option (CheckedDocument model) := do
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let raw ← (readDocument { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
    (input scenario)).toOption
  (checkDocument prepared "en_US" raw.data).toOption

private inductive ReadChange where
  | unavailable | malformed | value (payload : Value) | structural | unavailableError

private structure Override where
  field : FieldId
  row : Option Env := none
  change : ReadChange

private def readChanged (document : CheckedDocument model) (overrides : List Override) :
    Env → FieldId → Except CheckedAddressingError (Option CheckedCell) := fun row field =>
  match overrides.find? (fun entry => entry.field == field && entry.row.all (· == row)) with
  | none => (document.fullValidationAddressedCell row field).map (fun addressed => some addressed.cell)
  | some entry => match entry.change with
      | .unavailable => pure none
      | .malformed => pure (some malformedCheckedCell)
      | .value payload => pure (some (checkAdmittedRawCell (.parsed payload)))
      | .structural => .error (.checkedDocumentRequired ["injected"])
      | .unavailableError => .error (.partialUnavailable row field)

private def evaluate (text : String) (isPartial : Bool) (scenario : Scenario := {})
    (scope : ValidationRelevanceScope := .full) (overrides : List Override := [])
    (directRelevant : Bool := true) :
    Option (Except CheckedAddressingError Verdict) := do
  let document ← checked scenario
  let parsed ← (parseText .english text).toOption
  let condition ← (lowerCondition model ["Form"] false parsed.body).toOption
  let context : AddressedValidationEvaluationContext model := {
    scalar := { fields := document.flatContext, groups := GroupPresenceContext.unavailable }, outer := [],
    input := if isPartial then .partialView document (readChanged document overrides) else .checked document }
  if isPartial then
    let .leaf leaf := condition.core | none
    leaf.evalAddressedPartial? context scope (fun field => directRelevant && scope.coversField model field [])
      (fun _ _ => .error (.checkedDocumentRequired [])) none
  else some (condition.core.evalAddressed context)

private def verdict (text : String) (isPartial : Bool) (scenario : Scenario := {})
    (scope : ValidationRelevanceScope := .full) : Option Verdict :=
  (evaluate text isPartial scenario scope).bind Except.toOption

private def resultMatches (actual : Option (Except CheckedAddressingError Verdict))
    (expected : Except CheckedAddressingError Verdict) : Bool :=
  match actual, expected with
  | some (.ok actual), .ok expected => actual == expected
  | some (.error actual), .error expected => decide (actual = expected)
  | _, _ => false

private def rootField (name : String) : RelevantEntityPattern := { path := ["Form", name], indices := [.all, .all] }
private def rowField (name : String) (row : Option Nat := none) : RelevantEntityPattern := {
  path := ["Form", "Rows", name], indices := [.all, row.map RelevanceIndex.concrete |>.getD .all, .all] }
private def allRows : RelevantEntityPattern := { path := ["Form", "Rows"], indices := [.all, .all] }
private def coverage (entities : List RelevantEntityPattern) : ValidationRelevanceScope :=
  .partialSet (rootField "Ref" :: rowField "Ref" :: entities)
private def selectedCoverage (row : Nat := 1) : ValidationRelevanceScope := coverage
  ([rootField "Key", rootField "S", rowField "Code"] ++ ["S", "E", "Amount"].map (fun field => rowField field (some row)))

private def equalities : List (String × String) := [
  ("[Rows/S For Key] + [S]", "ab!"), ("[Rows/E For Key] + [S]", "a!"),
  ("[Rows/E ->Kind For Key] + [S]", "group!"), ("RangeAsString(Rows/S For Key,1,1) + [S]", "a!"),
  ("FieldValueAsString(Rows/Amount For Key) + [S]", "01.50!"),
  ("[Rows/S For Key] + [Rows/E For Key] + FieldValueAsString(Rows/Amount For Key)", "aba01.50"),
  ("[Rows/S For \"R1\"] + [Rows/S For \"R2\"]", "abcd"),
  ("[Rows/E ->Kind For \"R1\"] + [Rows/E ->Kind For \"R2\"]", "groupother"),
  ("FieldValueAsString(Rows/Amount For \"R1\") + FieldValueAsString(Rows/Amount For \"R2\")", "01.5002.50")]

example : equalities.all (fun (expression, expected) => ["==", "!="].all fun operator =>
    let text := expression ++ " " ++ operator ++ " \"" ++ expected ++ "\""
    verdict text false == some (if operator == "==" then .fired .value else .notFired) &&
    verdict text true == verdict text false) = true := by native_decide

example : (equalities.take 6).all (fun (expression, expected) =>
    let text := expression ++ " == \"" ++ expected ++ "\""
    verdict text true {} (selectedCoverage) == some (.fired .value) &&
    verdict text true {} (selectedCoverage 2) == some .unknown &&
    verdict (text.replace " For Key" " For \"R1\"") true {} (coverage [rootField "S", allRows]) == some (.fired .value)) = true := by native_decide

private def absenceCases : List (Scenario × Verdict) := [
  ({}, .notFired), ({ firstText := "" }, .fired .omission), ({ omitted := true }, .fired .omission),
  ({ key := "missing" }, .fired .omission), ({ key := "" }, .fired .omission),
  ({ firstText := "long" }, .unknown), ({ firstCode := "R2", key := "R2" }, .unknown),
  ({ secondText := "long" }, .notFired)]

example : absenceCases.all (fun (scenario, expected) =>
    let text := "[Rows/S For Key] + \"!\" == \"!\""
    verdict text false scenario == some expected && verdict text true scenario == some expected) = true := by native_decide

example : (["[Rows/E For Key]", "[Rows/E ->Kind For Key]", "FieldValueAsString(Rows/Amount For Key)"].all (fun source =>
    let text := source ++ " + \"!\" == \"!\""
    verdict text true { key := "missing" } == verdict text false { key := "missing" } &&
    verdict text true { key := "missing" } == some (.fired .omission)) &&
    verdict "[Rows/E For Key] + \"!\" == \"a!\"" true { firstEnum := "outside" } == some .unknown &&
    verdict "FieldValueAsString(Rows/Amount For Key) + \"!\" == \"01.50!\"" true { amount := .str "bad" } == some .unknown) = true := by native_decide

example : verdict "[Rows/S For Key] + \"!\" == \"cd!\"" true { key := "R2", firstCode := "R2" }
      (coverage [rootField "Key", rowField "Code" (some 2), rowField "S" (some 2)]) == some (.fired .value) ∧
    verdict "[Rows/S For Key] + \"!\" == \"!\"" true { key := "missing" }
      (coverage [rootField "Key", rowField "Code", rowField "S"]) == some (.fired .omission) ∧
    verdict "[Rows/S For Key] + \"!\" == \"!\"" true { key := "missing" }
      (coverage [rootField "Key", rowField "Code" (some 1), rowField "Code" (some 2),
        rowField "S" (some 1), rowField "S" (some 2)]) == some .unknown := by native_decide

example : [1,5].all (fun field => [ReadChange.unavailable, .malformed].all fun change =>
    resultMatches (evaluate "[Rows/S For Key] + \"!\" == \"ab!\"" true {} .full [{ field, change }]) (.ok .unknown)) = true := by native_decide

example : resultMatches (evaluate "[Rows/S For Key] + \"!\" == \"cd!\"" true {} .full
      [{ field := 1, change := .value (.str "R2") }]) (.ok (.fired .value)) ∧
    resultMatches (evaluate "[Rows/S For Key] + \"!\" == \"xy!\"" true {} .full
      [{ field := 5, change := .value (.str "xy") }]) (.ok (.fired .value)) ∧
    resultMatches (evaluate "[Rows/E For Key] + \"!\" == \"b!\"" true {} .full
      [{ field := 6, change := .value (.enum "b") }]) (.ok (.fired .value)) ∧
    resultMatches (evaluate "[Rows/E ->Kind For Key] + \"!\" == \"other!\"" true {} .full
      [{ field := 6, change := .value (.enum "b") }]) (.ok (.fired .value)) := by native_decide

example : [1,5].all (fun field =>
    resultMatches (evaluate "[Rows/S For Key] + \"!\" == \"ab!\"" true {} .full
      [{ field, change := .structural }]) (.error (.checkedDocumentRequired ["injected"]))) &&
    resultMatches (evaluate "[Rows/S For Key] + \"!\" == \"ab!\"" true {} .full
      [{ field := 1, change := .unavailableError }]) (.ok .unknown) &&
    resultMatches (evaluate "[Rows/S For Key] + \"!\" == \"ab!\"" true {} .full
      [{ field := 5, change := .unavailableError }]) (.error (.partialUnavailable [(10,1)] 5)) = true := by native_decide

example : resultMatches (evaluate "[Rows/S For \"R1\"] + \"!\" == \"ab!\"" true {} .full
      [{ field := 1, change := .structural }, { field := 3, change := .structural }]) (.ok (.fired .value)) ∧
    resultMatches (evaluate "[Rows/S For Key] + \"!\" == \"ab!\"" true {} .full
      [{ field := 5, row := some [(10,2)], change := .structural }]) (.ok (.fired .value)) := by native_decide

private def numericInput : Lean.Json := (Lean.Json.parse "1.5").toOption.getD .null

example : [(Lean.Json.str "01.50", "01.50"), (.str "1.5", "1.50"), (numericInput, "1.50")].all
    (fun (amount, expected) =>
      let text := "FieldValueAsString(Rows/Amount For Key) + \"!\" == \"" ++ expected ++ "!\""
      verdict text true { amount } == some (.fired .value) && verdict text true { amount } == verdict text false { amount }) = true := by native_decide

example : resultMatches (evaluate "FieldValueAsString(Rows/Amount For Key) + \"!\" == \"7!\"" true {} .full
      [{ field := 4, change := .value (.num 7) }]) (.error (.stringExpression .indexedReadUnavailable)) := by native_decide

example : resultMatches (evaluate "[S] + \"!\" == \"!!\"" true {} .full [] false) (.ok .unknown) ∧
    resultMatches (evaluate "[S] + [Rows/S For \"R1\"] == \"!ab\"" true {} .full [] false) (.ok .unknown) := by native_decide

-- Default ingestion rejects supplementary Unicode. These admitted callback cells isolate the
-- shared fold's eager fault order without asserting kernel correspondence for the injected state.
example : resultMatches (evaluate "[S] + \"!\" == RangeAsString(Rows/S For \"R2\",1,1) + \"!\"" true {} .full
      [{ field := 2, change := .unavailable }, { field := 5, row := some [(10,2)], change := .value (.str "😀") }])
      (.error (.stringExpression (.unalignedUtf16Range 5 1 1))) ∧
    resultMatches (evaluate "[Rows/S For \"R1\"] + \"!\" == RangeAsString(S,1,1) + \"!\"" true {} .full
      [{ field := 5, row := some [(10,1)], change := .unavailable }, { field := 2, change := .value (.str "😀") }])
      (.error (.stringExpression (.unalignedUtf16Range 2 1 1))) := by native_decide

example : resultMatches (evaluate "[S] + RangeAsString(Rows/S For \"R2\",1,1) == \"x\"" true {} .full
      [{ field := 2, change := .unavailable }, { field := 5, row := some [(10,2)], change := .value (.str "😀") }])
      (.error (.stringExpression (.unalignedUtf16Range 5 1 1))) := by native_decide

private def ruleFor (text : String) (repeated : Bool) : Option (CheckedResolvedValidationRule model) :=
  (checkRule { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
    .english {
      name := "String", group := ["Form"], errorCode := "PROBE", errorEntityRelPath := if repeated then "../Rows/Ref" else "../Ref"
      condition := (if repeated then "FieldFilled(Rows/Ref)" else "FieldFilled(Ref)") ++ " And (" ++ text ++ ")"
      severity := "ERROR" } world).toOption

private def partialRules (text : String) (repeated : Bool) (scenario : Scenario := {})
    (scope : ValidationRelevanceScope := .full) : Option (List (Option Verdict)) := do
  let document ← checked scenario
  let rule ← ruleFor text repeated
  if repeated then
    match ← (rule.evalOrdinaryRepeatablePartial document scope (some world)).toOption with
    | .skipped => none
    | .evaluated rows => pure (rows.map fun (_, outcome) => match outcome with
        | .skipped => none
        | .evaluated result => some result.verdict)
  else
    match ← (rule.evalAddressedPartial document scope (some world)).toOption with
    | .skipped => none
    | .evaluated result => some [some result.verdict]

private def fullRules (text : String) (repeated : Bool) (scenario : Scenario := {}) : Option (List String) := do
  let document ← checked scenario
  let rule ← ruleFor text repeated
  let messages ← (runRule world document rule).toOption
  pure (messages.map fun message => (observe model message).messageType)

example : [false,true].all (fun repeated => (equalities.take 6).all fun (expression, expected) =>
    let text := expression ++ " == \"" ++ expected ++ "\""
    partialRules text repeated == some (List.replicate (if repeated then 2 else 1) (some (.fired .value))) &&
    fullRules text repeated == some (List.replicate (if repeated then 2 else 1) "VALUE_ERROR") &&
    partialRules text repeated {} (coverage [rootField "Key", rootField "S", rowField "Code"]) ==
      some (List.replicate (if repeated then 2 else 1) (some .unknown))) = true := by native_decide

example : [false,true].all (fun repeated =>
    partialRules "[Rows/S For Key] + \"!\" == \"!\"" repeated { key := "missing" } ==
      some (List.replicate (if repeated then 2 else 1) (some (.fired .omission))) &&
    fullRules "[Rows/S For Key] + \"!\" == \"!\"" repeated { key := "missing" } ==
      some (List.replicate (if repeated then 2 else 1) "OMISSION_ERROR")) = true := by native_decide

private def globalTarget (key : String) : Option Verdict := do
  let model : FlatModel := { model with fields := model.fields.map fun field =>
    { field with isGlobal := field.id == 2 || field.id == 5 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let raw ← (readDocument { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
    (input {})).toOption
  let document ← (checkDocument prepared "en_US" raw.data).toOption
  let text := "[Rows/S For \"" ++ key ++ "\"] + [S] == \"" ++ (if key == "R1" then "ab!" else "!") ++ "\""
  let parsed ← (parseText .english text).toOption
  let condition ← (lowerCondition model ["Form"] false parsed.body).toOption
  let .leaf (.stringExpression comparison) := condition.core | none
  (comparison.evalPartial document (.partialSet [rowField "Code"]) []
    (fun row field => (document.fullValidationAddressedCell row field).map (fun cell => some cell.cell))).toOption

example : globalTarget "R1" = some (.fired .value) ∧
    globalTarget "missing" = some (.fired .omission) := by native_decide

end A12Kernel.Dm.PartialStringExpressionLocks
