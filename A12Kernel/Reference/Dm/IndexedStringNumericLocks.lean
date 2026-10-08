import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Document
import A12Kernel.Reference.Dm.LowerValidation

namespace A12Kernel.Dm.IndexedStringNumericLocks

private def model : FlatModel := {
  fields := [
    { id := 1, name := "Key", groupPath := ["Form"], policy := { kind := .string } },
    { id := 2, name := "Out", groupPath := ["Form"], policy := { kind := .number { scale := 2, signed := true } } },
    { id := 3, name := "Code", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .string } },
    { id := 4, name := "Text", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .string },
      stringPatternSource := some asciiDigitsPatternSource, stringPolicy := { maxLength := some 15 } },
    { id := 5, name := "Enum", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .enumeration },
      enumeration := some { storedTokens := ["1.5", "2.5"], categories := [{ name := "Numeric", tokens := ["-3.25", "4.75"] }] } },
    { id := 6, name := "Out", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .number { scale := 2, signed := true } } },
    { id := 7, name := "Key", groupPath := ["Form", "Requests"], repeatableScope := [20], policy := { kind := .string } },
    { id := 8, name := "Out", groupPath := ["Form", "Requests"], repeatableScope := [20], policy := { kind := .number { scale := 0, signed := true } } }]
  repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 3, indexField := some 3 },
    { level := 20, path := ["Form", "Requests"], repeatability := some 2 }] }

private structure Scenario where
  key : String := "R1"
  text : String := "12"
  secondCode : String := "R2"
  repeated : Bool := false
  boundKey : Bool := false
  targetScale : Nat := 0
  producer : Option (String × String) := none

private def input (scenario : Scenario) : Lean.Json :=
  let row (code text enumeration : String) := Lean.Json.mkObj [
    ("Code", .str code), ("Text", .str text), ("Enum", .str enumeration), ("Out", .str "99")]
  Lean.Json.mkObj [("Form", Lean.Json.mkObj [("Key", .str scenario.key), ("Out", .str "99"),
    ("Rows", .arr #[row "R1" scenario.text "1.5", row scenario.secondCode "34" "2.5"]),
    ("Requests", .arr #[Lean.Json.mkObj [("Key", .str "R2"), ("Out", .str "99")],
      Lean.Json.mkObj [("Key", .str "R1"), ("Out", .str "99")]])])]

private def evaluate (expression : String) (computation : Bool)
    (scenario : Scenario := {}) (guard : Option String := none) : Option (Sum Verdict (List String)) := do
  let model := { model with fields := model.fields.map fun field =>
    if field.id == 2 || field.id == 6 then
      { field with policy := { kind := .number { scale := scenario.targetScale, signed := true } } } else field }
  let group := if scenario.boundKey then ["Form", "Requests"] else ["Form"]
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let data ← (readDocument {
    flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] } (input scenario)).toOption
  let document ← (checkDocument prepared "en_US" data.data).toOption
  if computation then
    let step ← (lowerComputation model .english {
      name := "Result", group, targetRelPath := (if scenario.repeated then "../Rows/Out" else "../Out"),
      commonPrecondition := guard, alternatives := [{ precondition := none, operation := expression }], errorCodesToSuppress := [] }).toOption
    let producers ← scenario.producer.toList.mapM fun (target, operation) =>
      (lowerComputation model .english {
        name := "Producer", group := ["Form"], targetRelPath := "../" ++ target,
        commonPrecondition := none, alternatives := [{ precondition := none, operation }], errorCodesToSuppress := [] }).toOption
    let results ← (runComputations world prepared document (step.2 :: producers.map (·.2))).toOption
    pure (.inr ((results.filter (·.pointer.endsWith "/Out")).map (·.outcome)))
  else
    let parsed ← (parseText .english expression).toOption
    let condition ← (lowerCondition model group false parsed.body).toOption
    Sum.inl <$> (condition.core.evalAddressed {
      scalar := { fields := document.flatContext, groups := GroupPresenceContext.unavailable },
      outer := (if scenario.boundKey then [(20, 1)] else []), input := .checked document }).toOption

example : [("Length(Rows/Text For Key)", "2", 0), ("RangeAsNumber(Rows/Text For Key,2,2)", "2", 0),
    ("FieldValueAsNumber(Rows/Text For Key)", "12", 0), ("FieldValueAsNumber(Rows/Enum For Key)", "1.5", 1),
    ("FieldValueAsNumber(Rows/Enum ->Numeric For Key)", "-3.25", 2)].all (fun (expression, expected, scale) =>
      evaluate (expression ++ " == " ++ expected) false == some (.inl (.fired .value)) &&
      evaluate expression true { targetScale := scale } == some (.inr ["value " ++ expected]) &&
      evaluate "1" true {} (some (expression ++ " == " ++ expected)) == some (.inr ["value 1"])) = true := by native_decide

example : evaluate "FieldValueAsNumber(Rows/Text For \"R1\") + FieldValueAsNumber(Rows/Text For \"R2\")" true =
    some (.inr ["value 46"]) := by native_decide

example : ["Length(Rows/Text For Key)", "RangeAsNumber(Rows/Text For Key,2,2)", "FieldValueAsNumber(Rows/Text For Key)"].all
    (fun expression =>
      [({ key := "missing" } : Scenario), { text := "" }].all (fun scenario =>
        evaluate (expression ++ " == 0") false scenario == some (.inl (.fired .omission)) &&
        evaluate expression true scenario == some (.inr ["value 0"])) &&
      [({ text := "bad" } : Scenario), { secondCode := "R1" }].all (fun scenario =>
        evaluate (expression ++ " == 0") false scenario == some (.inl .unknown) &&
        evaluate expression true scenario == some (.inr ["cleared"]))) = true := by native_decide

example : evaluate "RangeAsNumber(Rows/Text For Key,1,3) == 0" false = some (.inl (.fired .value)) ∧
    evaluate "FieldValueAsNumber(Rows/Text For Key) == 0" false { text := "00" } = some (.inl (.fired .value)) := by native_decide

example : [("Length(Rows/Text For Key)", "3"), ("RangeAsNumber(Rows/Text For Key,2,2)", "8"),
    ("FieldValueAsNumber(Rows/Text For Key)", "789")].all (fun (expression, expected) =>
      [false, true].all fun repeated =>
        evaluate expression true { repeated, text := "bad", producer := some ("Rows/Text", "\"789\"") } ==
          some (.inr (List.replicate (if repeated then 2 else 1) ("value " ++ expected)))) = true := by native_decide

example : evaluate "FieldValueAsNumber(Rows/Text For Key)" true
    { key := "missing", producer := some ("Key", "\"R2\"") } = some (.inr ["value 34"]) := by native_decide

example : ["Length([Rows/Text For Key])", "RangeAsNumber([Rows/Text For Key],1,1)",
    "FieldValueAsNumber([Rows/Text For Key])", "RangeAsNumber(Rows/Text For Key,0,1)",
    "Length(Rows/Enum For Key)", "RangeAsNumber(Rows/Enum For Key,1,1)",
    "FieldValueAsNumber(Rows/Enum ->Missing For Key)", "Length(Rows/Text For 1)"].all
    (fun expression => (evaluate (expression ++ " == 0") false).isNone && (evaluate expression true).isNone) = true ∧
    (evaluate "FieldValueAsNumber(Rows/Enum For Key)" true).isNone = true := by native_decide

example : evaluate "FieldValueAsNumber(../Rows/Text For ../Key) == 12" false { boundKey := true } =
    some (.inl (.fired .value)) ∧
    evaluate "RangeAsNumber(../Rows/Text For ../Key,2,2) == 2" false { boundKey := true } =
      some (.inl (.fired .value)) ∧
    evaluate "FieldValueAsNumber(../Rows/Text For ../Key)" true { boundKey := true } =
      some (.inr ["value 12", "value 12"]) ∧
    evaluate "FieldValueAsNumber(../Rows/Text For Key) == 34" false { boundKey := true } =
      some (.inl (.fired .value)) ∧
    evaluate "FieldValueAsNumber(../Rows/Text For Key)" true { boundKey := true } =
      some (.inr ["value 34", "value 12"]) := by native_decide

private def partialVerdict (condition : String) (scope : ValidationRelevanceScope := .full)
    (scenario : Scenario := {}) (changes : List (FieldId × Option CheckedCell) := []) : Option Verdict := do
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } } builtinStringPatternCompiler model).toOption
  let data ← (readDocument {
    flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] } (input scenario)).toOption
  let document ← (checkDocument prepared "en_US" data.data).toOption
  let parsed ← (parseText .english condition).toOption
  let checked ← (lowerCondition model ["Form"] false parsed.body).toOption
  let .leaf leaf := checked.core | none
  let context : AddressedValidationEvaluationContext model := {
    scalar := { fields := document.flatContext, groups := GroupPresenceContext.unavailable }, outer := []
    input := .partialView document fun environment field => match changes.find? (·.1 == field) with
      | some (_, cell) => pure cell
      | none => (fun cell => some cell.cell) <$> document.addressedCell environment field }
  let result ← leaf.evalAddressedPartial? context scope (fun _ => true)
    (fun _ _ => .error (.checkedDocumentRequired [])) none
  result.toOption

example : [("Length(Rows/Text For Key)", "2"), ("RangeAsNumber(Rows/Text For Key,2,2)", "2"),
    ("FieldValueAsNumber(Rows/Text For Key)", "12")].all (fun (expression, expected) =>
      partialVerdict (expression ++ " == " ++ expected) == some (.fired .value) &&
      partialVerdict (expression ++ " == 0") .full { key := "missing" } == some (.fired .omission) &&
      partialVerdict (expression ++ " == 0") (.partialSet []) { key := "missing" } == some .unknown &&
      partialVerdict (expression ++ " == 0") .full {} [(4, some (checkAdmittedRawCell .empty))] == some (.fired .omission) &&
      partialVerdict (expression ++ " == 0") .full {} [(4, none)] == some .unknown &&
      partialVerdict (expression ++ " == 0") .full {} [(4, some malformedCheckedCell)] == some .unknown) = true := by native_decide

example : partialVerdict "FieldValueAsNumber(Rows/Text For Key) == 34" .full { key := "missing" }
      [(1, some (checkAdmittedRawCell (.parsed (.str "R2"))))] = some (.fired .value) ∧
    partialVerdict "FieldValueAsNumber(Rows/Enum ->Numeric For Key) == -3.25" = some (.fired .value) ∧
    partialVerdict "FieldValueAsNumber(Rows/Text For \"R1\") + FieldValueAsNumber(Rows/Text For \"R2\") == 46" =
      some (.fired .value) := by native_decide

example : evaluate "1" true { key := "missing", producer := some ("Key", "\"R2\"") }
      (some "FieldValueAsNumber(Rows/Text For Key) == 34") = some (.inr ["value 1"]) ∧
    evaluate "1" true { text := "bad", producer := some ("Rows/Text", "\"789\"") }
      (some "Length(Rows/Text For Key) == 3") = some (.inr ["value 1"]) ∧
    partialVerdict "Length(Rows/Text For Key) >= 0" .full { key := "missing" } = some (.fired .value) ∧
    partialVerdict "FieldValueAsNumber(Rows/Text For Key) >= 0" .full { key := "missing" } = some (.fired .omission) := by native_decide

private def sourceSummary (expression : String) : Option (List FieldId × List FieldId × Nat) := do
  let parsed ← (parseText .english expression).toOption
  let .indexedString surface operation ← (lowerComputationNumericAtom model ["Form"] parsed.body).toOption | none
  let source ← (elaborateIndexedStringNumericSource model ["Form"] surface operation).toOption
  pure ((model.fields.filter fun field => source.referencesField field.id).map (·.id), source.boundFieldIds, source.projection.scale)

example : sourceSummary "Length(Rows/Text For Key)" = some ([1, 3, 4], [1], 0) ∧
    sourceSummary "FieldValueAsNumber(Rows/Enum ->Numeric For Key)" = some ([1, 3, 5], [1], 2) ∧
    sourceSummary "FieldValueAsNumber(Rows/Enum For \"R1\")" = some ([3, 5], [], 1) := by native_decide

end A12Kernel.Dm.IndexedStringNumericLocks
