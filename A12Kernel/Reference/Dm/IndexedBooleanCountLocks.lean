import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Document
import A12Kernel.Reference.Dm.LowerValidation

namespace A12Kernel.Dm.IndexedBooleanCountLocks

private def model : FlatModel := {
  fields := [
    { id := 1, name := "Key", groupPath := ["Form"], policy := { kind := .string } },
    { id := 2, name := "Out", groupPath := ["Form"], policy := { kind := .number { scale := 0, signed := true } } },
    { id := 3, name := "Code", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .string } },
    { id := 4, name := "B", groupPath := ["Form", "Rows", "Flags"], repeatableScope := [10], policy := { kind := .boolean } },
    { id := 5, name := "C", groupPath := ["Form", "Rows", "Flags"], repeatableScope := [10], policy := { kind := .confirm } },
    { id := 6, name := "B", groupPath := ["Form", "Rows", "Inner"], repeatableScope := [10, 20], policy := { kind := .boolean } },
    { id := 7, name := "Fallback", groupPath := ["Form"], policy := { kind := .boolean } },
    { id := 8, name := "Out", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .number { scale := 0, signed := true } } }]
  repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 3, indexField := some 3 },
    { level := 20, path := ["Form", "Rows", "Inner"], repeatability := some 3 }] }

private structure Scenario where
  key : String := "R1"
  boolean : String := "true"
  confirm : String := "true"
  secondCode : String := "R2"
  inner : List String := ["true", "false"]
  repeated : Bool := false
  producer : Option (String × String) := none

private def input (scenario : Scenario) : Lean.Json :=
  let row (code boolean confirm : String) := Lean.Json.mkObj [
    ("Code", .str code), ("Flags", Lean.Json.mkObj [("B", .str boolean), ("C", .str confirm)]),
    ("Inner", .arr (scenario.inner.map (fun value => Lean.Json.mkObj [("B", .str value)])).toArray), ("Out", .str "99")]
  Lean.Json.mkObj [("Form", Lean.Json.mkObj [("Key", .str scenario.key), ("Out", .str "99"), ("Fallback", .str "false"),
    ("Rows", .arr #[row "R1" scenario.boolean scenario.confirm, row scenario.secondCode "false" ""])])]

private def evaluate (expression : String) (computation : Bool)
    (scenario : Scenario := {}) (guard : Option String := none) : Option (Sum Verdict (List String)) := do
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let data ← (readDocument {
    flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] } (input scenario)).toOption
  let document ← (checkDocument prepared "en_US" data.data).toOption
  if computation then
    let step ← (lowerComputation model .english {
      name := "Result", group := ["Form"], targetRelPath := if scenario.repeated then "../Rows/Out" else "../Out",
      commonPrecondition := guard, alternatives := [{ precondition := none, operation := expression }], errorCodesToSuppress := [] }).toOption
    let producers ← scenario.producer.toList.mapM fun (target, operation) =>
      (lowerComputation model .english {
        name := "Producer", group := ["Form"], targetRelPath := "../" ++ target,
        commonPrecondition := none, alternatives := [{ precondition := none, operation }], errorCodesToSuppress := [] }).toOption
    let results ← (runComputations world prepared document (step.2 :: producers.map (·.2))).toOption
    pure (.inr ((results.filter (·.pointer.endsWith "/Out")).map (·.outcome)))
  else
    let parsed ← (parseText .english expression).toOption
    let condition ← (lowerCondition model ["Form"] false parsed.body).toOption
    Sum.inl <$> (condition.core.evalAddressed {
      scalar := { fields := document.flatContext, groups := GroupPresenceContext.unavailable },
      outer := [], input := .checked document }).toOption

example : [("NumberOfValueInFields(True In Rows/Flags/B For Key, Fallback)", "1", Polarity.value),
    ("NumberOfValueInFields(False In Rows/Flags/B For Key, Fallback)", "1", .value),
    ("NumberOfValueInFields(True In Rows/Flags For Key)", "2", .value),
    ("NumberOfValueInFields(True In Rows/Inner*/B For Key)", "1", .omission)].all (fun (expression, expected, polarity) =>
      evaluate (expression ++ " == " ++ expected) false == some (.inl (.fired polarity)) &&
      evaluate expression true == some (.inr ["value " ++ expected])) = true := by native_decide

example : evaluate "NumberOfValueInFields(False In Rows/Flags/B For \"R1\", Rows/Flags/B For \"R2\")" true =
    some (.inr ["value 1"]) ∧
    (evaluate "NumberOfValueInFields(True In Rows/Inner For Key)" true).isNone = true ∧
    evaluate "NumberOfValueInFields(False In Rows/Inner* For Key)" true = some (.inr ["value 1"]) := by native_decide

example : [({ key := "missing" } : Scenario), { boolean := "" }].all (fun scenario =>
    evaluate "NumberOfValueInFields(True In Rows/Flags/B For Key, Fallback) == 0" false scenario ==
      some (.inl (.fired .omission)) &&
    evaluate "NumberOfValueInFields(True In Rows/Flags/B For Key, Fallback)" true scenario == some (.inr ["value 0"])) = true ∧
    evaluate "NumberOfValueInFields(True In Rows/Flags/C For Key, Fallback)" true { confirm := "" } = some (.inr ["value 0"]) := by native_decide

example : [({ boolean := "bad" } : Scenario), { secondCode := "R1" }].all (fun scenario =>
    evaluate "NumberOfValueInFields(True In Rows/Flags/B For Key, Fallback) == 0" false scenario == some (.inl .unknown) &&
    evaluate "NumberOfValueInFields(True In Rows/Flags/B For Key, Fallback)" true scenario == some (.inr ["cleared"])) = true ∧
    evaluate "NumberOfValueInFields(True In Rows/Flags/C For Key, Fallback)" true { confirm := "false" } = some (.inr ["cleared"]) := by native_decide

example : ["NumberOfValueInFields(False In Rows/Flags/C For Key, Fallback)",
    "NumberOfValueInFields(False In Rows/Flags For Key)",
    "NumberOfValueInFields(True In Rows/Code For Key, Fallback)",
    "NumberOfValueInFields(True In Rows/Flags/B For Key)"].all
    (fun expression => (evaluate (expression ++ " == 0") false).isNone && (evaluate expression true).isNone) = true := by native_decide

example : [false, true].all (fun repeated =>
    evaluate "NumberOfValueInFields(True In Rows/Flags/B For Key, Fallback)" true
      { repeated, key := "missing", producer := some ("Key", "\"R1\"") } ==
      some (.inr (List.replicate (if repeated then 2 else 1) "value 1")) &&
    evaluate "NumberOfValueInFields(True In Rows/Flags/B For Key, Fallback)" true
      { repeated, boolean := "bad", producer := some ("Rows/Flags/B", "False") } ==
      some (.inr (List.replicate (if repeated then 2 else 1) "value 0"))) = true := by native_decide

example : evaluate "1" true {} (some "NumberOfValueInFields(True In Rows/Flags For Key) == 2") =
    some (.inr ["value 1"]) := by native_decide

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

example : ["NumberOfValueInFields(True In Rows/Flags/B For Key, Fallback)",
    "NumberOfValueInFields(False In Rows/Flags/B For Key, Fallback)"].all (fun expression =>
      partialVerdict (expression ++ " == 1") == some (.fired .value) &&
      partialVerdict (expression ++ " == 1") (.partialSet []) == some .unknown &&
      partialVerdict (expression ++ " == 1") .full {} [(4, none)] == some .unknown &&
      partialVerdict (expression ++ " == 1") .full {} [(4, some malformedCheckedCell)] == some .unknown) = true ∧
    partialVerdict "NumberOfValueInFields(True In Rows/Flags For Key) == 2" = some (.fired .value) ∧
    partialVerdict "NumberOfValueInFields(True In Rows/Inner*/B For Key) == 1" = some (.fired .omission) := by native_decide

example : partialVerdict "NumberOfValueInFields(True In Rows/Flags/B For Key, Fallback) == 0" .full
      { key := "missing" } = some (.fired .omission) ∧
    partialVerdict "NumberOfValueInFields(True In Rows/Flags/B For Key, Fallback) == 0" .full {}
      [(4, some (checkAdmittedRawCell (.parsed (.bool false))))] = some (.fired .value) ∧
    partialVerdict "NumberOfValueInFields(True In Rows/Flags/B For Key, Fallback) == 0" .full { key := "missing" }
      [(1, some (checkAdmittedRawCell (.parsed (.str "R2"))))] = some (.fired .value) := by native_decide

example : evaluate "NumberOfValueInFields(True In Rows/Inner*/B For Key) == 1" false
      { inner := ["true", "false", "false", "bad"] } = some (.inl (.fired .value)) ∧
    evaluate "NumberOfValueInFields(True In Rows/Inner*/B For Key)" true
      { inner := ["true", "false", "false", "bad"] } = some (.inr ["value 1"]) ∧
    evaluate "NumberOfValueInFields(True In Rows/Inner*/B For Key) == 0" false { key := "missing" } =
      some (.inl (.fired .value)) ∧
    evaluate "NumberOfValueInFields(True In Rows/Flags For Key) == 0" false { key := "missing" } =
      some (.inl (.fired .omission)) := by native_decide

private def dependencies (expression : String) : Option (List FieldId) := do
  let parsed ← (parseText .english expression).toOption
  let .booleanValueCount expected source ← (lowerComputationNumericAtom model ["Form"] parsed.body).toOption | none
  let checked ← (elaborateBooleanValueCountSource model ["Form"] expected source).toOption
  pure ((model.fields.filter fun field => checked.referencesField field.id).map (·.id))

example : dependencies "NumberOfValueInFields(True In Rows/Flags/B For Key, Fallback)" = some [1, 3, 4, 7] ∧
    dependencies "NumberOfValueInFields(True In Rows/Flags For \"R1\")" = some [3, 4, 5] := by native_decide

private def relevant (path : List String) : RelevantEntityPattern :=
  { path := "Form" :: path, indices := (List.range (path.length + 1)).map fun _ => .all }

example : partialVerdict "NumberOfValueInFields(True In Rows/Inner*/B For Key) == 1"
      (.partialSet [relevant ["Key"], relevant ["Rows", "Code"],
        { path := ["Form", "Rows", "Inner", "B"], indices := [.all, .concrete 1, .all, .all] }])
      { inner := ["true"] } = some (.fired .omission) ∧
    partialVerdict "NumberOfValueInFields(True In Rows/Inner*/B For Key) == 1"
      (.partialSet [relevant ["Key"], relevant ["Rows", "Code"],
        { path := ["Form", "Rows", "Inner", "B"], indices := [.all, .concrete 1, .concrete 1, .all] }]) { inner := ["true"] } = some .unknown ∧
    partialVerdict "NumberOfValueInFields(True In Rows/Flags For Key) == 2"
      (.partialSet [relevant ["Key"], relevant ["Rows", "Code"], relevant ["Rows", "Flags", "B"]]) =
      some .unknown := by native_decide

end A12Kernel.Dm.IndexedBooleanCountLocks
