import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Document
import A12Kernel.Elaboration.GeneratedComputationValidation.Assembly
import A12Kernel.Elaboration.ValidationCondition.Reference

namespace A12Kernel.Dm.IndexedComparisonLocks

private def model : FlatModel := {
  fields := [
    { id := 1, name := "Key", groupPath := ["Form"], policy := { kind := .string } },
    { id := 2, name := "Fallback", groupPath := ["Form"], policy := { kind := .boolean } },
    { id := 3, name := "Out", groupPath := ["Form"], policy := { kind := .number { scale := 0, signed := true } } },
    { id := 4, name := "Code", groupPath := ["Form", "Rows"], repeatableScope := [10],
      policy := { kind := .string }, stringPolicy := { maxLength := some 3 } },
    { id := 5, name := "Flag", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .boolean } },
    { id := 6, name := "Agreed", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .confirm } },
    { id := 7, name := "Span", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .dateRange },
      dateRangePolicy := some { format := "yyyy-MM-dd", separator := "/" } },
    { id := 8, name := "RowOut", groupPath := ["Form", "Rows"], repeatableScope := [10],
      policy := { kind := .number { scale := 0, signed := true } } }]
  repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 3, indexField := some 4 }] }

private def input (flag fallback : String) (key : String := "one")
    (secondCode : String := "two") (agreed : String := "")
    (firstSpan secondSpan : String := "") : Option (CheckedDocument model) := do
  let data := Lean.Json.mkObj [("Form", Lean.Json.mkObj [
    ("Key", .str key), ("Fallback", .str fallback), ("Out", .str "99"),
    ("Rows", .arr #[
      Lean.Json.mkObj [("RowOut", .str "99"), ("Code", .str "one"), ("Flag", .str flag), ("Agreed", .str agreed), ("Span", .str firstSpan)],
      Lean.Json.mkObj [("RowOut", .str "99"), ("Code", .str secondCode), ("Flag", .str "false"), ("Span", .str secondSpan)]])])]
  let dm : DmModel := { flat := model, computations := [], rules := [], conditionLanguage := "en_US", refusals := [] }
  let document ← (readDocument dm data).toOption
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } } builtinStringPatternCompiler model).toOption
  (checkDocument prepared "en_US" document.data).toOption

private def validation (expression flag fallback : String) (key : String := "one")
    (secondCode : String := "two") (agreed : String := "")
    (firstSpan secondSpan : String := "") : Option Verdict := do
  let document ← input flag fallback key secondCode agreed firstSpan secondSpan
  let parsed ← (parseText .english expression).toOption
  let condition ← (lowerCondition model ["Form"] false parsed.body).toOption
  (condition.core.evalAddressed {
    scalar := { fields := document.flatContext, groups := GroupPresenceContext.unavailable }
    outer := [], input := .checked document }).toOption

private def computation (expression flag fallback : String) (key : String := "one")
    (secondCode : String := "two") (agreed : String := "")
    (firstSpan secondSpan : String := "")
    (producer : Option (String × String) := none) (rowTarget := false) : Option String := do
  let document ← input flag fallback key secondCode agreed firstSpan secondSpan
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } } builtinStringPatternCompiler model).toOption
  let step ← (lowerComputation model .english {
    name := "Out", group := ["Form"],
    targetRelPath := if rowTarget then "../Rows/RowOut" else "../Out", commonPrecondition := some expression
    alternatives := [{ precondition := none, operation := "1" }], errorCodesToSuppress := [] }).toOption
  let producers ← producer.toList.mapM fun (target, operation) =>
    (lowerComputation model .english {
      name := target, group := ["Form"], targetRelPath := "../" ++ target, commonPrecondition := none,
      alternatives := [{ precondition := none, operation }], errorCodesToSuppress := [] }).toOption
  let results ← (runComputations { now := { epochMillis := 0 } } prepared document
    (step.2 :: producers.map (·.2))).toOption
  if rowTarget then pure (String.intercalate ","
    ((results.filter (·.pointer.endsWith "/RowOut")).map (·.outcome)))
  else (results.find? (·.pointer.endsWith "/Out")).map (·.outcome)

private def direct := "[Rows/Flag For Key] == True"
private def first := "FirstFilledValue(Rows/Flag For Key, Fallback) == True"
private def leadingFallback := "FirstFilledValue(Fallback, Rows/Flag For Key) == True"

example : model.validate.isOk = true ∧
    validation "[Fallback] == True" "false" "true" = some (.fired .value) ∧
    computation "[Fallback] == True" "false" "true" = some "value 1" := by native_decide

example : validation direct "true" "false" = some (.fired .value) ∧
    validation direct "false" "true" = some .notFired ∧
    validation direct "" "true" = some .notFired ∧
    validation direct "bad" "true" = some .unknown ∧
    validation direct "true" "true" "missing" = some .notFired ∧
    validation direct "true" "true" "one" "one" = some .unknown ∧
    validation direct "true" "true" "one" "long" = some (.fired .value) := by native_decide

example : computation direct "true" "false" = some "value 1" ∧
    computation direct "false" "true" = some "cleared" ∧
    computation direct "" "true" = some "cleared" ∧
    computation direct "bad" "true" = some "cleared" ∧
    computation direct "true" "true" "missing" = some "cleared" ∧
    computation direct "true" "true" "one" "one" = some "cleared" ∧
    computation direct "true" "true" "one" "long" = some "cleared" := by native_decide

example : validation "[Rows/Agreed For Key] != True" "true" "true" = some (.fired .omission) ∧
    computation "[Rows/Agreed For Key] != True" "true" "true" = some "value 1" ∧
    validation "True == [Rows/Agreed For Key]" "true" "true" (agreed := "true") = some (.fired .value) ∧
    computation "True == [Rows/Agreed For Key]" "true" "true" (agreed := "true") = some "value 1" := by native_decide

example : validation first "" "true" = some (.fired .omission) ∧
    computation first "" "true" = some "value 1" ∧
    computation first "false" "true" = some "cleared" ∧
    computation first "bad" "true" = some "cleared" ∧
    computation leadingFallback "bad" "true" = some "value 1" ∧
    computation leadingFallback "true" "true" "one" "long" = some "value 1" := by native_decide

example : ["[Rows/Flag For Key] == [Fallback]", "[Fallback] == [Rows/Flag For Key]"].all
    (fun expression => validation expression "true" "true" == some (.fired .value) &&
      computation expression "true" "true" == some "value 1") = true ∧
    ["FirstFilledValue(Rows/Flag For Key, Fallback) == [Fallback]",
     "[Fallback] == FirstFilledValue(Rows/Flag For Key, Fallback)"].all
    (fun expression => validation expression "" "true" == some (.fired .omission) &&
      computation expression "" "true" == some "value 1") = true := by native_decide

example : ["[Rows/Flag For Key] == Fallback", "FirstFilledValue(Rows/Flag For Key, Fallback) == Fallback"].all
    (fun expression => (validation expression "true" "true").isNone &&
      (computation expression "true" "true").isNone) = true := by native_decide

example : validation "[Rows/Span For \"one\"] == [Rows/Span For \"two\"]" "true" "true"
      (firstSpan := "2024-01-01/2024-01-10") (secondSpan := "2024-01-01/2024-01-10") = some (.fired .value) ∧
    computation "[Rows/Span For \"one\"] == [Rows/Span For \"two\"]" "true" "true"
      (firstSpan := "2024-01-01/2024-01-10") (secondSpan := "2024-01-01/2024-01-10") = some "value 1" := by native_decide

private def booleanLiteralComparisons : List (String × String) := [
  ("[Rows/Flag For Key] == True", "true"), ("True == [Rows/Flag For Key]", "true"),
  ("[Rows/Flag For Key] != False", "true"), ("False != [Rows/Flag For Key]", "true"),
  ("[Rows/Flag For Key] == False", "false"), ("False == [Rows/Flag For Key]", "false"),
  ("[Rows/Flag For Key] != True", "false"), ("True != [Rows/Flag For Key]", "false")]

example : booleanLiteralComparisons.all (fun (expression, filled) =>
    let cases : List (String × Verdict × String) := [
      (filled, .fired .value, "value 1"),
      (if filled == "true" then "false" else "true", .notFired, "cleared"),
      ("", .notFired, "cleared")]
    cases.all (fun (flag, verdict, outcome) =>
      validation expression flag "true" == some verdict &&
      computation expression flag "true" == some outcome)) = true := by native_decide

example : ([
    ("[Rows/Agreed For Key] == True", "true", .fired .value, "value 1"),
    ("True == [Rows/Agreed For Key]", "true", .fired .value, "value 1"),
    ("[Rows/Agreed For Key] == True", "", .notFired, "cleared"),
    ("True == [Rows/Agreed For Key]", "", .notFired, "cleared"),
    ("[Rows/Agreed For Key] != True", "true", .notFired, "cleared"),
    ("True != [Rows/Agreed For Key]", "true", .notFired, "cleared"),
    ("[Rows/Agreed For Key] != True", "", .fired .omission, "value 1"),
    ("True != [Rows/Agreed For Key]", "", .fired .omission, "value 1")]
    : List (String × String × Verdict × String)).all
    (fun (expression, agreed, verdict, outcome) =>
      validation expression "true" "true" (agreed := agreed) == some verdict &&
      computation expression "true" "true" (agreed := agreed) == some outcome) = true := by native_decide

example : [
    "[Rows/Agreed For Key] == False", "False == [Rows/Agreed For Key]",
    "[Rows/Agreed For Key] != False", "False != [Rows/Agreed For Key]",
    "[Rows/Flag For Key] > True"].all (fun expression =>
      (validation expression "true" "true" (agreed := "true")).isNone &&
      (computation expression "true" "true" (agreed := "true")).isNone) = true ∧
    (validation "FirstFilledValue(Rows/Agreed For Key, Rows/Agreed For \"two\") == True"
      "true" "true" (agreed := "true")).isNone = true ∧
    (computation "FirstFilledValue(Rows/Agreed For Key, Rows/Agreed For \"two\") == True"
      "true" "true" (agreed := "true")).isNone = true ∧
    validation "FirstFilledValue(Rows/Flag For Key, Rows/Flag For \"two\") == True" "true" "true" = some (.fired .value) ∧
    computation "FirstFilledValue(Rows/Flag For Key, Rows/Flag For \"two\") == True" "true" "true" = some "value 1" := by native_decide

private def rangeEqual := "[Rows/Span For \"one\"] == [Rows/Span For \"two\"]"
private def rangeDifferent := "[Rows/Span For \"one\"] != [Rows/Span For \"two\"]"
private def rangeFirst :=
  "FirstFilledValue(Rows/Span For \"one\", Rows/Span For \"two\") == [Rows/Span For \"two\"]"

example : ([
    ("2024-01-01/2024-01-10", [
      (rangeEqual, .fired .value, "value 1"), (rangeDifferent, .notFired, "cleared"),
      (rangeFirst, .fired .value, "value 1")]),
    ("2024-02-01/2024-02-10", [
      (rangeEqual, .notFired, "cleared"), (rangeDifferent, .fired .value, "value 1"),
      (rangeFirst, .notFired, "cleared")]),
    ("", [
      (rangeEqual, .notFired, "cleared"), (rangeDifferent, .notFired, "cleared"),
      (rangeFirst, .fired .omission, "value 1")]),
    ("bad", [
      (rangeEqual, .unknown, "cleared"), (rangeDifferent, .unknown, "cleared"),
      (rangeFirst, .unknown, "cleared")])]
    : List (String × List (String × Verdict × String))).all
    (fun (firstSpan, cases) => cases.all (fun (expression, verdict, outcome) =>
      validation expression "true" "true"
        (firstSpan := firstSpan) (secondSpan := "2024-01-01/2024-01-10") == some verdict &&
      computation expression "true" "true"
        (firstSpan := firstSpan) (secondSpan := "2024-01-01/2024-01-10") == some outcome)) = true := by native_decide

example : computation direct "false" "false" "missing"
      (producer := some ("Key", "\"one\"")) = some "cleared" ∧
    computation direct "true" "false" "missing"
      (producer := some ("Key", "\"one\"")) = some "value 1" ∧
    computation direct "false" "false"
      (producer := some ("Rows/Flag", "True")) = some "value 1" ∧
    computation first "" "false"
      (producer := some ("Fallback", "True")) = some "value 1" := by native_decide

private def partialVerdict (expression : String) (scope : ValidationRelevanceScope := .full)
    (changes : List (FieldId × Option CheckedCell) := []) : Option Verdict := do
  let document ← input "true" "true"
  let parsed ← (parseText .english expression).toOption
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

example : [direct, first].all (fun expression =>
    partialVerdict expression == some (.fired .value) &&
    partialVerdict expression (.partialSet []) == some .unknown &&
    partialVerdict expression .full [(5, none)] == some .unknown &&
    partialVerdict expression .full [(5, some malformedCheckedCell)] == some .unknown) = true ∧
    partialVerdict leadingFallback .full [(5, none)] = some (.fired .value) := by native_decide

private def generatedGuard (expression flag : String) : Option Bool := do
  let document ← input flag "true"
  let parsed ← (parseText .english expression).toOption
  let surface ← (lowerGuard model ["Form"] false parsed.body (some ["Form"])).toOption
  let guard ← (model.elaborateCheckedComputationCondition ["Form"] ["Form"] surface).toOption
  let operation ← (elaborateCompleteNumericComputationOperation model ["Form"] 3
    (.literal { value := 1, authoredScale := 0 }) false).toOption
  let table : GeneratedComputationTable (CheckedNumericComputationOperation model) (CheckedComputationCondition model) := {
    targetField := 3, name := "Computed", commonPrecondition := some guard
    alternatives := .singleton { operation }, messagePlan := { parts := [] } }
  let rule ← (assembleGeneratedNumericOperationTableRule model table).toOption
  let outcome ← (rule.evalAddressedFull {
    scalar := { fields := document.flatContext, groups := GroupPresenceContext.unavailable }
    outer := [], input := .checked document } true).toOption
  pure (match outcome with | .fired _ => true | _ => false)

example : generatedGuard direct "true" = some true ∧
    generatedGuard direct "false" = some false ∧
    generatedGuard first "" = some true ∧
    generatedGuard first "bad" = some false := by native_decide

private def references (expression : String) : Option (List MessagePointer) := do
  let parsed ← (parseText .english expression).toOption
  let checked ← (lowerCondition model ["Form"] false parsed.body).toOption
  (checked.core.referencePointers [] (some {
    cache := { insertions := [{ group := 10, parentPath := [], key := .text "one", row := 1 }] }
    keyAt := fun address => if address.field == 1 then some (.text "one") else none })).toOption

example : references direct = some [
    { field := 1, coordinates := [] }, { field := 4, coordinates := [.concrete 1] },
    { field := 5, coordinates := [.concrete 1] }] := by native_decide

example : ["[Rows/Flag For Key] == [Rows/Flag]",
    "FirstFilledValue(Rows/Flag For Key, Fallback) == [Rows/Flag]"].all (fun expression =>
      computation expression "true" "false" (rowTarget := true) == some "value 1,cleared" &&
      (computation expression "true" "false").isNone) = true := by native_decide

example : (computation "[Rows/Flag For Rows/Code] == True" "true" "false" (rowTarget := true)).isNone ∧
    computation direct "true" "false" (rowTarget := true) = some "value 1,value 1" := by native_decide

end A12Kernel.Dm.IndexedComparisonLocks
