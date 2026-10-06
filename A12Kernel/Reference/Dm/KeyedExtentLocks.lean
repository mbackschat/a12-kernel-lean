import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Document
import A12Kernel.Reference.Dm.LowerValidation

namespace A12Kernel.Dm.KeyedExtentLocks

private def model : FlatModel := {
  fields := [
    { id := 1, name := "Code", groupPath := ["Form", "Packages"], repeatableScope := [10], policy := { kind := .string } },
    { id := 2, name := "Header", groupPath := ["Form", "Packages"], repeatableScope := [10], policy := { kind := .number { scale := 0, signed := true } } },
    { id := 3, name := "Weight", groupPath := ["Form", "Packages", "Items"], repeatableScope := [10,20], policy := { kind := .number { scale := 0, signed := true } } },
    { id := 4, name := "Quantity", groupPath := ["Form", "Packages", "Items"], repeatableScope := [10,20], policy := { kind := .number { scale := 0, signed := true } } },
    { id := 5, name := "Key", groupPath := ["Form"], policy := { kind := .string } },
    { id := 6, name := "Out", groupPath := ["Form"], policy := { kind := .number { scale := 0, signed := true } } }]
  repeatableGroups := [
    { level := 10, path := ["Form", "Packages"], repeatability := some 3, indexField := some 1 },
    { level := 20, path := ["Form", "Packages", "Items"], repeatability := some 2 }] }

private def input (key : String) (duplicate : Bool := false) (bad : Bool := false) (invalidIndex : Bool := false) (emptySecond : Bool := false) (sourceModel : FlatModel := model) (header : String := "1") : Option (CheckedDocument sourceModel) := do
  let numericIndex := (sourceModel.lookupUniqueId 1).toOption.any (fun field => field.policy.kind.surfaceKind == .number)
  let package (key : String) (weights : List String) := Lean.Json.mkObj [
    ("Code", .str key), ("Header", .str header),
    ("Items", .arr (weights.map fun weight => Lean.Json.mkObj [
      ("Weight", .str weight), ("Quantity", .str "2")]).toArray)]
  let data := Lean.Json.mkObj [("Form", Lean.Json.mkObj [
    ("Key", .str key), ("Out", .str "99"),
    ("Packages", .arr #[package (if numericIndex then "1" else "P1") ["2", if bad then "bad" else "5"], package (if invalidIndex then "" else if duplicate then (if numericIndex then "1" else "P1") else (if numericIndex then "2" else "P2")) (if emptySecond then [] else ["11"])])])]
  let dm : DmModel := { flat := sourceModel, computations := [], rules := [], conditionLanguage := "en_US", refusals := [] }
  let input ← (readDocument dm data).toOption
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } } builtinStringPatternCompiler sourceModel).toOption
  (checkDocument prepared "en_US" input.data).toOption

private def validationVerdict (expression : String) (key : String := "P1") (duplicate : Bool := false) (bad : Bool := false) (invalidIndex : Bool := false) (emptySecond : Bool := false) : Option Verdict := do
  let checked ← input key duplicate bad invalidIndex emptySecond
  let parsed ← (parseText .english expression).toOption
  let condition ← (lowerCondition model ["Form"] false parsed.body).toOption
  let verdict ← (condition.core.evalAddressed {
    scalar := { fields := checked.flatContext, groups := GroupPresenceContext.unavailable },
    outer := [], input := .checked checked }).toOption
  pure verdict

private def validation (expression : String) (key : String := "P1") (duplicate : Bool := false)
    (bad : Bool := false) (invalidIndex : Bool := false) : Option Bool :=
  (validationVerdict expression key duplicate bad invalidIndex).map fun
    | .fired _ => true | _ => false

private def computation (operation : String) (guard : String := "FieldFilled(Key)")
    (key : String := "P1") (duplicate : Bool := false) (bad : Bool := false) (invalidIndex : Bool := false) (fallback : Bool := false) (producer : Option (String × String) := none) : Option String := do
  let checked ← input key duplicate bad invalidIndex
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let lowered ← (lowerComputation model .english {
    name := "Consumer", group := ["Form"], targetRelPath := "../Out", commonPrecondition := if fallback then none else some guard,
    alternatives := if fallback then [{ precondition := some guard, operation }, { precondition := some "FieldFilled(Key)", operation := "2" }]
      else [{ precondition := none, operation }], errorCodesToSuppress := [] }).toOption
  let producers ← producer.toList.mapM fun (target, operation) =>
    (lowerComputation model .english {
      name := "Producer", group := ["Form"], targetRelPath := "../" ++ target,
      commonPrecondition := none, alternatives := [{ precondition := none, operation }], errorCodesToSuppress := [] }).toOption
  let results ← (runComputations world prepared checked (lowered.2 :: producers.map (·.2))).toOption
  ((results.filter (·.pointer.endsWith "/Out")).head?).map (·.outcome)

example : validation "NumberOfFilledFields(Packages For Key) == 6" = some true ∧
    computation "NumberOfFilledFields(Packages For Key)" = some "value 6" ∧
    validation "NumberOfFilledFields(Packages For Key) == 4" "P2" = some true ∧
    computation "NumberOfFilledFields(Packages For Key)" "FieldFilled(Key)" "P2" = some "value 4" := by native_decide

example : validation "AllFieldsFilled(Packages For Key)" = some true ∧
    validation "AllFieldsFilled(Packages For Key)" "P2" = some false ∧
    validation "NoFieldFilled(Packages For Key)" "missing" = some true ∧
    computation "1" "NoFieldFilled(Packages For Key)" "missing" = some "value 1" := by native_decide

example : validation "NumberOfFilledFields(Packages/Items*/Weight For Key) == 2" = some true ∧
    computation "NumberOfFilledFields(Packages/Items*/Weight For Key)" = some "value 2" ∧
    validation "AllFieldsFilled(Packages/Items*/Weight For Key)" = some true ∧
    computation "1" "AllFieldsFilled(Packages/Items*/Weight For Key)" = some "value 1" := by native_decide

example : validation "NoFieldFilled(Packages For Key)" "P1" true = some false ∧
    computation "NumberOfFilledFields(Packages For Key)" "FieldFilled(Key)" "P1" true = some "cleared" ∧
    computation "1" "NoFieldFilled(Packages For Key)" "P1" false true = some "cleared" ∧
    computation "1" "AtLeastOneFieldFilled(Packages For Key)" "P1" false true = some "value 1" := by native_decide

example : validation "NumberOfFilledFields(Packages/Items* For Key) == 4" = some true ∧
    computation "NumberOfFilledFields(Packages/Items* For Key)" = some "value 4" ∧
    validation "AllFieldsFilled(Packages/Items* For Key)" = some true ∧
    computation "1" "NoFieldFilled(Packages/Items* For Key)" "missing" = some "value 1" := by native_decide

private def operators := ["AllFieldsFilled", "NoFieldFilled", "AtLeastOneFieldFilled",
  "MoreThanOneFieldFilled", "NotAllFieldsFilled", "NotExactlyOneFieldFilled", "FieldsNotCollectivelyFilled"]

private def signature (compute : Bool) (key : String) (operand : String := "Packages For Key") : Option String := do
  let results ← operators.mapM fun operator => do
    let condition := operator ++ "(" ++ operand ++ ")"
    if compute then pure ((← computation "1" condition key) == "value 1") else validation condition key
  pure (String.ofList (results.map fun result => if result then 'T' else 'F'))

example : [false, true].map (signature · "P1") = [some "TFTTFTF", some "TFTTFTF"] ∧
    [false, true].map (signature · "P2") = [some "FFTTTTT", some "FFTTTTT"] ∧
    [false, true].map (signature · "missing") = [some "FTFFTTF", some "FTFFTTF"] := by native_decide

example : validation "NumberOfFilledFields(Packages For Key) == 6" "P1" false false true = some true ∧
    computation "NumberOfFilledFields(Packages For Key)" "FieldFilled(Key)" "P1" false false true = some "cleared" ∧
    computation "1" "AllFieldsFilled(Packages For Key)" "missing" false false false true = some "value 2" ∧
    computation "1" "AllFieldsFilled(Packages For Key)" "P1" false true false true = some "cleared" ∧
    computation "1" "NoFieldFilled(Packages For Key)" "P1" false true false true = some "value 2" := by native_decide

example : validation "NumberOfFilledFields(Packages For \"P1\",Packages/Header For \"P1\") == 7" = none ∧
    validation "NumberOfFilledFields(Packages For \"P1\",Packages/Header For \"P2\") == 7" = some true ∧
    validation "NumberOfFilledFields(Packages For Key,Packages For Key) == 12" = none ∧
    validation "NumberOfFilledFields(Packages/Items For Key) == 4" = none ∧
    validation "NumberOfFilledFields(Packages*/Items*/Weight For Key) == 3" = none := by native_decide

private def missingEnvironmentRefused : Option Bool := do
  let source ← (elaborateKeyedEntityExtent model ["Form"] {
    target := .group { base := .relative 0, groups := ["Packages"] }, key := .literal (.text "P1") }).toOption
  let checked ← input "P1"
  let readColumn : SemanticIndexColumnReader := fun group target outer => do
    let column ← checked.resolveSemanticIndexColumnWith checked.read group target outer
    pure { column with entries := column.entries.map fun entry => { entry with environment := none } }
  pure (!(source.selectWith .validation readColumn [] checked.flatContext.read checked.flatContext.storedText).isOk)

example : missingEnvironmentRefused = some true := by native_decide

example : [false, true].map (fun compute => signature compute "P1" "Packages/Items*/Weight For Key") =
      [some "TFTTFTF", some "TFTTFTF"] ∧
    [false, true].map (fun compute => signature compute "P2" "Packages/Items*/Weight For Key") =
      [some "FFTFTFT", some "FFTFTFT"] ∧
    [false, true].map (fun compute => signature compute "P2" "Packages/Items* For Key") =
      [some "FFTTTTT", some "FFTTTTT"] := by native_decide

example : computation "NumberOfFilledFields(Packages For Key)" "FieldFilled(Key)" "missing" false false false false
      (some ("Key", "\"P1\"")) = some "value 6" ∧
    computation "NumberOfFilledFields(Packages For Key)" "FieldFilled(Key)" "P1" false true false false
      (some ("Packages/Items/Weight", "4")) = some "value 6" ∧
    computation "NumberOfFilledFields(Packages For Key)" "FieldFilled(Key)" "missing" = some "value 0" ∧
    validation "NoFieldFilled(Packages For Key)" "" = some true ∧
    validation "NumberOfFilledFields(Packages For Packages/Code) == 6" = none ∧
    validation "NumberOfFilledFields(Packages For Out) == 6" = none := by native_decide

example : computation "[Packages/Header For Key]" "FieldFilled(Key)" "missing" false false false false
      (some ("Key", "\"P1\"")) = some "value 1" := by native_decide

private def numericIndexCount (keySource : String) (operator : String := "NumberOfFilledFields") : Option String := do
  let model := { model with fields := model.fields.map fun field =>
    if field.id == 1 || field.id == 5 then { field with policy := { kind := .number { scale := 0, signed := true } } } else field }
  let package (code : String) (items : Array Lean.Json) := Lean.Json.mkObj [
    ("Code", .str code), ("Header", .str "1"), ("Items", .arr items)]
  let data := Lean.Json.mkObj [("Form", Lean.Json.mkObj [
    ("Key", .str "01"), ("Out", .str "99"), ("Packages", .arr #[
      package "1" #[Lean.Json.mkObj [("Weight", .str "2"), ("Quantity", .str "3")]], package "2" #[]])])]
  let dm : DmModel := { flat := model, computations := [], rules := [], conditionLanguage := "en_US", refusals := [] }
  let input ← (readDocument dm data).toOption
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  let lowered ← (lowerComputation model .english {
    name := "Consumer", group := ["Form"], targetRelPath := "../Out", commonPrecondition := none,
    alternatives := [{ precondition := none, operation := operator ++ "(Packages For " ++ keySource ++ ")" }],
    errorCodesToSuppress := [] }).toOption
  let results ← (runComputations world prepared checked [lowered.2]).toOption
  (results.head?).map (·.outcome)

example : numericIndexCount "Key" = some "value 4" ∧
    numericIndexCount "\"01\"" = some "value 4" ∧
    numericIndexCount "\"2\"" = some "value 2" ∧
    numericIndexCount "\"bad\"" = none := by native_decide

example : validation "Sum(Packages/Items*/Weight For Key) == 7" = some true ∧
    computation "Sum(Packages/Items*/Weight For Key)" = some "value 7" ∧
    validation "MinValue(Packages/Items*/Weight For Key) == 2" = some true ∧
    computation "MaxValue(Packages/Items*/Weight For Key)" = some "value 5" ∧
    computation "NumberOfDifferentValues(Packages/Items*/Weight For Key)" = some "value 2" ∧
    computation "FirstFilledValue(Packages/Items*/Weight For Key, Packages/Header For Key)" = some "value 2" := by native_decide

private def numberFamily (operand : String) (key : String) (expected : List String) : Bool :=
  let operators := ["Sum", "MinValue", "MaxValue", "NumberOfDifferentValues", "FirstFilledValue"]
  (operators.zip expected).all fun (operator, expected) =>
    let call := operator ++ "(" ++ operand ++ ")"
    validation (call ++ " == " ++ expected) key == some true &&
      computation call "FieldFilled(Key)" key == some ("value " ++ expected)

example : numberFamily "Packages/Items*/Weight For Key" "P1" ["7", "2", "5", "2", "2"] ∧
    numberFamily "Packages/Items*/Weight For Key" "P2" ["11", "11", "11", "1", "11"] ∧
    numberFamily "Packages/Items* For Key" "P1" ["11", "2", "5", "2", "2"] ∧
    numberFamily "Packages/Header For Key,Packages/Header For \"P2\"" "P1" ["2", "1", "1", "1", "1"] := by native_decide

example : numberFamily "Packages/Items*/Weight For Key" "missing" ["0", "0", "0", "0", "0"] ∧
    computation "FirstFilledValue(Packages/Items*/Weight For Key,Packages/Header For \"P1\")"
      "FieldFilled(Key)" "missing" = some "value 1" := by native_decide

example : ["Sum", "MinValue", "MaxValue", "NumberOfDifferentValues"].all (fun operator =>
    validation (operator ++ "(Packages/Items*/Weight For Key) == 7") "P1" false true == some false &&
    computation (operator ++ "(Packages/Items*/Weight For Key)") "FieldFilled(Key)" "P1" false true == some "cleared" &&
    computation (operator ++ "(Packages/Items*/Weight For Key)") "FieldFilled(Key)" "P1" true == some "cleared") := by native_decide

example : validation "Sum(Packages/Items*/Weight For Key) == 7" "P1" false false true = some true ∧
    computation "Sum(Packages/Items*/Weight For Key)" "FieldFilled(Key)" "P1" false false true = some "cleared" ∧
    validation "FirstFilledValue(Packages/Items*/Weight For Key) == 2" "P1" false true = some true ∧
    computation "FirstFilledValue(Packages/Items*/Weight For Key)" "FieldFilled(Key)" "P1" false true = some "value 2" ∧
    computation "FirstFilledValue(Packages/Items*/Weight For Key)" "FieldFilled(Key)" "P1" true = some "cleared" := by native_decide

example : computation "Sum(Packages/Items*/Weight For Key)" "FieldFilled(Key)" "missing" false false false false
      (some ("Key", "\"P1\"")) = some "value 7" ∧
    computation "Sum(Packages/Items*/Weight For Key)" "FieldFilled(Key)" "P1" false true false false
      (some ("Packages/Items/Weight", "4")) = some "value 8" := by native_decide

example : numericIndexCount "Key" "Sum" = some "value 7" ∧
    numericIndexCount "\"01\"" "MinValue" = some "value 1" ∧
    numericIndexCount "Key" "MaxValue" = some "value 3" ∧
    numericIndexCount "Key" "NumberOfDifferentValues" = some "value 3" ∧
    numericIndexCount "Key" "FirstFilledValue" = some "value 1" ∧
    numericIndexCount "\"2\"" "Sum" = some "value 3" := by native_decide

example : validation "Sum(Packages For Key) == 7" = none ∧
    validation "Sum(Packages/Header For Key) == 1" = none ∧
    validation "Sum(Packages/Header For Key,Packages/Header For Key) == 2" = none ∧
    validation "Sum(Packages/Items For Key) == 11" = none := by native_decide

example : validation "NumberOfValueInFields(2 In Packages/Items* For Key) == 3" = some true ∧
    computation "NumberOfValueInFields(2 In Packages/Items* For Key)" = some "value 3" := by native_decide

example : computation "NumberOfValueInFields(2 In Packages/Items* For Key)" "FieldFilled(Key)" "missing" = some "value 0" ∧
    computation "NumberOfValueInFields(2 In Packages/Items* For Key)" "FieldFilled(Key)" "P1" true = some "cleared" ∧
    computation "NumberOfValueInFields(2 In Packages/Items* For Key)" "FieldFilled(Key)" "P1" false true = some "cleared" ∧
    validation "NumberOfValueInFields(2 In Packages/Items* For Key) == 3" "P1" false false true = some true ∧
    computation "NumberOfValueInFields(2 In Packages/Items* For Key)" "FieldFilled(Key)" "P1" false false true = some "cleared" := by native_decide

example : ["Sum", "MinValue", "MaxValue"].all (fun operator =>
    validationVerdict (operator ++ "(Packages/Items*/Weight For Key) == 0") "missing" == some (.fired .value) &&
    validationVerdict (operator ++ "(Packages/Items*/Weight For Key) == 0") "P2" false false false true == some (.fired .omission)) := by native_decide

private def partialOutcome (expression : String) (coverage : List RelevantEntityPattern)
    (key : String := "P1") (duplicate : Bool := false) (numericIndex : Bool := false) (header : String := "1") (invalidIndex : Bool := false) : Option (Except OrdinaryRepeatableRuleEvaluationError PartialRuleOutcome) := do
  let sourceModel := if numericIndex then { model with fields := model.fields.map fun field =>
    if field.id == 1 || field.id == 5 then { field with policy := { kind := .number { scale := 0, signed := true } } }
    else field } else model
  let document ← input (if numericIndex then key.replace "P" "" else key) duplicate false invalidIndex false sourceModel header
  let parsed ← (parseText .english ("FieldFilled(Out) And (" ++ expression ++ ")")).toOption
  let condition ← (lowerCondition sourceModel ["Form"] false parsed.body).toOption
  let rule ← (assembleResolvedValidationRule sourceModel condition 6 "PARTIAL_INDEX" .error { parts := [] }).toOption
  pure (rule.evalAddressedPartial document (.partialSet (
    { path := ["Form", "Out"], indices := [.all, .all] } :: coverage)))

private def partialVerdict (expression : String) (coverage : List RelevantEntityPattern)
    (key : String := "P1") (duplicate : Bool := false) (numericIndex : Bool := false) (header : String := "1") (invalidIndex : Bool := false) : Option Verdict := do
  let result ← (← partialOutcome expression coverage key duplicate numericIndex header invalidIndex).toOption
  match result with | .evaluated result => some result.verdict | .skipped => none

private def relevant (path : List String) : RelevantEntityPattern :=
  { path := "Form" :: path, indices := (List.range (path.length + 1)).map fun _ => .all }

private def concreteRow (row : Nat) : RelevantEntityPattern :=
  { path := ["Form", "Packages"], indices := [.all, .concrete row] }

example : ["FieldFilled(Packages/Header For \"P1\")", "[Packages/Header For \"P1\"] == 1",
    "GroupFilled(Packages For \"P1\")"].all (fun expression =>
      partialVerdict expression [relevant ["Packages"]] == some (.fired .value) &&
      partialVerdict expression [concreteRow 1] == some (.fired .value) &&
      partialVerdict expression [relevant ["Packages", "Header"]] == some .unknown) = true := by native_decide

example : partialVerdict "GroupFilled(Packages For \"P1\")" [relevant ["Packages", "Code"]] = some (.fired .value) ∧
    partialVerdict "FieldFilled(Packages/Header For \"P1\")" [relevant ["Packages", "Code"]] = some .unknown := by native_decide

example : ["FieldNotFilled(Packages/Header For \"missing\")", "[Packages/Header For \"missing\"] == 0",
    "GroupNotFilled(Packages For \"missing\")"].all (fun expression =>
      partialVerdict expression [relevant ["Packages"]] == some (.fired .omission) &&
      partialVerdict expression [concreteRow 1, concreteRow 2] == some .unknown &&
      partialVerdict expression [relevant ["Packages", "Code"], concreteRow 1, concreteRow 2] == some .unknown) = true := by native_decide

example : partialVerdict "FieldFilled(Packages/Header For Key)" [relevant ["Packages"]] = some .unknown ∧
    partialVerdict "FieldFilled(Packages/Header For Key)" [relevant ["Packages"], relevant ["Key"]] = some (.fired .value) ∧
    partialVerdict "FieldFilled(Packages/Header For \"P1\")" [concreteRow 1] "P1" true = some (.fired .value) ∧
    partialVerdict "FieldFilled(Packages/Header For \"P1\")" [relevant ["Packages"]] "P1" true = some .unknown := by native_decide

example : [false, true].all (fun numericIndex =>
    let key := if numericIndex then "1" else "P1"
    let missing := if numericIndex then "9" else "missing"
    let selected := "[Packages/Header For \"" ++ key ++ "\"] == 1"
    let absent := "[Packages/Header For \"" ++ missing ++ "\"] == 0"
    partialVerdict selected [relevant ["Packages", "Code"], relevant ["Packages", "Header"]] "P1" false numericIndex == some (.fired .value) &&
    partialVerdict absent [relevant ["Packages", "Code"], relevant ["Packages", "Header"]] "P1" false numericIndex == some (.fired .omission) &&
    partialVerdict absent [concreteRow 1, concreteRow 2, relevant ["Packages", "Header"]] "P1" false numericIndex == some .unknown &&
    partialVerdict "[Packages/Header For Key] == 1" [relevant ["Packages"], relevant ["Key"]] "P1" false numericIndex == some (.fired .value)) = true := by native_decide

example : partialVerdict "[Packages/Header For Key] == 1"
    [relevant ["Packages"], relevant ["Key"]] "bad" false true = some .unknown ∧
    partialVerdict "FieldFilled(Packages/Header For \"P1\")" [relevant ["Packages"]] "P1" false false "bad" = some .unknown ∧
    partialVerdict "FieldNotFilled(Packages/Header For \"P1\")" [relevant ["Packages"]] "P1" false false "" = some (.fired .omission) ∧
    partialVerdict "FieldFilled(Packages/Header For \"P1\")" [relevant ["Packages"]] "P1" false false "1" true = some (.fired .value) ∧
    partialVerdict "FieldNotFilled(Packages/Header For \"missing\")" [relevant ["Packages"]] "P1" false false "1" true = some .unknown := by native_decide

example : partialVerdict "FieldFilled(Out) Or [Packages/Header For Key] == 1" [] = some (.fired .value) ∧
    partialVerdict "[Packages/Header For Key] == 1 Or FieldFilled(Out)" [] = some (.fired .value) := by native_decide

private def partialUnsupported (expression : String) : Bool :=
  match partialOutcome expression [relevant ["Packages"], relevant ["Key"]] with
  | some (.error .unsupportedCondition) => true
  | _ => false

example : partialUnsupported "NumberOfValueInFields(2 In Packages/Items* For Key) == 3" = true := by native_decide

example : partialUnsupported "NumberOfValueInFields(2 In Packages/Items* For Key) == 3 Or FieldFilled(Out)" = true := by native_decide

end A12Kernel.Dm.KeyedExtentLocks
