import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Document
import A12Kernel.Reference.Dm.LowerValidation
import A12Kernel.Reference.Dm.Validate

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

private def dimsModel : FlatModel :=
  { model with fields := model.fields.flatMap fun declaration =>
      if declaration.id == 5 then [
        { id := 7, name := "Width", groupPath := ["Form", "Packages", "Dims"], repeatableScope := [10], policy := { kind := .number { scale := 0, signed := true } } },
        { id := 8, name := "Depth", groupPath := ["Form", "Packages", "Dims"], repeatableScope := [10], policy := { kind := .number { scale := 0, signed := true } } },
        declaration]
      else [declaration] }

private def input (key : String) (duplicate : Bool := false) (bad : Bool := false) (invalidIndex : Bool := false) (emptySecond : Bool := false) (sourceModel : FlatModel := model) (header : String := "1")
    (dims : String × String := ("3", "4")) (out : String := "99") : Option (CheckedDocument sourceModel) := do
  let numericIndex := (sourceModel.lookupUniqueId 1).toOption.any (fun field => field.policy.kind.surfaceKind == .number)
  let package (key : String) (weights : List String) := Lean.Json.mkObj ([
    ("Code", .str key), ("Header", .str header),
    ("Items", .arr (weights.map fun weight => Lean.Json.mkObj [
      ("Weight", .str weight), ("Quantity", .str "2")]).toArray)] ++
    if sourceModel.fields.any (·.id == 7) then
      [("Dims", Lean.Json.mkObj ([("Width", dims.1), ("Depth", dims.2)].filterMap fun (name, value) =>
        if value.isEmpty then none else some (name, .str value)))] else [])
  let data := Lean.Json.mkObj [("Form", Lean.Json.mkObj [
    ("Key", .str key), ("Out", if out.isEmpty then .null else .str out),
    ("Packages", .arr #[package (if numericIndex then "1" else "P1") ["2", if bad then "bad" else "5"], package (if invalidIndex then "" else if duplicate then (if numericIndex then "1" else "P1") else (if numericIndex then "2" else "P2")) (if emptySecond then [] else ["11"])])])]
  let dm : DmModel := { flat := sourceModel, computations := [], rules := [], conditionLanguage := "en_US", refusals := [] }
  let input ← (readDocument dm data).toOption
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } } builtinStringPatternCompiler sourceModel).toOption
  (checkDocument prepared "en_US" input.data).toOption

private def validationVerdict (expression : String) (key : String := "P1") (duplicate : Bool := false) (bad : Bool := false) (invalidIndex : Bool := false) (emptySecond : Bool := false)
    (sourceModel : FlatModel := model) (dims : String × String := ("3", "4")) (out : String := "99") : Option Verdict := do
  let checked ← input key duplicate bad invalidIndex emptySecond sourceModel (dims := dims) (out := out)
  let parsed ← (parseText .english expression).toOption
  let condition ← (lowerCondition sourceModel ["Form"] false parsed.body).toOption
  let verdict ← (condition.core.evalAddressed {
    scalar := { fields := checked.flatContext, groups := GroupPresenceContext.unavailable },
    outer := [], input := .checked checked }).toOption
  pure verdict

private def validation (expression : String) (key : String := "P1") (duplicate : Bool := false)
    (bad : Bool := false) (invalidIndex : Bool := false) : Option Bool :=
  (validationVerdict expression key duplicate bad invalidIndex).map fun
    | .fired _ => true | _ => false

private def computation (operation : String) (guard : String := "FieldFilled(Key)")
    (key : String := "P1") (duplicate : Bool := false) (bad : Bool := false) (invalidIndex : Bool := false) (fallback : Bool := false) (producer : Option (String × String) := none)
    (sourceModel : FlatModel := model) (emptySecond : Bool := false) (header : String := "1") : Option String := do
  let checked ← input key duplicate bad invalidIndex emptySecond sourceModel header
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler sourceModel).toOption
  let lowered ← (lowerComputation sourceModel .english {
    name := "Consumer", group := ["Form"], targetRelPath := "../Out", commonPrecondition := if fallback then none else some guard,
    alternatives := if fallback then [{ precondition := some guard, operation }, { precondition := some "FieldFilled(Key)", operation := "2" }]
      else [{ precondition := none, operation }], errorCodesToSuppress := [] }).toOption
  let producers ← producer.toList.mapM fun (target, operation) =>
    (lowerComputation sourceModel .english {
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

-- A duplicate key leaves no declared slot missing, so `NotAllFieldsFilled` cannot fire; with no
-- matching row the declared extent is missing (q04 of the
-- [semantic-index capture](../../../docs/sources/model-structure-and-declaration-probes.md#src-semantic-index-reads)).
-- The Kernel shows only silence there, so the lock excludes firing rather than choosing unknown.
example : (validationVerdict "NotAllFieldsFilled(Packages/Items*/Weight For Key)" (duplicate := true)).any
      (fun | .fired _ => false | _ => true) = true ∧
    validationVerdict "NotAllFieldsFilled(Packages/Items*/Weight For Key)" "missing" = some (.fired .omission) := by
  native_decide

-- Beside another operand the duplicate still leaves no slot missing, so an empty sibling alone fires
-- the negative quantifier, and a matched row's uninstantiated tail fires it (w02, w03 and q04).
example : (validationVerdict "NotAllFieldsFilled(Out, Packages/Items*/Weight For Key)" (duplicate := true)).any
      (fun | .fired _ => false | _ => true) = true ∧
    validationVerdict "NotAllFieldsFilled(Out, Packages/Items*/Weight For Key)" (duplicate := true) (out := "") =
      some (.fired .omission) ∧
    ["99", ""].all (fun out =>
      (validationVerdict "FieldsNotCollectivelyFilled(Out, Packages/Items*/Weight For Key)" (duplicate := true)
        (out := out)).any (fun | .fired _ => false | _ => true)) = true ∧
    validationVerdict "NotAllFieldsFilled(Packages/Items*/Weight For Key)" "P2" = some (.fired .omission) := by
  native_decide

-- The keyed fixed group behaves alike (v05 of the same capture).
example : ["P1", "missing"].all (fun key =>
      validationVerdict "NotAllFieldsFilled(Packages/Dims For Key)" key (sourceModel := dimsModel) (dims := ("3", "")) ==
        some (.fired .omission)) ∧
    (validationVerdict "NotAllFieldsFilled(Packages/Dims For Key)" (duplicate := true) (sourceModel := dimsModel)
      (dims := ("3", ""))).any (fun | .fired _ => false | _ => true) = true := by native_decide

private def mixedDims : FlatModel :=
  { dimsModel with fields := dimsModel.fields.map fun declaration =>
      if declaration.id == 7 then { declaration with policy := { kind := .number { scale := 0, signed := false } } }
      else declaration }

-- A keyed group may mix signedness: each missing summand takes its polarity from its own declaration,
-- not from the first or any signed sibling (m01 against m06 of the semantic-index capture).
example : validationVerdict "Sum(Packages/Dims For Key) > 0" (sourceModel := mixedDims) (dims := ("", "5")) =
      some (.fired .value) ∧
    validationVerdict "Sum(Packages/Dims For Key) > 0" (sourceModel := mixedDims) (dims := ("5", "")) =
      some (.fired .omission) := by native_decide

/-- A key selecting no package leaves the starred list absent, an open extent like an uninstantiated
tail, so a fired comparison is OMISSION; the matched package's exhausted `Items` stays VALUE. Kernel
calibration: the generated self-validation rows of the retained nested-semantic-index,
selected-message-references and index-text-normalization captures. -/
example : validationVerdict "[Out] != Sum(Packages/Items*/Weight For Key)" "missing" = some (.fired .omission) ∧
    validationVerdict "[Out] != Sum(Packages/Items*/Weight For Key)" "P1" = some (.fired .value) := by
  native_decide

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
    validationVerdict (operator ++ "(Packages/Items*/Weight For Key) == 0") "missing" == some (.fired .omission) &&
    validationVerdict (operator ++ "(Packages/Items*/Weight For Key) == 0") "P2" false false false true == some (.fired .omission)) := by native_decide

private def partialOutcome (expression : String) (coverage : List RelevantEntityPattern)
    (key : String := "P1") (duplicate : Bool := false) (numericIndex : Bool := false) (header : String := "1") (invalidIndex : Bool := false) (emptySecond : Bool := false) (baseModel : FlatModel := model) : Option (Except OrdinaryRepeatableRuleEvaluationError PartialRuleOutcome) := do
  let sourceModel := if numericIndex then { baseModel with fields := baseModel.fields.map fun field =>
    if field.id == 1 || field.id == 5 then { field with policy := { kind := .number { scale := 0, signed := true } } }
    else field } else baseModel
  let document ← input (if numericIndex then key.replace "P" "" else key) duplicate false invalidIndex emptySecond sourceModel header
  let parsed ← (parseText .english ("FieldFilled(Out) And (" ++ expression ++ ")")).toOption
  let condition ← (lowerCondition sourceModel ["Form"] false parsed.body).toOption
  let rule ← (assembleResolvedValidationRule sourceModel condition 6 "PARTIAL_INDEX" .error { parts := [] }).toOption
  pure (rule.evalAddressedPartial document (.partialSet (
    { path := ["Form", "Out"], indices := [.all, .all] } :: coverage)))

private def partialVerdict (expression : String) (coverage : List RelevantEntityPattern)
    (key : String := "P1") (duplicate : Bool := false) (numericIndex : Bool := false) (header : String := "1") (invalidIndex : Bool := false) (emptySecond : Bool := false) (baseModel : FlatModel := model) : Option Verdict := do
  let result ← (← partialOutcome expression coverage key duplicate numericIndex header invalidIndex emptySecond baseModel).toOption
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

example : partialVerdict "SumOfProducts(Packages*/Header,Packages*/Header) == 2"
    [relevant ["Packages"]] = some (.fired .omission) ∧
    partialVerdict "SumOfProducts(Packages*/Header,Packages*/Header) == 2"
      [concreteRow 1, concreteRow 2] = some .unknown ∧
    partialVerdict "SumOfProducts(Packages*/Header,Packages*/Header) == 2"
      [concreteRow 1, concreteRow 2, concreteRow 3] = some (.fired .omission) := by native_decide

example : partialVerdict "SumOfProducts(Packages*/Header,Packages*/Header) == 2 Or FieldFilled(Out)"
    [] = some (.fired .value) := by native_decide

example : partialVerdict "FirstFilledValue(Packages/Items*/Weight For Key) == 2"
    [relevant ["Key"], relevant ["Packages", "Code"], relevant ["Packages", "Items", "Weight"]] = some (.fired .value) ∧
    partialVerdict "FirstFilledValue(Packages/Header For Key,Out) == 1"
      [relevant ["Key"], relevant ["Packages", "Code"], relevant ["Packages", "Header"]] = some (.fired .value) ∧
    partialVerdict "FirstFilledValue(Packages/Items* For Key) == 2"
      [relevant ["Key"], relevant ["Packages", "Code"], relevant ["Packages", "Items", "Weight"]] = some (.fired .value) := by native_decide

example : partialVerdict "FirstFilledValue(Packages/Header For Key,Out) == 99"
    [relevant ["Key"], relevant ["Packages", "Code"], relevant ["Packages", "Header"]] "P1" false false "" = some (.fired .omission) ∧
    partialVerdict "FirstFilledValue(Packages/Header For Key,Out) == 99"
      [relevant ["Key"], relevant ["Packages", "Code"]] = some .unknown ∧
    partialVerdict "FirstFilledValue(Out,Packages/Header For Key) == 99" [] = some (.fired .value) ∧
    partialVerdict "FirstFilledValue(Packages/Items*/Weight For Key,Out) == 99"
      [relevant ["Key"], relevant ["Packages"]] "missing" = some (.fired .omission) ∧
    partialVerdict "FirstFilledValue(Packages/Items*/Weight For Key,Out) == 99"
      [relevant ["Key"], concreteRow 1, concreteRow 2] "missing" = some .unknown := by native_decide

private def partialAggregateFamily (operand : String) (expected : List String)
    (coverage : List RelevantEntityPattern) (key : String := "P1") (baseModel : FlatModel := model) : Bool :=
  (["Sum", "MinValue", "MaxValue", "NumberOfDifferentValues"].zip expected).all fun (operator, value) =>
    partialVerdict (operator ++ "(" ++ operand ++ ") == " ++ value) coverage key (baseModel := baseModel) == some (.fired .value)

example : partialAggregateFamily "Packages/Items*/Weight For Key" ["7", "2", "5", "2"]
    [relevant ["Key"], relevant ["Packages"]] = true ∧
    partialAggregateFamily "Packages/Items* For Key" ["11", "2", "5", "2"]
      [relevant ["Key"], relevant ["Packages"]] = true ∧
    partialAggregateFamily "Packages/Header For Key,Packages/Header For \"P2\"" ["2", "1", "1", "1"]
      [relevant ["Key"], relevant ["Packages"]] = true := by native_decide

example : ["Sum", "MinValue", "MaxValue", "NumberOfDifferentValues"].all (fun operator =>
    partialVerdict (operator ++ "(Packages/Items* For Key) == 11")
      [relevant ["Key"], relevant ["Packages", "Code"], relevant ["Packages", "Items", "Weight"]] == some .unknown &&
    partialVerdict (operator ++ "(Packages/Items*/Weight For Key) == 7")
      [relevant ["Key"], relevant ["Packages", "Items", "Weight"]] == some .unknown) = true := by native_decide

private def concreteItem (package item : Nat) : RelevantEntityPattern :=
  { path := ["Form", "Packages", "Items", "Weight"], indices := [.all, .concrete package, .concrete item, .all] }

private def packageWeights (package : Nat) : RelevantEntityPattern :=
  { path := ["Form", "Packages", "Items", "Weight"], indices := [.all, .concrete package, .all, .all] }

example : (["Sum", "MinValue", "MaxValue", "NumberOfDifferentValues"].zip ["7", "2", "5", "2"]).all (fun (operator, value) =>
    let expression := operator ++ "(Packages/Items*/Weight For Key) == " ++ value
    partialVerdict expression [relevant ["Key"], relevant ["Packages", "Code"], concreteItem 1 1, concreteItem 1 2] == some .unknown &&
    partialVerdict expression [relevant ["Key"], relevant ["Packages", "Code"], packageWeights 1, concreteItem 2 1] == some (.fired .value) &&
    partialVerdict expression [relevant ["Key"], relevant ["Packages", "Code"], packageWeights 1, concreteItem 1 1] == some (.fired .value) &&
    partialVerdict expression [relevant ["Key"], relevant ["Packages"]] "1" false true == some (.fired .value)) = true := by native_decide

example : ["Sum", "MinValue", "MaxValue", "NumberOfDifferentValues"].all (fun operator =>
    partialVerdict (operator ++ "(Packages/Items*/Weight For Key) == 0")
      [relevant ["Key"], relevant ["Packages"]] "missing" == some (.fired .omission) &&
    partialVerdict (operator ++ "(Packages/Items*/Weight For Key) == 0")
      [relevant ["Key"], concreteRow 1, concreteRow 2] "missing" == some .unknown &&
    partialVerdict (operator ++ "(Packages/Items*/Weight For Key) == 0")
      [relevant ["Key"], relevant ["Packages"]] "P1" true == some .unknown &&
    partialVerdict (operator ++ "(Packages/Header For Key,Packages/Header For \"P2\") == 0")
      [relevant ["Key"], relevant ["Packages"]] "P1" false false "bad" == some .unknown) = true := by native_decide

private def aggregateReadback (expression : String) (formalFirst unavailableFirst : Bool) (laterFault : Bool := true) (checkedInput : Bool := false) (injected : Rat := 8) : Option Verdict := do
  let document ← input "P1"
  let parsed ← (parseText .english expression).toOption
  let checked ← (lowerCondition model ["Form"] false parsed.body).toOption
  let .leaf leaf := checked.core | none
  let context : AddressedValidationEvaluationContext model := {
    scalar := { fields := document.flatContext, groups := GroupPresenceContext.unavailable }, outer := []
    input := if checkedInput then .checked document else .partialView document fun row field =>
      if field == 3 && row.lookup 20 == some 1 then
        pure (if unavailableFirst then none else if formalFirst then some malformedCheckedCell
          else some (checkAdmittedRawCell (.parsed (.num injected))))
      else if field == 3 && laterFault then .error (.checkedDocumentRequired ["unreached"])
      else (fun addressed => some addressed.cell) <$> document.addressedCell row field }
  let result ← leaf.evalAddressedPartial? context .full (fun _ => true)
    (fun _ _ => .error (.checkedDocumentRequired [])) none
  result.toOption

example : ["Sum", "MinValue", "MaxValue", "NumberOfDifferentValues"].all (fun operator =>
    let expression := operator ++ "(Packages/Items*/Weight For Key) == 8"
    aggregateReadback expression true false == some .unknown &&
    aggregateReadback expression false true == some .unknown) = true := by native_decide

example : (["Sum", "MinValue", "MaxValue", "NumberOfDifferentValues"].zip ["13", "5", "8", "2"]).all (fun (operator, value) =>
    aggregateReadback (operator ++ "(Packages/Items*/Weight For Key) == " ++ value) false false false == some (.fired .value)) = true := by native_decide

example : ["Sum", "MinValue", "MaxValue", "NumberOfDifferentValues"].all (fun operator =>
    let expression := operator ++ "(Packages/Header For Key,Packages/Header For \"P1\") == 1"
    (validationVerdict expression "missing").isSome &&
    partialVerdict expression [relevant ["Key"], relevant ["Packages"]] "missing" == validationVerdict expression "missing") = true := by native_decide

example : (["Sum", "MinValue", "MaxValue", "NumberOfDifferentValues"].zip ["7", "2", "5", "2"]).all (fun (operator, value) =>
    aggregateReadback (operator ++ "(Packages/Items*/Weight For Key) == " ++ value) false false false true == some (.fired .value)) = true := by native_decide

example : ["Sum", "MinValue", "MaxValue", "NumberOfDifferentValues"].all (fun operator =>
    let expression := operator ++ "(Packages/Items*/Weight For Key) == 0"
    (validationVerdict expression "P2" false false false true).isSome &&
    partialVerdict expression [relevant ["Key"], relevant ["Packages"]] "P2" false false "1" false true ==
      validationVerdict expression "P2" false false false true) = true := by native_decide

example : partialAggregateFamily "Packages/Dims For Key" ["7", "3", "4", "2"]
    [relevant ["Key"], concreteRow 1] (baseModel := dimsModel) = true ∧
    partialAggregateFamily "Packages/Dims For Key" ["7", "3", "4", "2"]
      [relevant ["Key"], relevant ["Packages", "Code"], relevant ["Packages", "Dims"]] (baseModel := dimsModel) = true ∧
    partialVerdict "Sum(Packages/Dims For Key) == 7"
      [relevant ["Key"], relevant ["Packages", "Code"], relevant ["Packages", "Dims", "Width"]] (baseModel := dimsModel) = some .unknown := by native_decide

example : partialVerdict "NumberOfValueInFields(2 In Packages/Items* For Key) == 3"
    [relevant ["Key"], relevant ["Packages"]] = some (.fired .value) ∧
    partialVerdict "NumberOfValueInFields(2 In Packages/Items*/Weight For Key) == 1"
      [relevant ["Key"], relevant ["Packages"]] = some (.fired .value) ∧
    partialVerdict "NumberOfValueInFields(3 In Packages/Dims For Key) == 1"
      [relevant ["Key"], relevant ["Packages"]] (baseModel := dimsModel) = some (.fired .value) := by native_decide

example : partialVerdict "NumberOfValueInFields(2 In Packages/Items*/Weight For Key) == 1"
    [relevant ["Key"], relevant ["Packages", "Code"], concreteItem 1 1, concreteItem 1 2] = some .unknown ∧
    partialVerdict "NumberOfValueInFields(2 In Packages/Items*/Weight For Key) == 1"
      [relevant ["Key"], relevant ["Packages", "Code"], packageWeights 1, concreteItem 2 1] = some (.fired .value) ∧
    partialVerdict "NumberOfValueInFields(2 In Packages/Items*/Weight For Key) == 0"
      [relevant ["Key"], relevant ["Packages"]] "missing" = some (.fired .value) ∧
    partialVerdict "NumberOfValueInFields(2 In Packages/Items*/Weight For Key) == 0"
      [relevant ["Key"], concreteRow 1, concreteRow 2] "missing" = some .unknown ∧
    partialVerdict "NumberOfValueInFields(2 In Packages/Items*/Weight For Key) == 1"
      [relevant ["Key"], relevant ["Packages"]] "1" false true = some (.fired .value) := by native_decide

example : aggregateReadback "NumberOfValueInFields(8 In Packages/Items*/Weight For Key) == 1" false false false = some (.fired .value) ∧
    aggregateReadback "NumberOfValueInFields(8 In Packages/Items*/Weight For Key) == 1" false false = none ∧
    aggregateReadback "NumberOfValueInFields(8 In Packages/Items*/Weight For Key) == 1" true false = some .unknown ∧
    aggregateReadback "NumberOfValueInFields(8 In Packages/Items*/Weight For Key) == 1" false true = some .unknown := by native_decide

example : partialVerdict "NumberOfValueInFields(1 In Key,Out) == 1"
    [relevant ["Key"]] "1" false true = some (.fired .value) ∧
    partialVerdict "NumberOfValueInFields(1 In Key,Out) == 1" [] "1" false true = some .unknown ∧
    partialVerdict "NumberOfValueInFields(2 In Packages/Items* For Key) == 3"
      [relevant ["Key"], concreteRow 1] "P1" true = some (.fired .value) ∧
    partialVerdict "NumberOfValueInFields(2 In Packages/Items* For Key) == 3"
      [relevant ["Key"], relevant ["Packages"]] "P1" true = some .unknown := by native_decide

example : [("AtLeastOneFieldValueIncludedInValueList", Verdict.fired .value),
    ("NoFieldValueIncludedInValueList", .notFired), ("NotAllFieldValuesIncludedInValueList", .fired .value)].all
    (fun (operator, expected) => partialVerdict (operator ++ "(Packages/Items*/Weight For Key In Packages/Header For Key)")
      [relevant ["Key"], relevant ["Packages"]] (header := "2") == some expected) = true := by native_decide

example : partialVerdict "AtLeastOneFieldValueIncludedInValueList(Packages/Items*/Weight For Key In Packages/Header For Key)"
    [relevant ["Key"], relevant ["Packages", "Code"], relevant ["Packages", "Header"], concreteItem 1 1]
    (header := "2") = some (.fired .value) ∧
    partialVerdict "NoFieldValueIncludedInValueList(Packages/Items*/Weight For Key In Packages/Header For Key)"
      [relevant ["Key"], relevant ["Packages", "Code"], relevant ["Packages", "Header"], concreteItem 1 1]
      (header := "2") = some .unknown ∧
    partialVerdict "NotAllFieldValuesIncludedInValueList(Packages/Items*/Weight For Key In Packages/Header For Key)"
      [relevant ["Key"], relevant ["Packages", "Code"], relevant ["Packages", "Header"], concreteItem 1 2]
      (header := "2") = some (.fired .value) := by native_decide

example : [("AtLeastOneFieldValueIncludedInValueList", Verdict.notFired),
    ("NoFieldValueIncludedInValueList", .fired .value), ("NotAllFieldValuesIncludedInValueList", .fired .value)].all
    (fun (operator, expected) => validationVerdict (operator ++ "(Packages/Items*/Weight For Key In Packages/Header For Key)")
      == some expected) = true := by native_decide

example : [("AtLeastOneFieldValueIncludedInValueList", Verdict.fired .value),
    ("NoFieldValueIncludedInValueList", .unknown), ("NotAllFieldValuesIncludedInValueList", .unknown)].all
    (fun (operator, expected) => partialVerdict (operator ++ "(Packages/Header For Key In Packages/Items*/Weight For Key)")
      [relevant ["Key"], relevant ["Packages", "Code"], relevant ["Packages", "Header"], concreteItem 1 1]
      (header := "2") == some expected) = true := by native_decide

example : partialVerdict "NoFieldValueIncludedInValueList(Packages/Items*/Weight For Key In Out)"
    [relevant ["Key"], relevant ["Packages"]] "missing" = some (.fired .omission) ∧
    partialVerdict "NoFieldValueIncludedInValueList(Packages/Items*/Weight For Key In Out)"
      [relevant ["Key"], relevant ["Packages", "Code"]] "missing" = some .unknown ∧
    partialVerdict "NoFieldValueIncludedInValueList(Packages/Header For Key In Out)"
      [relevant ["Key"], relevant ["Packages"]] "missing" = some (.fired .omission) ∧
    partialVerdict "AtLeastOneFieldValueIncludedInValueList(Packages/Dims For Key In Packages/Header For Key)"
      [relevant ["Key"], relevant ["Packages"]] (header := "3") (baseModel := dimsModel) = some (.fired .value) := by native_decide

example : let expression := "NoFieldValueIncludedInValueList(Packages/Items*/Weight For Key In Packages/Items*/Quantity For Key)"
    aggregateReadback expression false false false = some (.fired .value) ∧
    aggregateReadback expression true false false = some .unknown ∧
    aggregateReadback expression false true false = some .unknown ∧
    aggregateReadback expression false false false true = some .notFired := by native_decide

example : validationVerdict "FieldValuesNotUnique(Packages/Items* For Key)" = some (.fired .value) ∧
    validationVerdict "FieldValuesNotUnique(Packages/Items*/Weight For Key)" = some .notFired ∧
    validationVerdict "FieldValuesNotUnique(Packages/Items* For Key)" "missing" = some .notFired := by native_decide

example : partialVerdict "FieldValuesNotUnique(Packages/Items* For Key)"
    [relevant ["Key"], relevant ["Packages"]] = some (.fired .value) ∧
    partialVerdict "FieldValuesNotUnique(Packages/Items* For Key)"
      [relevant ["Key"], relevant ["Packages", "Code"], concreteItem 1 1, concreteItem 1 2] = some .notFired ∧
    partialVerdict "FieldValuesNotUnique(Packages/Items*/Quantity For Key)"
      [relevant ["Key"], relevant ["Packages", "Code"],
       { concreteItem 1 1 with path := ["Form", "Packages", "Items", "Quantity"] },
       { concreteItem 1 2 with path := ["Form", "Packages", "Items", "Quantity"] }] = some (.fired .value) := by native_decide

example : let expression := "FieldValuesNotUnique(Packages/Items*/Weight For Key)"
    aggregateReadback expression false false false (injected := 5) = some (.fired .value) ∧
    aggregateReadback expression true false false (injected := 5) = some .notFired ∧
    aggregateReadback expression false true false (injected := 5) = some .notFired ∧
    aggregateReadback expression false false false true (injected := 5) = some .notFired := by native_decide

example : partialVerdict "FieldValuesNotUnique(Packages/Items* For Key)"
    [relevant ["Key"], relevant ["Packages"]] "1" false true = some (.fired .value) ∧
    partialVerdict "FieldValuesNotUnique(Packages/Items* For Key)"
      [relevant ["Key"], concreteRow 1] "P1" true = some (.fired .value) ∧
    partialVerdict "FieldValuesNotUnique(Packages/Items* For Key)"
      [relevant ["Key"], relevant ["Packages"]] "P1" true = some .notFired ∧
    partialVerdict "FieldValuesNotUnique(Packages/Items* For Key)"
      [relevant ["Packages"]] = some .notFired := by native_decide

example : computation "1" "FieldValuesNotUnique(Packages/Items* For Key)" = some "value 1" ∧
    computation "1" "FieldValuesNotUnique(Packages/Items*/Quantity For Key)" = some "value 1" ∧
    computation "1" "FieldValuesNotUnique(Packages/Items*/Weight For Key)" = some "cleared" ∧
    computation "1" "FieldValuesNotUnique(Packages/Dims For Key)" (sourceModel := dimsModel) = some "cleared" ∧
    computation "1" "FieldValuesNotUnique(Packages/Header For Key,Packages/Dims/Width For Key)"
      (sourceModel := dimsModel) (header := "3") = some "value 1" := by native_decide

example : [("AtLeastOneFieldValueIncludedInValueList", "value 1"),
    ("NoFieldValueIncludedInValueList", "cleared"), ("NotAllFieldValuesIncludedInValueList", "value 1")].all
    (fun (operator, expected) => ["Packages/Items*/Weight For Key", "Packages/Items* For Key"].all fun fields =>
      computation "1" (operator ++ "(" ++ fields ++ " In Packages/Header For Key)")
        (header := "2") == some expected) = true := by native_decide

example : [("AtLeastOneFieldValueIncludedInValueList", "value 1"),
    ("NoFieldValueIncludedInValueList", "cleared"), ("NotAllFieldValuesIncludedInValueList", "value 1")].all
    (fun (operator, expected) => computation "1" (operator ++ "(Packages/Dims For Key In Packages/Header For Key)")
      (sourceModel := dimsModel) (header := "3") == some expected) = true := by native_decide

example : [("AtLeastOneFieldValueIncludedInValueList", "value 1"),
    ("NoFieldValueIncludedInValueList", "cleared"),
    ("NotAllFieldValuesIncludedInValueList", "cleared")].all
    (fun (operator, present) =>
      computation "1" (operator ++ "(Packages/Header For Key In Packages/Items*/Quantity For Key)")
        (header := "2") == some present &&
      computation "1" (operator ++ "(Packages/Items*/Weight For Key In Packages/Header For Key)")
        (key := "P2") (emptySecond := true) ==
        some (if operator == "NoFieldValueIncludedInValueList" then "value 1" else "cleared") &&
      computation "1" (operator ++ "(Packages/Header For Key In Packages/Items*/Quantity For Key)")
        (header := "") == some (if operator == "NoFieldValueIncludedInValueList" then "value 1" else "cleared")) = true := by native_decide

example : [("AtLeastOneFieldValueIncludedInValueList", "value 1"),
    ("NoFieldValueIncludedInValueList", "cleared"), ("NotAllFieldValuesIncludedInValueList", "cleared")].all
    (fun (operator, expected) =>
      computation "1" (operator ++ "(Packages/Items*/Weight For Key In Packages/Header For Key)")
        (bad := true) (header := "2") == some expected &&
      computation "1" (operator ++ "(Packages/Header For Key In Packages/Items*/Weight For Key)")
        (bad := true) (header := "2") == some "cleared") = true := by native_decide

example : let quantityFirst := { model with fields := model.fields.filter (·.id != 3) ++ model.fields.filter (·.id == 3) }
    computation "1" "FieldValuesNotUnique(Packages/Items* For Key)" (bad := true) = some "cleared" ∧
    computation "1" "FieldValuesNotUnique(Packages/Items* For Key)" (bad := true)
      (sourceModel := quantityFirst) = some "value 1" := by native_decide

example : ["FieldValuesNotUnique(Packages/Items* For Key)",
    "AtLeastOneFieldValueIncludedInValueList(Packages/Items*/Weight For Key In Packages/Header For Key)"].all
    (fun guard => computation "1" guard (key := "missing") (header := "2") (fallback := true) == some "value 2" &&
      computation "1" guard (duplicate := true) (header := "2") (fallback := true) == some "cleared" &&
      computation "1" guard (invalidIndex := true) (header := "2") (fallback := true) == some "cleared" &&
      computation "1" guard (key := "missing") (header := "2")
        (producer := some ("Key", "\"P1\"")) == some "value 1") = true := by native_decide

example : computation "1" "FieldValuesNotUnique(Packages/Dims For Key)"
      (sourceModel := dimsModel) (producer := some ("Packages/Dims/Depth", "3")) = some "value 1" ∧
    computation "1" "FieldValuesNotUnique(Packages/Header For Key,Packages/Dims/Width For Key)"
      (sourceModel := dimsModel) (producer := some ("Packages/Header", "3")) = some "value 1" ∧
    computation "1" "NoFieldValueIncludedInValueList(Packages/Items*/Weight For Key In Packages/Header For Key)"
      (producer := some ("Packages/Items/Weight", "1")) = some "cleared" ∧
    computation "1" "AtLeastOneFieldValueIncludedInValueList(Packages/Header For Key In Packages/Items*/Weight For Key)"
      (producer := some ("Packages/Items/Weight", "1")) = some "value 1" := by native_decide

example : let numericIndex := { model with fields := model.fields.map fun field =>
      if field.id == 1 || field.id == 5 then { field with policy := { kind := .number { scale := 0, signed := true } } } else field }
    computation "1" "FieldValuesNotUnique(Packages/Items* For Key)" (key := "01") (sourceModel := numericIndex) = some "value 1" ∧
    computation "1" "AtLeastOneFieldValueIncludedInValueList(Packages/Items*/Weight For Key In Packages/Header For Key)"
      (key := "01") (sourceModel := numericIndex) (header := "2") = some "value 1" := by native_decide

example : ["FieldValuesNotUnique(Packages/Items* For Key)",
    "NotAllFieldValuesIncludedInValueList(Packages/Items*/Weight For Key In Packages/Header For Key)",
    "AtLeastOneFieldValueIncludedInValueList(Packages/Header For Key In Packages/Items*/Weight For Key)"].all
    (fun guard => computation "1" guard (bad := true) (header := "2") (fallback := true) == some "cleared") = true := by native_decide

private inductive BoundListDeclaration where
  | row
  | ancestor

private def boundListVerdicts (kind : FieldKind) (operator : String) (literal : Bool := false)
    (reverse : Bool := false) (partialScope : Option ValidationRelevanceScope := none)
    (outsideError : Bool := false) (unselected : Bool := false)
    (declaration : BoundListDeclaration := .row) (composed : Bool := false) : Option (List Verdict) := do
  let sourceModel : FlatModel := {
    model with
    fields := model.fields.map fun field =>
      if field.id == 2 || field.id == 3 || field.id == 4 then
        { field with
          policy := { kind := kind }
          enumeration := if kind == .enumeration then some { storedTokens := ["2", "5", "11"] } else none }
      else field
    repeatableGroups := model.repeatableGroups.map fun group => { group with repeatability := some 2 } }
  let dm : DmModel := { flat := sourceModel, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let package := fun (code : String) (weights : List String) => Lean.Json.mkObj [
    ("Code", .str code), ("Header", .str (if code == "P1" then "2" else "11")), ("Items", .arr (weights.map fun value =>
      Lean.Json.mkObj [("Weight", .str value), ("Quantity", .str "2")]).toArray)]
  let data ← (readDocument dm (Lean.Json.mkObj [("Form", Lean.Json.mkObj [
    ("Key", .str "P1"), ("Out", .str "99"), ("Packages", .arr #[package "P1" ["2", "5"], package "P2" ["11", "2"]])])])).toOption
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } } builtinStringPatternCompiler sourceModel).toOption
  let document ← (checkDocument prepared "en_US" data.data).toOption
  let (ruleGroup, rowPrefix) := match declaration with
    | .row => (["Form", "Packages", "Items"], "")
    | .ancestor => (["Form"], "Packages/Items/")
  let selected := if unselected then rowPrefix ++ "Quantity" else "/Form/Packages/Header For \"P1\""
  let subject := if reverse then selected else rowPrefix ++ "Weight"
  let members := if literal then "\"2\"" else if reverse then rowPrefix ++ "Weight" else selected
  let rule ← (checkRule dm .english {
    group := ruleGroup, name := "BoundList", errorCode := "BOUND_LIST"
    errorEntityRelPath := if outsideError then "/Form/Out" else "../" ++ rowPrefix ++ "Weight"
    -- The filled error field guards the row level, where a bare `No…` quantifier and one whose
    -- subject reads outside the row are refused
    -- ([checkpoint](../../../docs/sources/model-structure-and-declaration-probes.md#src-iteration-guard-k04)
    -- rows `u19`–`u24`), without changing any verdict.
    condition := "FieldFilled(" ++ rowPrefix ++ "Weight) And " ++
      operator ++ "(" ++ subject ++ " In " ++ members ++ ")" ++
      (if composed then " And FieldFilled(Key)" else ""), severity := "ERROR" }).toOption
  if let some scope := partialScope then
    match ← (rule.evalOrdinaryRepeatablePartial document scope).toOption with
    | .skipped => return []
    | .evaluated rows => return rows.filterMap fun (_, result) =>
        match result with | .skipped => none | .evaluated outcome => some outcome.verdict
  pure ((← (rule.evalOrdinaryRepeatableFull document).toOption).map (·.2.verdict))

example : [FieldKind.number { scale := 0, signed := true }, .string, .enumeration].all (fun kind =>
    ["AtLeastOneFieldValueIncludedInValueList", "NoFieldValueIncludedInValueList", "NotAllFieldValuesIncludedInValueList"].all fun operator =>
      [false, true].all fun reverse =>
        let expected := if operator == "AtLeastOneFieldValueIncludedInValueList" then
            [Verdict.fired .value, .notFired, .notFired, .fired .value]
          else [.notFired, .fired .value, .fired .value, .notFired]
        boundListVerdicts kind operator false reverse == some expected &&
        boundListVerdicts kind operator false reverse (some .full) == some expected &&
        (boundListVerdicts kind operator false reverse none true).isNone) = true := by native_decide

example : [FieldKind.string, .enumeration].all (fun kind =>
    ["AtLeastOneFieldValueIncludedInValueList", "NoFieldValueIncludedInValueList", "NotAllFieldValuesIncludedInValueList"].all fun operator =>
      let expected := if operator == "AtLeastOneFieldValueIncludedInValueList" then
          [Verdict.fired .value, .notFired, .notFired, .fired .value]
        else [.notFired, .fired .value, .fired .value, .notFired]
      boundListVerdicts kind operator true == some expected &&
      boundListVerdicts kind operator true false (some .full) == some expected) = true := by native_decide

example : [FieldKind.number { scale := 0, signed := true }, .string, .enumeration].all (fun kind =>
    boundListVerdicts kind "AtLeastOneFieldValueIncludedInValueList" false false none false true ==
      some [.fired .value, .notFired, .notFired, .fired .value] &&
    [1, 2].all fun child =>
      let scope := ValidationRelevanceScope.partialSet [
        RelevantEntityPattern.allInstances ["Form", "Packages", "Code"],
        RelevantEntityPattern.allInstances ["Form", "Packages", "Header"],
        { path := ["Form", "Packages", "Items", "Weight"],
          indices := [.concrete 1, .concrete 1, .concrete child, .concrete 1] }]
      boundListVerdicts kind "AtLeastOneFieldValueIncludedInValueList" false false (some scope) ==
        some [if child == 1 then .fired .value else .notFired]) = true := by native_decide

private def boundAncestorMatrix (kind : FieldKind) : Bool :=
    ["AtLeastOneFieldValueIncludedInValueList", "NoFieldValueIncludedInValueList", "NotAllFieldValuesIncludedInValueList"].all fun operator =>
      [none, some ValidationRelevanceScope.full].all fun scope =>
        let expected := if operator == "AtLeastOneFieldValueIncludedInValueList" then
            [Verdict.fired .value, .notFired, .notFired, .fired .value]
          else [.notFired, .fired .value, .fired .value, .notFired]
        boundListVerdicts kind operator (partialScope := scope) (unselected := true)
          (declaration := .ancestor) == some expected &&
        boundListVerdicts kind operator (partialScope := scope) (unselected := true)
          (declaration := .ancestor) (composed := true) == some expected &&
        (boundListVerdicts kind operator (partialScope := scope) (outsideError := true)
          (unselected := true) (declaration := .ancestor)).isNone &&
        (kind == .number { scale := 0, signed := true } ||
          boundListVerdicts kind operator (literal := true) (partialScope := scope)
            (declaration := .ancestor) == some expected &&
          boundListVerdicts kind operator (literal := true) (partialScope := scope)
            (declaration := .ancestor) (composed := true) == some expected)

example : boundAncestorMatrix (.number { scale := 0, signed := true }) = true := by native_decide
example : boundAncestorMatrix .string = true := by native_decide
example : boundAncestorMatrix .enumeration = true := by native_decide

end A12Kernel.Dm.KeyedExtentLocks
