import A12Kernel.Reference.Dm.Document
import A12Kernel.Reference.Dm.LowerValidation
import A12Kernel.Reference.Dm.Validate

namespace A12Kernel.Dm.PartialFieldListLocks

private def model : FlatModel := {
  fields := [
    { id := 1, name := "Id", groupPath := ["Form", "Parents"], repeatableScope := [10], policy := { kind := .string } },
    { id := 2, name := "N", groupPath := ["Form", "Parents", "Rows"], repeatableScope := [10,20], policy := { kind := .number { scale := 0, signed := true } } },
    { id := 3, name := "M", groupPath := ["Form", "Parents", "Rows"], repeatableScope := [10,20], policy := { kind := .number { scale := 0, signed := true } } },
    { id := 4, name := "Key", groupPath := ["Form"], policy := { kind := .string } },
    { id := 5, name := "Anchor", groupPath := ["Form"], policy := { kind := .string } },
    { id := 6, name := "Label", groupPath := ["Form", "Parents"], repeatableScope := [10], policy := { kind := .string } },
    { id := 7, name := "Spare", groupPath := ["Form"], policy := { kind := .string } },
    { id := 8, name := "Fallback", groupPath := ["Form"], policy := { kind := .number { scale := 0, signed := true } } }]
  repeatableGroups := [
    { level := 10, path := ["Form", "Parents"], repeatability := some 3, indexField := some 1 },
    { level := 20, path := ["Form", "Parents", "Rows"], repeatability := some 3 }] }

private def input (values : List String) (sourceModel : FlatModel := model)
    (fallback : String := "9") : Option (CheckedDocument sourceModel) := do
  let parent (key : String) (rows : List String) := Lean.Json.mkObj [
    ("Id", .str key), ("Label", .str (if key == "A" then "filled" else "")),
    ("Rows", .arr (rows.map fun n => Lean.Json.mkObj [("N", .str n)]).toArray)]
  let data := Lean.Json.mkObj [("Form", Lean.Json.mkObj [
    ("Key", .str "A"), ("Anchor", .str "ready"), ("Fallback", .str fallback),
    ("Parents", .arr #[parent "A" values, parent "B" [""]])])]
  let dm : DmModel := { flat := sourceModel, computations := [], rules := [], conditionLanguage := "en_US", refusals := [] }
  let parsed ← (readDocument dm data).toOption
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } } builtinStringPatternCompiler sourceModel).toOption
  (checkDocument prepared "en_US" parsed.data).toOption

private def relevant (path : List String) (indices : List RelevanceIndex := []) : RelevantEntityPattern :=
  { path := "Form" :: path, indices := if indices.isEmpty then path.map (fun _ => .all) ++ [.all] else indices }

private def slot (parent row : RelevanceIndex) : RelevantEntityPattern :=
  relevant ["Parents", "Rows", "N"] [.all, parent, row, .all]

private def verdict (expression : String) (values : List String)
    (coverage : List RelevantEntityPattern) (sourceModel : FlatModel := model)
    (fallback : String := "9") : Option Verdict := do
  let document ← input values sourceModel fallback
  let parsed ← (parseText .english ("FieldFilled(Anchor) And (" ++ expression ++ ")")).toOption
  let condition ← (lowerCondition sourceModel ["Form"] false parsed.body).toOption
  let rule ← (assembleResolvedValidationRule sourceModel condition 5 "PARTIAL_FILL" .error { parts := [] }).toOption
  let result ← (rule.evalAddressedPartial document (.partialSet (
    [relevant ["Anchor"], relevant ["Key"], relevant ["Spare"], relevant ["Fallback"], relevant ["Parents", "Id"]] ++ coverage))).toOption
  match result with
  | .evaluated result => pure result.verdict
  | .skipped => none

private def fires (expression : String) (values : List String)
    (coverage : List RelevantEntityPattern) : Option Bool :=
  (verdict expression values coverage).map fun | .fired _ => true | _ => false

private def allFields := "Parents*/Rows*/N"
private def selectedFields := "Parents/Rows*/N For Key"
private def storedSlots := [slot (.concrete 1) (.concrete 1), slot (.concrete 1) (.concrete 2)]

-- KF527's committed differential pins these fired-code distinctions independently of polarity.
example : fires ("AtLeastOneFieldFilled(" ++ allFields ++ ")") ["2", "5"] [] = some false ∧
    fires ("AtLeastOneFieldFilled(" ++ selectedFields ++ ")") ["2", "5"] storedSlots = some true ∧
    fires ("MoreThanOneFieldFilled(" ++ selectedFields ++ ")") ["2", "5"] storedSlots = some true := by native_decide

example : fires ("NoFieldFilled(" ++ allFields ++ ")") ["", ""]
      [slot (.concrete 1) .all, slot (.concrete 2) .all] = some false ∧
    fires ("NoFieldFilled(" ++ selectedFields ++ ")") ["", ""] [slot (.concrete 1) .all] = some true ∧
    fires ("NotAllFieldsFilled(" ++ allFields ++ ")") ["", ""] [slot (.concrete 1) .all] = some true := by native_decide

example : fires ("NotAllFieldsFilled(" ++ selectedFields ++ ")") ["2", "5"] storedSlots = some false ∧
    fires ("NotAllFieldsFilled(" ++ selectedFields ++ ")") ["2", "5"] [slot (.concrete 1) (.concrete 3)] = some true ∧
    fires ("AllFieldsFilled(" ++ selectedFields ++ ")") ["2", "5", "1"] storedSlots = some false ∧
    fires ("AllFieldsFilled(" ++ selectedFields ++ ")") ["2", "5", "1"]
      (storedSlots ++ [slot (.concrete 1) (.concrete 3)]) = some true := by native_decide

example : fires "NoFieldFilled(Parents/Rows*/N For \"absent\")" ["", ""]
      [slot .all (.concrete 1), slot .all (.concrete 2), slot .all (.concrete 3)] = some true := by native_decide

example : fires ("FirstFilledValue(" ++ allFields ++ ") < 100") ["", ""]
      [slot (.concrete 1) .all, slot (.concrete 2) .all] = some false ∧
    fires ("FirstFilledValue(" ++ selectedFields ++ ") < 100") ["", ""]
      [slot (.concrete 1) .all, slot (.concrete 2) .all] = some true ∧
    fires ("FirstFilledValue(" ++ selectedFields ++ ") < 100") ["", ""]
      [slot .all (.concrete 1), slot .all (.concrete 2)] = some false ∧
    fires ("FirstFilledValue(" ++ selectedFields ++ ") < 100") ["", ""]
      [slot .all (.concrete 1), slot .all (.concrete 2), slot .all (.concrete 3)] = some true := by native_decide

example : fires "FirstFilledValue(Parents/Rows*/N For \"absent\") < 100" ["2", "5"]
      [slot .all (.concrete 1), slot .all (.concrete 2), slot .all (.concrete 3)] = some true ∧
    fires ("FirstFilledValue(" ++ selectedFields ++ ") == 5") ["", "5"] [slot (.concrete 1) (.concrete 2)] = some false ∧
    verdict ("FirstFilledValue(" ++ selectedFields ++ ") == 5") ["", "5"] storedSlots = some (.fired .omission) ∧
    verdict ("FirstFilledValue(" ++ selectedFields ++ ") == 2") ["2", "bad"] [slot (.concrete 1) (.concrete 1)] = some (.fired .value) := by native_decide

private def operators := ["AllFieldsFilled", "NoFieldFilled", "AtLeastOneFieldFilled",
  "MoreThanOneFieldFilled", "NotAllFieldsFilled", "NotExactlyOneFieldFilled", "FieldsNotCollectivelyFilled"]

private def results (operand : String) (values : List String) (coverage : List RelevantEntityPattern) :=
  operators.map fun operator => fires (operator ++ "(" ++ operand ++ ")") values coverage

example : results selectedFields ["2", "5"] storedSlots =
    [some false, some false, some true, some true, some false, some true, some false] ∧
    results selectedFields ["2", "5"] [slot (.concrete 1) .all] =
    [some false, some false, some true, some true, some true, some true, some true] := by native_decide

example : results "Parents/Rows* For Key" ["2", "5"] [relevant ["Parents", "Rows"]] =
    [some false, some false, some true, some true, some true, some true, some true] ∧
    results "Parents*/Rows*" ["", ""] [relevant ["Parents", "Rows"]] =
    [some false, some true, some false, some false, some true, some true, some false] := by native_decide

example : fires "NoFieldFilled(Parents/Rows*/N For \"absent\")" ["2", "5"]
      ((List.range 3).flatMap fun parent => (List.range 3).map fun row => slot (.concrete (parent + 1)) (.concrete (row + 1))) = some false ∧
    fires "NotAllFieldsFilled(Parents/Rows*/N For \"absent\")" ["2", "5"] [slot .all (.concrete 3)] = some true ∧
    fires "NoFieldFilled(Parents/Rows*/N For \"absent\")" ["2", "5"] [slot .all (.concrete 3)] = some false := by native_decide

example : verdict ("AtLeastOneFieldFilled(" ++ selectedFields ++ ")") ["bad", "5"] storedSlots = some (.fired .value) ∧
    verdict ("NotAllFieldsFilled(" ++ selectedFields ++ ")") ["bad", "5"] [slot (.concrete 1) (.concrete 1)] = some .unknown ∧
    verdict ("NotAllFieldsFilled(" ++ selectedFields ++ ")") ["bad", "5"] [slot (.concrete 1) (.concrete 3)] = some (.fired .omission) := by native_decide

example : fires ("Sum(" ++ selectedFields ++ ") == 7") ["2", "5"]
      (storedSlots ++ [slot (.concrete 1) (.concrete 3)]) = some false ∧
    fires ("Sum(" ++ selectedFields ++ ") == 7") ["2", "5"] [slot (.concrete 1) .all] = some true := by native_decide

private def partialRead (operator : FieldFillQuantifier) (unavailable : Bool) : Option Verdict := do
  let document ← input ["", ""]
  let declaration ← model.fields.find? (·.id == 2)
  let source : CheckedFieldFillList model := { operands := [.field declaration] }
  (source.evaluatePartialFill operator document
    (.partialSet [slot (.concrete 1) (.concrete 3)]) [(10,1),(20,3)]
    (fun row field => if unavailable then pure none else
      some <$> document.checkedCellWithRead document.readDeclared row field)).toOption

example : partialRead .noFieldFilled false = some (.fired .omission) ∧
    partialRead .notAllFieldsFilled false = some (.fired .omission) ∧
    partialRead .noFieldFilled true = some .unknown ∧
    partialRead .notAllFieldsFilled true = some .unknown := by native_decide

private def labelAt (row : Nat) := relevant ["Parents", "Label"] [.all, .concrete row, .all]

example : fires "AtLeastOneFieldFilled(Parents/Label For Key, Spare)" [] [labelAt 1] = some true ∧
    fires "AtLeastOneFieldFilled(Parents/Label For Key, Spare)" [] [labelAt 2] = some false ∧
    fires "NoFieldFilled(Parents/Label For \"B\", Spare)" [] [labelAt 2] = some true ∧
    fires "NoFieldFilled(Parents/Label For \"B\", Spare)" [] [labelAt 1] = some false := by native_decide

private def boundDirect (row covered : Nat) (values : List String := ["2", ""]) : Option Bool := do
  let document ← input values
  let parsed ← (parseText .english "FieldNotFilled(M) And AtLeastOneFieldFilled(N, M)").toOption
  let condition ← (lowerCondition model ["Form", "Parents", "Rows"] false parsed.body).toOption
  let rule ← (assembleResolvedValidationRule model condition 3 "BOUND_FILL" .error { parts := [] }).toOption
  let (_, result) ← (rule.evalOrdinaryRepeatablePartialAt document
    (.partialSet [relevant ["Parents", "Rows", "M"], slot (.concrete 1) (.concrete covered)])
    [(10,1),(20,row)]).toOption
  match result with
  | .evaluated result => pure (match result.verdict with | .fired _ => true | _ => false)
  | .skipped => none

example : boundDirect 1 1 = some true ∧ boundDirect 1 2 = some false ∧
    boundDirect 2 2 = some false ∧ boundDirect 2 1 = some false ∧
    boundDirect 2 2 ["", "2"] = some true ∧ boundDirect 2 1 ["", "2"] = some false := by native_decide

private def textModel : FlatModel := { model with fields := model.fields.map fun field =>
  if field.id == 2 || field.id == 3 || field.id == 8 then { field with policy := { kind := .string } } else field }

private def booleanModel : FlatModel := { model with fields := model.fields.map fun field =>
  if field.id == 2 || field.id == 3 || field.id == 8 then { field with policy := { kind := .boolean } } else field }

example : verdict "FirstFilledValue(Parents/Rows*/N For Key, Fallback) == \"head\"" ["head", ""]
      [slot (.concrete 1) (.concrete 1)] textModel "tail" = some (.fired .value) ∧
    verdict "FirstFilledValue(Parents/Rows*/N For Key, Fallback) == True" ["true", ""]
      [slot (.concrete 1) (.concrete 1)] booleanModel "true" = some (.fired .value) := by native_decide

example : verdict "FirstFilledValue(Parents/Rows*/N For Key, Fallback) == \"tail\"" ["", ""]
      storedSlots textModel "tail" = some .unknown ∧
    verdict "FirstFilledValue(Parents/Rows*/N For Key, Fallback) == \"tail\"" ["", ""]
      [slot (.concrete 1) .all] textModel "tail" = some (.fired .omission) ∧
    verdict "FirstFilledValue(Parents/Rows*/N For Key, Fallback) == True" ["", ""]
      storedSlots booleanModel "true" = some .unknown ∧
    verdict "FirstFilledValue(Parents/Rows*/N For Key, Fallback) == True" ["", ""]
      [slot (.concrete 1) .all] booleanModel "true" = some (.fired .omission) := by native_decide

private def withPayload (prototype : FlatFieldDecl) : FlatModel := { model with
  timeZoneId := "UTC", baseYear := some 2024,
  fields := model.fields.map fun field =>
    if field.id == 2 || field.id == 3 || field.id == 8 then
      { prototype with
        id := field.id, name := field.name, groupPath := field.groupPath,
        repeatableScope := field.repeatableScope }
    else field }

private def profiles : List (FlatModel × String) := [
  (model, "9"), (textModel, "tail"), (booleanModel, "true"),
  (withPayload {
    id := 0, groupPath := ["Form"], name := "Payload", policy := { kind := .enumeration },
    enumeration := some { storedTokens := ["head", "tail"] } }, "tail"),
  (withPayload {
    id := 0, groupPath := ["Form"], name := "Payload", policy := { kind := .temporal .date .fullDate },
    temporalTargetPolicy := some { format := "yyyy-MM-dd" } }, "2024-01-01"),
  (withPayload {
    id := 0, groupPath := ["Form"], name := "Payload", policy := { kind := .temporal .time .time },
    temporalTargetPolicy := some { format := "HH:mm:ss" } }, "12:30:00"),
  (withPayload {
    id := 0, groupPath := ["Form"], name := "Payload", policy := { kind := .temporal .dateTime .now },
    temporalTargetPolicy := some { format := "yyyy-MM-dd'T'HH:mm:ss" } }, "2024-01-01T12:30:00"),
  (withPayload {
    id := 0, groupPath := ["Form"], name := "Payload", policy := { kind := .dateRange },
    dateRangePolicy := some { format := "yyyy-MM-dd", separator := "/" } }, "2024-01-01/2024-02-01")]

example : profiles.all (fun (profile, payload) =>
    verdict "FirstFilledValue(Parents/Rows* For Key, Fallback) == [Fallback]" ["", ""]
      [relevant ["Parents", "Rows"] [.all, .concrete 1, .all]] profile payload == some (.fired .omission) &&
    verdict "FirstFilledValue(Parents/Rows* For Key, Fallback) == [Fallback]" ["", ""]
      [relevant ["Parents", "Rows"] [.all, .concrete 1, .concrete 1],
       relevant ["Parents", "Rows"] [.all, .concrete 1, .concrete 2]] profile payload == some .unknown) := by native_decide

example : profiles.all (fun (profile, payload) =>
    verdict "FirstFilledValue(Parents*/Rows*/N, Fallback) == [Fallback]" ["", ""]
      [slot (.concrete 1) .all, slot (.concrete 2) .all] profile payload == some .unknown &&
    verdict "FirstFilledValue(Parents*/Rows*/N, Fallback) == [Fallback]" ["", ""]
      [slot .all .all] profile payload == some (.fired .omission) &&
    verdict "FirstFilledValue(Parents/Rows*/N For \"absent\", Fallback) == [Fallback]" [payload, payload]
      [slot .all (.concrete 1), slot .all (.concrete 2), slot .all (.concrete 3)] profile payload == some (.fired .omission)) := by native_decide

example : profiles.all (fun (profile, payload) =>
    verdict "FirstFilledValue(Parents/Rows*/N For Key, Fallback) == [Fallback]" [payload, ""]
      [slot (.concrete 1) (.concrete 1)] profile payload == some (.fired .value) &&
    verdict "FirstFilledValue(Parents/Rows*/N For Key, Fallback) == [Fallback]" ["", payload]
      [slot (.concrete 1) (.concrete 2)] profile payload == some .unknown &&
    verdict "FirstFilledValue(Parents/Rows*/N For Key, Fallback) == [Fallback]" ["", payload]
      storedSlots profile payload == some (.fired .omission)) := by native_decide


example : profiles.all (fun (profile, payload) =>
    verdict "FirstFilledValue(Parents/Rows* For Key, Fallback) == [Fallback]" [payload, "invalid"]
      [slot (.concrete 1) (.concrete 1)] profile payload == some (.fired .value) &&
    verdict "FirstFilledValue(Parents/Rows*/N For \"absent\", Fallback) == [Fallback]" [payload, payload]
      [slot .all (.concrete 1), slot .all (.concrete 2)] profile payload == some .unknown &&
    verdict "FirstFilledValue(Parents/Rows*/N For \"absent\", Fallback) == [Fallback]" [payload, payload]
      [slot (.concrete 1) .all, slot (.concrete 2) .all, slot (.concrete 3) .all] profile payload == some .unknown) := by native_decide

example : (profiles.drop 2).all (fun (profile, payload) =>
    verdict "FirstFilledValue(Parents/Rows*/N For Key, Fallback) == [Fallback]" ["invalid", payload]
      [slot (.concrete 1) .all] profile payload == some .unknown) := by native_decide

private def unavailablePrefix (profile : FlatModel) (payload : String)
    (values : List String) (unavailableRow : Nat) : Option Verdict := do
  let document ← input values profile payload
  let parsed ← (parseText .english "FirstFilledValue(Parents/Rows*/N For Key, Fallback) == [Fallback]").toOption
  let checked ← (lowerCondition profile ["Form"] false parsed.body).toOption
  let .leaf leaf := checked.core | none
  let context : AddressedValidationEvaluationContext profile := {
    scalar := { fields := document.flatContext, groups := GroupPresenceContext.unavailable }, outer := []
    input := .partialView document fun row field =>
      if field == 2 && row.lookup 20 == some unavailableRow then pure none
      else some <$> document.checkedCellWithRead document.readDeclared row field }
  let result ← leaf.evalAddressedPartial? context .full (fun _ => true)
    (fun _ _ => .error (.checkedDocumentRequired [])) none
  result.toOption

example : profiles.all (fun (profile, payload) =>
    unavailablePrefix profile payload [payload, payload] 1 == some .unknown &&
    unavailablePrefix profile payload [payload, payload] 2 == some (.fired .value) &&
    unavailablePrefix profile payload ["", ""] 3 == some .unknown) := by native_decide


example : profiles.all (fun (profile, payload) =>
    verdict "FirstFilledValue(Parents/Rows*/N For Key) == [Fallback]" ["", ""]
      [slot (.concrete 1) .all] profile payload == some .notFired &&
    verdict "FirstFilledValue(Parents/Rows*/N For Key) == [Fallback]" ["", ""]
      storedSlots profile payload == some .unknown &&
    verdict "FirstFilledValue(Parents/Rows* For Key) == [Fallback]" ["", ""]
      [relevant ["Parents", "Rows"] [.all, .concrete 1, .all]] profile payload == some .notFired &&
    verdict "FirstFilledValue(Parents/Rows* For Key) == [Fallback]" ["", ""]
      [relevant ["Parents", "Rows"] [.all, .concrete 1, .concrete 1],
       relevant ["Parents", "Rows"] [.all, .concrete 1, .concrete 2]] profile payload == some .unknown) := by native_decide

end A12Kernel.Dm.PartialFieldListLocks
