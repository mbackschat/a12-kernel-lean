import A12Kernel.Reference.Dm.HavingFixture

namespace A12Kernel.Dm.HavingUniquenessLocks
open A12Kernel Lean

private def model (token : Bool) : FlatModel := { HavingFixture.model with
  fields := HavingFixture.model.fields ++ [{
    id := 6, groupPath := ["Form", "Rows"], name := "Other", repeatableScope := [10],
    policy := { kind := if token then .string else .number { scale := 0, signed := true } } }] }

private def run (token : Bool) (filter : String) (operation : Option String := none) (expected : String := "9") : Option (Verdict × List String) :=
  let row (tag number other : String) := Json.mkObj [("Tag", .str tag), ("N", .str number), ("Other", .str other)]
  HavingFixture.runModel (model token) filter false "unused" "A" "B"
    (operationOverride := operation) (ruleExpected := expected)
    (rowsOverride := some #[row "A" "2" (if token then "A" else "2"),
      row "B" "5" (if token then "C" else "0"), row "A" "7" (if token then "A" else "7")])

example : run false "[Rows/N] == [Rows/Other]" = some (.fired .omission, ["value 9"]) ∧
    run true "[Rows/Tag] == [Rows/Other]" = some (.fired .omission, ["value 9"]) := by native_decide

example : run false "FieldValuesNotUnique(Rows/N, Rows/Other)" =
    some (.fired .omission, ["value 9"]) := by native_decide

example : run true "FieldValuesNotUnique(Rows/Tag, Rows/Other)" =
    some (.fired .omission, ["value 9"]) := by native_decide

private def temporalModel : FlatModel := { HavingFixture.model with fields := HavingFixture.model.fields ++
  ([ (6, "First"), (7, "Second") ].map fun (id, name) => {
    id, name, groupPath := ["Form", "Rows"], repeatableScope := [10],
    policy := { kind := .temporal .date .fullDate }, temporalTargetPolicy := some { format := "yyyy-MM-dd" } }) }

private def temporalRun (filter : String) : Option (Verdict × List String) :=
  let row (number second : String) := Json.mkObj [
    ("N", .str number), ("First", .str "2024-03-01"), ("Second", .str second)]
  HavingFixture.runModel temporalModel filter false "unused" "unused" "unused"
    (rowsOverride := some #[row "2" "2024-03-01", row "5" "2024-03-02", row "7" "2024-03-01"])

example : temporalRun "[Rows/First] == [Rows/Second]" =
    some (.fired .omission, ["value 9"]) := by native_decide

example : temporalRun "FieldValuesNotUnique(Rows/First, Rows/Second)" =
    some (.fired .omission, ["value 9"]) := by native_decide

private inductive Admission where
  | reader | operand | refused (code : Option KernelStaticDiagnostic) | admitted
  deriving Repr, BEq, DecidableEq
private def admission (filter : String) (model : FlatModel := model false) : Admission :=
  match (parseText .english filter).toOption.bind (fun parsed => (lowerHaving parsed.body).toOption) with
  | none => .reader
  | some authored => match elaborateStarFieldPath model ["Form"] {
      base := .relative 0, groups := [{ name := "Rows", starred := true }], field := "N" } with
    | .error _ => .operand
    | .ok source => match elaborateStarHavingCore model ["Form"] source authored with
      | .error error => .refused error.diagnostic?
      | .ok _ => .admitted

private def badKinds : FlatModel := { model false with fields := (model false).fields ++ [
  { id := 7, name := "Flag", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .boolean } },
  { id := 8, name := "Confirmed", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .confirm } },
  { id := 9, name := "Range", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .dateRange }, dateRangePolicy := some { format := "yyyy-MM-dd", separator := "/" } }] }

example : admission "FieldValuesNotUnique(Rows/N, Rows/Other)" = .admitted ∧
    admission "FieldValuesNotUnique(Rows/N)" = .refused (some .paramSizeInvalidN) ∧
    admission "FieldValuesNotUnique(Rows/N, Rows/N)" = .refused (some .duplicateParam1) ∧
    admission "FieldValuesNotUnique(Rows/N, Rows/Tag)" = .refused (some .varyingTypesNotAllowed) ∧
    admission "FieldValuesNotUnique(Rows/Flag)" badKinds = .refused (some .paramSizeInvalidN) ∧
    ["Flag", "Confirmed", "Range"].all (fun name =>
      admission ("FieldValuesNotUnique(Rows/N, Rows/Tag, Rows/" ++ name ++ ")") badKinds ==
        .refused (some .onlyStringEnumNumberDateAllowed) &&
      admission ("FieldValuesNotUnique(Rows/" ++ name ++ ", Rows/Tag, Rows/N)") badKinds ==
        .refused (some .onlyStringEnumNumberDateAllowed)) = true := by native_decide

private def formatModel (different : Bool) : FlatModel := { temporalModel with fields := temporalModel.fields.map fun field =>
  if field.id == 7 then { field with temporalTargetPolicy := some { format := if different then "yyyy" else "yyyy-MM-dd" } }
  else field }
example : admission "FieldValuesNotUnique(Rows/First, Rows/Second)" (formatModel false) = .admitted ∧
    admission "FieldValuesNotUnique(Rows/First, Rows/Second)" (formatModel true) =
      .refused (some .onlyStringEnumNumberDateAllowed) ∧
    admission "FieldValuesNotUnique(Expected, Error)" = .refused (some .noIterationForWildcard) ∧
    admission "FieldValuesNotUnique(Rows/N, $Rows/Other)" = .refused (some .noWildcard) := by native_decide

example : run false "FieldValuesNotUnique(Rows/N, Rows/Other)"
      (some "FirstFilledValue(Rows*/N Having FieldValuesNotUnique(Rows/N, Rows/Other))") "2" =
      some (.fired .omission, ["value 2"]) ∧
    HavingFixture.run "FieldValuesNotUnique(Rows/Tag, $Expected)" true .string "keep" "keep" "drop" =
      some (.fired .omission, ["value drop", "value 5"]) ∧
    HavingFixture.run "FieldValuesNotUnique(Rows/Tag, $Expected)" false .enumeration "keep" "keep" "drop"
      (some { storedTokens := ["keep", "drop"] }) = some (.fired .omission, ["value 9"]) := by native_decide

example : HavingFixture.referencesFor "FieldValuesNotUnique(Tag, $Tag)" (model true) "Other" = some (true, true) ∧
    HavingFixture.referencesFor "[N] > 0" (model true) "Other" = some (false, false) := by native_decide

private def rowModel (temporal : Bool) : FlatModel :=
  let base := if temporal then temporalModel else model true
  { base with fields := base.fields.map fun field =>
    if field.id == 5 then { field with groupPath := ["Form", "Rows"], repeatableScope := [10] } else field }

private def rows (temporal : Bool) (operation : String) (guard : Option String := none)
    (partialCheck : Bool := false) : Option (List Verdict × List String) := do
  let model := rowModel temporal
  let world : World := { now := { epochMillis := 0 } }
  let dm : DmModel := { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let row (tag n other second : String) := Json.mkObj ([
    ("Tag", .str tag), ("N", .str n), ("Out", .str "99")] ++
    if temporal then [("First", .str "2024-03-01"), ("Second", .str second)] else [("Other", .str other)])
  let input ← (readDocument dm (Json.mkObj [("Form", Json.mkObj [
    ("Rows", .arr #[row "A" "2" "A" "2024-03-01", row "B" "5" "C" "2024-03-02", row "A" "7" "A" "2024-03-01"])])])).toOption
  if !input.refusals.isEmpty then none
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let document ← (checkDocument prepared "en_US" input.data).toOption
  let rule ← (checkRule dm .english {
    group := ["Form"], name := "Selected", errorCode := "SELECTED", errorEntityRelPath := "../Rows/N",
    condition := if guard.isSome then "FieldFilled(Rows/N)" else "FieldFilled(Rows/N) And " ++ operation ++ " > 0",
    severity := "ERROR" } world).toOption
  let verdicts ← (rule.evalOrdinaryRepeatableFull document (some world)).toOption
  if partialCheck then
    return ← match rule.evalOrdinaryRepeatablePartial document .full with
      | .ok .skipped => some ([], [])
      | _ => none
  let (_, computation) ← (lowerComputation model .english {
    group := ["Form"], name := "Selected", targetRelPath := "../Rows/Out", commonPrecondition := none,
    alternatives := [{ precondition := guard, operation }], errorCodesToSuppress := [] }).toOption
  let results ← (runComputations world prepared document [computation]).toOption
  pure (verdicts.map (·.2.verdict), results.map (·.outcome))

private def rowFilter := "FieldValuesNotUnique(Rows/Tag, $Rows/Other)"
private def temporalFilter := "FieldValuesNotUnique(Rows/First, $Rows/Second)"
example : rows false ("Sum(Rows*/N Having " ++ rowFilter ++ ")") =
      some ([.fired .omission, .notFired, .fired .omission], ["value 9", "value 0", "value 9"]) ∧
    rows false ("Sum(Rows/N, Rows*/N Having " ++ rowFilter ++ ")") =
      some (List.replicate 3 (.fired .omission), ["value 11", "value 5", "value 16"]) ∧
    rows true ("Sum(Rows*/N Having " ++ temporalFilter ++ ")") =
      some ([.fired .omission, .notFired, .fired .omission], ["value 14", "value 0", "value 14"]) ∧
    rows false ("Sum(Rows*/N Having " ++ rowFilter ++ ")") (partialCheck := true) = some ([], []) := by native_decide

example : rows true ("FirstFilledValue(Rows*/N Having " ++ temporalFilter ++ ")") =
      some ([.fired .omission, .notFired, .fired .omission], ["value 2", "value 0", "value 2"]) ∧
    rows true "77" (some ("AtLeastOneFieldFilled(Rows*/N Having " ++ temporalFilter ++ ")")) =
      some (List.replicate 3 (.fired .value), ["value 77", "cleared", "value 77"]) := by native_decide

private def producedTemporalModel : FlatModel := { temporalModel with fields := temporalModel.fields.map fun field =>
  if field.id == 2 then { field with
    policy := { kind := .temporal .date .fullDate }
    temporalTargetPolicy := some { format := "yyyy-MM-dd" } } else field }
example : HavingFixture.runModel producedTemporalModel "FieldValuesNotUnique(Rows/First, $Expected)"
    true "2024-03-02" "unused" "unused" "Date(\"01\", \"03\", \"2024\")"
    (rowsOverride := some #[Json.mkObj [("N", .str "2"), ("First", .str "2024-03-01")],
      Json.mkObj [("N", .str "5"), ("First", .str "2024-03-01")],
      Json.mkObj [("N", .str "7"), ("First", .str "2024-03-01")]]) =
      some (.notFired, ["value 2024-03-01", "value 14"]) := by native_decide

private def crossTemporal : FlatModel := { temporalModel with fields := temporalModel.fields.map fun field =>
  if field.id == 6 || field.id == 7 then { field with
    policy := { kind := .temporal (if field.id == 6 then .date else .time) .time },
    temporalTargetPolicy := some { format := "HH:mm:ss" } } else field }
example : admission "FieldValuesNotUnique(Rows/First, Rows/Second)" crossTemporal = .admitted := by native_decide

private def enumerationModel : FlatModel := { model true with fields := (model true).fields.map fun field =>
  if field.id == 3 then { field with policy := { kind := .enumeration }, enumeration := some {
    storedTokens := ["A", "B"], categories := [{ name := "Label", tokens := ["same", "same"] }] } } else field }
example : admission "FieldValuesNotUnique(Rows/Tag, Rows/Other)" enumerationModel = .refused (some .varyingTypesNotAllowed) ∧
    admission "FieldValuesNotUnique(Rows/Tag -> Label, Rows/Tag)" enumerationModel =
      .refused (some .categoryNotAllowed) := by native_decide

private def invalidMiddleModel : FlatModel := { model true with fields := (model true).fields.map fun field =>
  if field.id == 6 then { field with stringPolicy := { maxLength := some 2 } } else field }
example : HavingFixture.runModel invalidMiddleModel "FieldValuesNotUnique(Rows/Tag, Rows/Other, $Expected)"
    false "A" "unused" "unused" (extra := [("Out", .str "99")])
    (rowsOverride := some #[Json.mkObj [("Tag", .str "A"), ("N", .str "2"), ("Other", .str "bad")],
      Json.mkObj [("Tag", .str "B"), ("N", .str "5"), ("Other", .str "bad")],
      Json.mkObj [("Tag", .str "A"), ("N", .str "7"), ("Other", .str "bad")]]) =
      some (.fired .omission, ["cleared"]) := by native_decide

end A12Kernel.Dm.HavingUniquenessLocks
