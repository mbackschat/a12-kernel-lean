import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Document
import A12Kernel.Reference.Dm.LowerValidation
import A12Kernel.Elaboration.ValidationCondition.Reference

namespace A12Kernel.Dm.TemporalExtractorPrecisionLocks
open Lean A12Kernel

private def date (id : FieldId) (name : String) (mode : TemporalPartialMode)
    (repeated : Bool := false) : FlatFieldDecl := {
  id, name, groupPath := if repeated then ["Form", "Rows"] else ["Form"]
  repeatableScope := if repeated then [10] else []
  policy := { kind := .temporal .date .fullDate }
  temporalTargetPolicy := some { format := "yyyy-MM-dd", partialMode := mode } }

private def model : FlatModel := {
  baseYear := some 2024, timeZoneId := "UTC"
  fields := [
    { id := 0, name := "Out", groupPath := ["Form"], policy := { kind := .number { scale := 0, signed := true } } },
    date 1 "Day" .dayOptional, date 2 "Month" .monthOptional,
    date 3 "Year" .yearOptional, date 4 "Full" .full,
    { id := 5, name := "Clock", groupPath := ["Form"], policy := { kind := .temporal .time .time }
      temporalTargetPolicy := some { format := "HH:mm:ss" } },
    { id := 6, name := "Code", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .string } },
    date 7 "Day" .dayOptional true, date 8 "Month" .monthOptional true,
    date 9 "Year" .yearOptional true,
    { id := 10, name := "Clock", groupPath := ["Form", "Rows"], repeatableScope := [10]
      policy := { kind := .temporal .time .time }, temporalTargetPolicy := some { format := "HH:mm:ss" } },
    { id := 11, name := "Stamp", groupPath := ["Form"], policy := { kind := .temporal .dateTime .now }
      temporalTargetPolicy := some { format := "yyyy-MM-dd'T'HH:mm:ss" } }]
  repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 2, indexField := some 6 }] }

private def dm (fixture : FlatModel := model) : DmModel := {
  flat := fixture, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }

private def input (day : String := "2024-05-00") (clock : String := "12:30:45") : Json :=
  Json.mkObj [("Form", Json.mkObj [
    ("Out", "99"), ("Day", .str day), ("Month", "2024-00-00"), ("Year", "0000-00-00"),
    ("Full", "2024-05-06"), ("Clock", .str clock), ("Stamp", "2024-05-06T12:30:45"),
    ("Rows", .arr #[Json.mkObj [("Code", "A"), ("Day", .str day), ("Month", "2024-00-00"), ("Year", "0000-00-00"), ("Clock", .str clock)],
      Json.mkObj [("Code", "B"), ("Day", "2023-04-00"), ("Month", "2023-00-00"), ("Year", "0000-00-00"), ("Clock", "01:02:03")]])])]

private def checked (day : String := "2024-05-00") (fixture : FlatModel := model)
    (clock : String := "12:30:45") (requiredDay : Bool := false) : Option (CheckedDocument fixture) := do
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } } builtinStringPatternCompiler fixture).toOption
  let raw ← (readDocument (dm fixture) (input day clock)).toOption
  if !raw.refusals.isEmpty then none
  let document ← (checkDocument prepared "en_US" raw.data).toOption
  if requiredDay then
    pure (document.overlayCells [] [
      { address := { field := 1, path := [] }, cell := { rawPresent := false, parsed := none, findings := [.required] } },
      { address := { field := 7, path := [1] }, cell := { rawPresent := false, parsed := none, findings := [.required] } }])
  else pure document

private def admitted (text : String) (fixture : FlatModel := model) : Bool :=
  ((parseText .english text).toOption.bind fun parsed =>
    (lowerCondition fixture ["Form"] false parsed.body).toOption).isSome

private def validate (text : String) (day : String := "2024-05-00")
    (fixture : FlatModel := model) (clock : String := "12:30:45") (requiredDay : Bool := false) : Option Verdict := do
  let document ← checked day fixture clock requiredDay
  let parsed ← (parseText .english text).toOption
  let condition ← (lowerCondition fixture ["Form"] false parsed.body).toOption
  (condition.core.evalAddressed {
    scalar := { fields := document.flatContext, groups := GroupPresenceContext.unavailable },
    outer := [], input := .checked document }).toOption

private def compute (text : String) (day : String := "2024-05-00")
    (fixture : FlatModel := model) (clock : String := "12:30:45") (requiredDay : Bool := false) : Option (List String) := do
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler fixture).toOption
  let document ← checked day fixture clock requiredDay
  let source ← (lowerComputation fixture .english {
    name := "Extract", group := ["Form"], targetRelPath := "../Out", commonPrecondition := none,
    alternatives := [{ precondition := none, operation := text }], errorCodesToSuppress := [] }).toOption
  let results ← (runComputations world prepared document [source.2]).toOption
  pure (results.map (·.outcome))

private def loadedTemporalModel (explicit : Bool) : Option FlatModel := do
  let fields ← [(4, "Full", "DateType", "yyyy-MM-dd"),
    (5, "Clock", "TimeType", "HH:mm:ss"),
    (11, "Stamp", "DateTimeType", "yyyy-MM-dd'T'HH:mm:ss")].mapM
      fun (id, name, typeName, format) =>
        (readFieldType id ["Form"] name [] (Json.mkObj [("fieldType", Json.mkObj [
          ("type", .str typeName), (typeName, Json.mkObj
            (if explicit then [("format", .str format)] else []))])])).toOption
  pure { model with fields := model.fields.map fun field =>
    (fields.find? (·.id == field.id)).getD field }

private def loadedExtraction (explicit : Bool) (expression : String) (expected : Nat) :
    Option (Verdict × List String) := do
  let fixture ← loadedTemporalModel explicit
  let verdict ← validate (expression ++ " == " ++ toString expected) (fixture := fixture)
  let results ← compute expression (fixture := fixture)
  pure (verdict, results)

example : [("YearFromDate(Full)", 2024), ("HoursFromTime(Clock)", 12),
    ("YearFromDate(DateFromDateTime(Stamp))", 2024),
    ("HoursFromTime(TimeFromDateTime(Stamp))", 12)].all (fun (expression, expected) =>
      loadedExtraction false expression expected ==
        some (.fired .value, ["value " ++ toString expected]) &&
      loadedExtraction true expression expected ==
        loadedExtraction false expression expected) := by native_decide

example : validate "YearFromDate(Full) == 2024" = some (.fired .value) ∧
    compute "HoursFromTime(Clock)" = some ["value 12"] := by native_decide

example : validate "YearFromDate(Clock) == 1970" = some (.fired .value) ∧
    compute "YearFromDate(Clock)" = some ["value 1970"] := by native_decide

example : validate "NumberOfFilledFields(Rows*/Code Having YearFromDate(Rows/Day) == 2024) == 1" =
    some (.fired .omission) := by native_decide

example : validate "HoursFromTime(Rows/Clock For \"A\") == 12" = some (.fired .value) ∧
    compute "HoursFromTime(Rows/Clock For \"B\")" = some ["value 1"] := by native_decide

example : validate "YearFromDate(Day) == 2024" = some (.fired .value) ∧
    compute "MonthFromDate(Day)" = some ["value 5"] := by native_decide

example : admitted "DayFromDate(Day) == 1" = false ∧
    validate "YearFromDate(Rows/Day For \"A\") == 2024" = some (.fired .value) := by native_decide

private def withPrecision (mode : TemporalPartialMode) (baseYear : Option Int) : FlatModel := { model with
  baseYear
  fields := model.fields.map fun field =>
    if field.id == 1 || field.id == 7 then { field with
      temporalTargetPolicy := some { format := "yyyy-MM-dd", partialMode := mode } } else field }

private def computationAdmitted (text : String) (fixture : FlatModel := model) : Bool :=
  (lowerComputation fixture .english {
    name := "Extract", group := ["Form"], targetRelPath := "../Out", commonPrecondition := none,
    alternatives := [{ precondition := none, operation := text }], errorCodesToSuppress := [] }).isOk

private def extractors : List (String × TemporalNumericPart) := [
  ("YearFromDate", .date .year), ("MonthFromDate", .date .month), ("QuarterFromDate", .date .quarter),
  ("DayFromDate", .date .day), ("HoursFromTime", .time .hour),
  ("MinutesFromTime", .time .minute), ("SecondsFromTime", .time .second)]

private def precisionCases : List (TemporalPartialMode × List Bool) := [
  (.full, [true, true, true, true, false, false, false]),
  (.dayOptional, [true, true, true, false, false, false, false]),
  (.monthOptional, [true, false, false, false, false, false, false]),
  (.yearOptional, [false, false, false, false, false, false, false])]

example : precisionCases.all (fun (mode, expected) => [none, some 2024].all fun baseYear =>
    let fixture := withPrecision mode baseYear
    (extractors.map fun (name, _) => admitted (name ++ "(Day) == 0") fixture) == expected &&
    (extractors.map fun (name, _) => computationAdmitted (name ++ "(Day)") fixture) == expected &&
    (extractors.map fun (name, _) => admitted (name ++ "(Rows/Day For \"A\") == 0") fixture) == expected &&
    (extractors.map fun (name, _) => computationAdmitted (name ++ "(Rows/Day For \"A\")") fixture) == expected &&
    (extractors.map fun (name, _) => admitted
      ("NumberOfFilledFields(Rows*/Code Having " ++ name ++ "(Rows/Day) == 0) == 1") fixture) == expected) := by native_decide

private def directPrecisionDiagnostic (fixture : FlatModel) (part : TemporalNumericPart) :
    Option KernelStaticDiagnostic :=
  match resolveNumericValidationAtom fixture ["Form"]
      (.temporalFieldPart { base := .relative 0, groups := [], field := "Day" } part) with
  | .ok _ => none
  | .error error => error.temporalFieldPartDiagnostic?

private def keyedPrecisionDiagnostic (fixture : FlatModel) (part : TemporalNumericPart) :
    Option KernelStaticDiagnostic :=
  match elaborateTemporalNumericExpression fixture ["Form"] (.indexed {
      target := { base := .relative 0, groups := ["Rows"], field := "Day" },
      key := .literal (.text "A") }) part with
  | .ok _ => none
  | .error error => error.precisionDiagnostic?

example : precisionCases.all (fun (mode, _) => extractors.all fun (_, part) =>
    let fixture := withPrecision mode (some 2024)
    let declaration := date 1 "Day" mode
    declaration.admitsTemporalPartPrecision part ||
      (directPrecisionDiagnostic fixture part == some .invalidDateType &&
        keyedPrecisionDiagnostic fixture part == some .invalidDateType &&
        (match fixture.elaborateNumericComputationAtom ["Form"] ["Form"]
          (.numeric (.temporalFieldPart { base := .relative 0, groups := [], field := "Day" } part)) with
          | .ok _ => false
          | .error error => error.diagnostic? == some .invalidDateType))) := by native_decide

example : [("YearFromDate", "2024", "1"), ("MonthFromDate", "5", "1"), ("QuarterFromDate", "2", "2")].all
    (fun (name, expected, count) =>
      validate (name ++ "(Day) == " ++ expected) == some (.fired .value) &&
      compute (name ++ "(Day)") == some ["value " ++ expected] &&
      validate (name ++ "(Rows/Day For \"A\") == " ++ expected) == some (.fired .value) &&
      compute (name ++ "(Rows/Day For \"A\")") == some ["value " ++ expected] &&
      validate ("NumberOfFilledFields(Rows*/Code Having " ++ name ++ "(Rows/Day) == " ++ expected ++ ") == " ++ count) ==
        some (.fired .omission)) := by native_decide

example : validate "YearFromDate(Month) == 2024" = some (.fired .value) ∧
    compute "YearFromDate(Rows/Month For \"B\")" = some ["value 2023"] ∧
    validate "NumberOfFilledFields(Rows*/Code Having YearFromDate(Rows/Month) == 2024) == 1" =
      some (.fired .omission) := by native_decide

example : validate "YearFromDate(Day) == 0" "" = some (.fired .omission) ∧
    compute "MonthFromDate(Day)" "" = some ["value 0"] ∧
    validate "YearFromDate(Rows/Day For \"A\") == 0" "" = some (.fired .omission) ∧
    compute "QuarterFromDate(Rows/Day For \"A\")" "" = some ["value 0"] ∧
    validate "YearFromDate(Day) == 2024" "bad" = some .unknown ∧
    compute "YearFromDate(Day)" "bad" = some ["cleared"] ∧
    compute "YearFromDate(Rows/Day For \"A\")" "bad" = some ["cleared"] ∧
    compute "YearFromDate(Rows/Day For \"B\")" "bad" = some ["value 2023"] ∧
    compute "YearFromDate(Rows/Day For \"missing\")" "bad" = some ["value 0"] := by native_decide

example : validate "NumberOfFilledFields(Rows*/Code Having YearFromDate(Rows/Day) == 2023) == 1" "bad" =
    some (.fired .omission) ∧
    admitted "NumberOfFilledFields(Rows*/Code Having YearFromDate(Rows/Day For \"A\") == 2024) == 1" = false := by native_decide

example : [1999, 2024].all (fun baseYear =>
    let fixture := { model with baseYear := some baseYear }
    validate "YearFromDate(Clock) == 1970" (fixture := fixture) == some (.fired .value) &&
    compute "YearFromDate(Clock)" (fixture := fixture) == some ["value 1970"] &&
    validate "YearFromDate(Rows/Clock For \"A\") == 1970" (fixture := fixture) == some (.fired .value) &&
    compute "YearFromDate(Rows/Clock For \"B\")" (fixture := fixture) == some ["value 1970"] &&
    validate "NumberOfFilledFields(Rows*/Code Having YearFromDate(Rows/Clock) == 1970) == 2" (fixture := fixture) ==
      some (.fired .omission) &&
    compute "YearFromDate(Date(\"01\",\"02\",YearFromDate(Clock)))" (fixture := fixture) == some ["value 1970"] &&
    compute "YearFromDate(AddYears(Full,YearFromDate(Clock) - 1970))" (fixture := fixture) == some ["value 2024"]) := by native_decide

example : validate "YearFromDate(Clock) == 0" (clock := "") = some (.fired .omission) ∧
    compute "YearFromDate(Clock)" (clock := "") = some ["value 0"] ∧
    validate "YearFromDate(Clock) == 1970" (clock := "bad") = some .unknown ∧
    compute "YearFromDate(Clock)" (clock := "bad") = some ["cleared"] := by native_decide

example : compute "YearFromDate(Date(\"01\",\"02\",YearFromDate(Day)))" = some ["value 2024"] ∧
    compute "YearFromDate(Date(\"01\",\"02\",YearFromDate(Rows/Day For \"A\")))" = some ["value 2024"] ∧
    compute "YearFromDate(AddYears(Full,YearFromDate(Day) - 2024))" = some ["value 2024"] ∧
    compute "YearFromDate(AddYears(Full,YearFromDate(Rows/Day For \"A\") - 2024))" = some ["value 2024"] := by native_decide

example : ["YearFromDate(\"2024-05-06\")", "YearFromDate(AddYears(Day,1))",
    "YearFromDate(AddYears(Rows/Day For \"A\",1))", "YearFromDate(Rows*/Day)",
    "YearFromDate(DateFromDateTime(Full))", "HoursFromTime(TimeFromDateTime(Clock))"].all
      (fun text => !admitted (text ++ " == 0") && !computationAdmitted text) ∧
    admitted "YearFromDate(Date(\"06\",\"05\",\"2024\")) == 2024" ∧
    compute "YearFromDate(DateFromDateTime(Stamp))" = some ["value 2024"] ∧
    compute "HoursFromTime(TimeFromDateTime(Stamp))" = some ["value 12"] := by native_decide

private def referenceInputs : MessageReferenceInputs := {
  cache := .known { insertions := [
    { group := 10, parentPath := [], key := .text "A", row := 1 },
    { group := 10, parentPath := [], key := .text "B", row := 2 }] }
  keyAt := fun _ => none }

private def pointers (text : String) : Option (List MessagePointer) := do
  let parsed ← (parseText .english text).toOption
  let condition ← (lowerCondition model ["Form"] false parsed.body).toOption
  (condition.core.referencePointers [] (some referenceInputs)).toOption

example : pointers "YearFromDate(Day) == 2024" = some [{ field := 1, coordinates := [] }] ∧
    pointers "YearFromDate(Rows/Day For \"A\") == 2024" = some [
      { field := 6, coordinates := [.concrete 1] }, { field := 7, coordinates := [.concrete 1] }] := by native_decide

private def keyedDependencies : Option (List FieldId × List FieldId × List (List RepeatableLevel) × Bool) := do
  let source ← (elaborateTemporalNumericExpression model ["Form"] (.indexed {
    target := { base := .relative 0, groups := ["Rows"], field := "Day" },
    key := .literal (.text "A") }) (.date .year)).toOption
  pure (source.fieldIds, source.boundFieldIds, source.bindingScopes, source.requiresAddressed)

example : keyedDependencies = some ([6, 7], [], [[], []], true) := by native_decide

private def partialProjection (field : FieldId) (row : Nat) (cell : Option CheckedCell)
    (scope : ValidationRelevanceScope := .full) :
    Option (Sum NumericValidationUnavailable NumericArithmeticOutcome) := do
  let document ← checked
  let source ← (elaborateTemporalNumericExpression model ["Form"] (.indexed {
    target := { base := .relative 0, groups := ["Rows"], field := "Day" },
    key := .literal (.text "A") }) (.date .year)).toOption
  let partialRead : TemporalPartialReadContext model := {
    document, scope, read := fun environment current =>
      if current == field && environment == [(10, row)] then pure cell
      else (fun addressed => some addressed.cell) <$> document.addressedCell environment current }
  let result ← (source.evalResult .validation document.flatContext (some document.indexedComputationFillContext)
    [] (some partialRead)).toOption
  pure (match result with | .error cause => .inl cause | .ok value => .inr value)

example : partialProjection 7 1 none = some (.inl .nonRelevant) ∧
    partialProjection 7 1 (some malformedCheckedCell) = some (.inl (.formal .malformed)) ∧
    partialProjection 7 2 (some malformedCheckedCell) = some (.inr (.value 2024 .fixed)) ∧
    partialProjection 7 2 none = some (.inr (.value 2024 .fixed)) ∧
    partialProjection 7 1 (some malformedCheckedCell) (.partialSet []) = some (.inl .nonRelevant) := by native_decide

example : pointers "YearFromDate(AddYears(Full,YearFromDate(Rows/Day For \"A\") - 2024)) == 2024" =
    some [{ field := 4, coordinates := [] },
      { field := 6, coordinates := [.concrete 1] }, { field := 7, coordinates := [.concrete 1] }] := by native_decide

example : (match elaborateScalarTemporalProjection
    { model with fields := model.fields ++ [date 1 "Duplicate" .dayOptional] } ["Form"]
    (.field { base := .relative 0, groups := [], field := "Day" }) (.date .year) with
    | .error (.model _) => true
    | _ => false) = true := by native_decide

private def parentGroup : RepeatableGroupDecl := {
  level := 20, path := ["Form", "Parent"], repeatability := some 2 }

private def nestedModel : FlatModel := { model with
  fields := model.fields.map fun field => if field.repeatableScope == [10] then
    { field with groupPath := ["Form", "Parent", "Rows"], repeatableScope := [20, 10] } else field
  repeatableGroups := [parentGroup,
    { level := 10, path := ["Form", "Parent", "Rows"], repeatability := some 2, indexField := some 6 }] }

private def boundKeyModel : FlatModel := { model with
  fields := model.fields ++ [{ id := 12, name := "Key", groupPath := ["Form", "Parent"], repeatableScope := [20], policy := { kind := .string } }]
  repeatableGroups := model.repeatableGroups ++ [parentGroup] }

private def projectedScopeAdmission (fixture : FlatModel) (parentSteps : Nat)
    (key : SurfaceSemanticIndexKey) : Option (Bool × Bool) := do
  let source ← (elaborateTemporalNumericExpression fixture ["Form", "Parent"] (.indexed {
    target := { base := .relative parentSteps, groups := ["Rows"], field := "Day" }, key }) (.date .year)).toOption
  pure (source.core.admitted fixture [], source.core.admitted fixture [20])

example : projectedScopeAdmission nestedModel 0 (.literal (.text "A")) = some (false, true) := by native_decide

example : projectedScopeAdmission boundKeyModel 1
    (.field { base := .relative 0, groups := [], field := "Key" }) = some (false, true) := by native_decide

example : validate "YearFromDate(Day) == 0" "" (requiredDay := true) = some .unknown ∧
    validate "YearFromDate(Rows/Day For \"A\") == 0" "" (requiredDay := true) = some .unknown ∧
    compute "YearFromDate(Day)" "" (requiredDay := true) = some ["value 0"] ∧
    compute "YearFromDate(Rows/Day For \"A\")" "" (requiredDay := true) = some ["value 0"] ∧
    validate "YearFromDate(Rows/Day For \"B\") == 2023" "" (requiredDay := true) = some (.fired .value) ∧
    compute "YearFromDate(Rows/Day For \"B\")" "" (requiredDay := true) = some ["value 2023"] := by native_decide

end A12Kernel.Dm.TemporalExtractorPrecisionLocks
