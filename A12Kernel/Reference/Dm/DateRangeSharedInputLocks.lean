import A12Kernel.Reference.Dm.Document
import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.LowerValidation
import A12Kernel.Elaboration.SemanticIndexDateRange
import A12Kernel.Elaboration.ValidationCondition.Reference

namespace A12Kernel.Dm.DateRangeSharedInputLocks
open Lean A12Kernel

private def declaration (id : FieldId) (format separator : String)
    (direction : DateRangeYearInterpretation) : FlatFieldDecl := {
  id, name := "Range" ++ toString id, groupPath := ["Form"]
  policy := { kind := .dateRange }
  dateRangePolicy := some { format, separator, interpretationOfYear := some direction } }

private def nativeDeclaration (id : FieldId) (format separator : String)
    (direction : DateRangeYearInterpretation) (additionalCheck : Bool := false) :
    Option FlatFieldDecl :=
  (readFieldType id ["Form"] ("Range" ++ toString id) [] (Json.mkObj [
    ("fieldType", Json.mkObj [("type", "DateRangeType"), ("DateRangeType", Json.mkObj [
      ("format", Json.str format), ("rangeSeparator", Json.str separator),
      ("interpretationOfYear", Json.str (if direction == .anchorStart then "FROM" else "TO")),
      ("youngerThan1900Check", Json.bool additionalCheck)])])])).toOption

private def nativeRead (profiles : List (String × String × DateRangeYearInterpretation × Bool))
    (field : FieldId) (text : String) : Option (String × RawCell) := do
  let fields ← profiles.zipIdx.mapM fun ((format, separator, direction, additionalCheck), id) =>
    nativeDeclaration id format separator direction additionalCheck
  let fixture : FlatModel := { fields, timeZoneId := "UTC" }
  let dm : DmModel := { flat := fixture, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let input ← (readDocument dm (Json.mkObj [("Form", Json.mkObj [
    ("Range" ++ toString field, Json.str text)])])).toOption
  if !input.refusals.isEmpty then none
  let cell ← input.data.cells.find? (fun cell => cell.address.field == field)
  pure (cell.stored, cell.raw)

private def read (firstFormat firstSeparator format separator text : String)
    (baseYear : Option Int) (direction : DateRangeYearInterpretation) :
    Option (String × RawCell) := do
  let first := declaration 0 firstFormat firstSeparator direction
  let source := declaration 1 format separator direction
  let model : FlatModel := { fields := [first, source], baseYear, timeZoneId := "UTC" }
  let cell ← (classifyStored model source { field := 1, path := [] } text).toOption
  pure (cell.stored, cell.raw)

private def components (value : Option (String × RawCell)) :
    Option (String × Int × Int × Nat) := do
  let (text, .parsed (.dateRange (.exact range))) ← value | none
  pure (text, range.start.parts.year, range.finish.parts.year, range.finish.parts.day)

-- The source matrix distinguishes declared conversion's day-1 default from runtime
-- endpoint completion: spec/05 §8, src-date-range-shared-runtime (2026-10-09).
example : [none, some 2024].all (fun year =>
    [DateRangeYearInterpretation.anchorStart, .anchorFinish].all (fun direction =>
      components (read "dd.MM" "-" "MM" "/" "03/10" year direction) ==
        some ("01.03-01.10", year.getD 2000, year.getD 2000, 1) &&
      components (read "MM" "/" "dd.MM" "-" "01.03-31.10" year direction) ==
        some ("03/10", year.getD 2000, year.getD 2000, 31))) = true := by native_decide

example : components (read "dd.MM" "-" "yyyy-MM-dd" "/"
    "2023-03-01/2024-10-31" none .anchorStart) =
    some ("01.03-31.10", 2000, 2000, 31) := by native_decide

example : read "MM" "/" "dd.MM" "-" "01.11-01.02" (some 2024) .anchorStart =
    some ("11/02", .rejected .dateRangeInvalid) := by native_decide

example : read "dd.MM" "-" "MM" "" "bad" none .anchorFinish =
    some ("bad", .rejected .dateRangeSeparator) := by native_decide

private def flagProfiles : List (String × String × DateRangeYearInterpretation × Bool) := [
  ("dd.MM", "-", .anchorStart, false), ("MM", "/", .anchorStart, true),
  ("MM", "/", .anchorStart, false)]

example : ((nativeDeclaration 1 "MM" "/" .anchorStart true).bind (·.dateRangePolicy)).map
    (·.youngerThan1900Check) = some true ∧
    components (nativeRead flagProfiles 1 "03/10") = some ("03/10", 2000, 2000, 31) ∧
    components (nativeRead flagProfiles 2 "03/10") = some ("01.03-01.10", 2000, 2000, 1) ∧
    nativeRead flagProfiles 1 "11/02" = some ("11/02", .rejected .dateRangeInvalid) := by native_decide

private def directionProfiles : List (String × String × DateRangeYearInterpretation × Bool) := [
  ("MM", "/", .anchorFinish, false), ("dd.MM", "-", .anchorStart, false),
  ("MM", "/", .anchorStart, false), ("dd.MM", "-", .anchorFinish, false)]


example : components (nativeRead directionProfiles 2 "03/10") = some ("01.03-01.10", 2000, 2000, 1) ∧
    components (nativeRead directionProfiles 3 "01.03-31.10") = some ("03/10", 2000, 2000, 31) ∧
    components (nativeRead directionProfiles 2 "11/02") = some ("01.11-01.02", 2000, 2001, 1) ∧
    nativeRead directionProfiles 3 "01.11-01.02" = some ("11/02", .rejected .dateRangeInvalid) := by native_decide

-- Declared conversion failure retains raw text for shared formal checking, rather than
-- rejecting it early: FieldValueConverter input stage, src-date-range-shared-runtime.
example : components (nativeRead [("dd.MM", "-", .anchorStart, false),
      ("MM", "/", .anchorStart, false)] 1 "01.03-31.10") = some ("01.03-31.10", 2000, 2000, 31) ∧
    components (nativeRead [("MM", "/", .anchorStart, false),
      ("dd.MM", "-", .anchorStart, false)] 1 "03/10") = some ("03/10", 2000, 2000, 31) := by native_decide

private def endpointModel (firstFormat firstSeparator format separator : String)
    (baseYear : Option Int) (direction : DateRangeYearInterpretation) : FlatModel := {
  fields := [declaration 0 firstFormat firstSeparator direction,
    declaration 1 format separator direction,
    { id := 2, name := "Out", groupPath := ["Form"], policy := { kind := .number { scale := 0, signed := true } } }]
  baseYear, timeZoneId := "UTC" }

private def admitted (fixture : FlatModel) (operation : String) : Bool :=
  ((parseText .english (operation ++ " == 0")).toOption.bind fun parsed =>
    (lowerCondition fixture ["Form"] false parsed.body).toOption).isSome &&
  (lowerComputation fixture .english {
    name := "Endpoint", group := ["Form"], targetRelPath := "../Out", commonPrecondition := none,
    alternatives := [{ precondition := none, operation }], errorCodesToSuppress := [] }).isOk

example : [DateRangeYearInterpretation.anchorStart, .anchorFinish].all (fun direction =>
    let fixture := endpointModel "dd.MM" "-" "MM" "/" none direction
    admitted fixture "YearFromDate(StartOfDateRange(Range1))" &&
      admitted fixture "DayFromDate(EndOfDateRange(Range1))" &&
      !(elaborateYearlessDateRangeBound fixture 1 .start).isOk) = true := by native_decide

private def profiles : List (String × String × String) := [
  ("yyyy-MM-dd", "/", "2023-03-01/2024-10-31"), ("dd.MM.yyyy", "-", "01.03.2023-31.10.2024"),
  ("yyyy", "/", "2023/2024"), ("yyyy-MM", "/", "2023-03/2024-10"),
  ("MM", "/", "03/10"), ("MM-dd", "/", "03-01/10-31"),
  ("MM", "", "0310"), ("dd.MM", "-", "01.03-31.10")]

private def bounds : List String := ["StartOfDateRange", "EndOfDateRange"]
private def parts : List String := ["YearFromDate", "MonthFromDate", "QuarterFromDate", "DayFromDate"]

example : profiles.all (fun (format, separator, _) =>
    [DateRangeYearInterpretation.anchorStart, .anchorFinish].all fun direction =>
      [none, some 2024].all fun baseYear =>
        let fixture := endpointModel "dd.MM" "-" format separator baseYear direction
        bounds.all (fun bound => parts.all (fun part =>
          admitted fixture (part ++ "(" ++ bound ++ "(Range1))"))) &&
        (elaborateDateRangeBound fixture 1 .start).isOk &&
        (elaborateDateRangeBound fixture 1 .finish).isOk &&
        !(elaborateYearlessDateRangeBound fixture 1 .start).isOk) = true := by native_decide

private def checked (fixture : FlatModel) (text : String) (json? : Option Json := none) : Option (CheckedDocument fixture) := do
  let dm : DmModel := { flat := fixture, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let input ← (readDocument dm (json?.getD (Json.mkObj [("Form", Json.mkObj [
    ("Range1", Json.str text), ("Out", Json.str "99")])]))).toOption
  if !input.refusals.isEmpty then none
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } } builtinStringPatternCompiler fixture).toOption
  (checkDocument prepared "en_US" input.data).toOption

private def run (fixture : FlatModel) (operation expected text : String)
    (json? : Option Json := none) : Option (Verdict × List String) := do
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler fixture).toOption
  let document ← checked fixture text json?
  let parsed ← (parseText .english (operation ++ " == " ++ expected)).toOption
  let condition ← (lowerCondition fixture ["Form"] false parsed.body).toOption
  let verdict ← (condition.core.evalAddressed {
    scalar := { fields := document.flatContext.withWorld world, groups := GroupPresenceContext.unavailable },
    outer := [], input := .checked document }).toOption
  let source ← (lowerComputation fixture .english {
    name := "Endpoint", group := ["Form"], targetRelPath := "../Out", commonPrecondition := none,
    alternatives := [{ precondition := none, operation }], errorCodesToSuppress := [] }).toOption
  let results ← (runComputations world prepared document [source.2]).toOption
  pure (verdict, results.map (·.outcome))

example : profiles.all (fun (format, separator, text) =>
    [DateRangeYearInterpretation.anchorStart, .anchorFinish].all fun direction =>
      [none, some 2024].all fun baseYear =>
        let fixture := endpointModel "dd.MM" "-" format separator baseYear direction
        let year := toString (baseYear.getD 2000)
        run fixture "YearFromDate(StartOfDateRange(Range1))" year text ==
          some (.fired .value, ["value " ++ year]) &&
        run fixture "YearFromDate(EndOfDateRange(Range1))" year text ==
          some (.fired .value, ["value " ++ year]) &&
        let day := if format == "MM" || format == "yyyy" || format == "yyyy-MM" then "1" else "31"
        run fixture "DayFromDate(EndOfDateRange(Range1))" day text ==
          some (.fired .value, ["value " ++ day])) = true := by native_decide

example : [DateRangeYearInterpretation.anchorStart, .anchorFinish].all (fun direction =>
    [none, some 2024].all fun baseYear =>
      let fixture := endpointModel "MM" "/" "dd.MM" "-" baseYear direction
      let year := toString (baseYear.getD 2000)
      run fixture "YearFromDate(StartOfDateRange(Range1))" year "01.03-31.10" ==
        some (.fired .value, ["value " ++ year]) &&
      run fixture "DayFromDate(EndOfDateRange(Range1))" "31" "01.03-31.10" ==
        some (.fired .value, ["value 31"]) &&
      run fixture "YearFromDate(StartOfDateRange(Range1))" "0" "01.11-01.02" ==
        some (.unknown, ["cleared"])) = true := by native_decide

example : [DateRangeYearInterpretation.anchorStart, .anchorFinish].all (fun direction =>
    [none, some 2024].all fun baseYear =>
      let fixture := endpointModel "dd.MM" "-" "MM" "/" baseYear direction
      let start := baseYear.getD 2000 - if direction == .anchorFinish then 1 else 0
      let finish := baseYear.getD 2000 + if direction == .anchorStart then 1 else 0
      run fixture "YearFromDate(StartOfDateRange(Range1))" (toString start) "11/02" ==
        some (.fired .value, ["value " ++ toString start]) &&
      run fixture "YearFromDate(EndOfDateRange(Range1))" (toString finish) "11/02" ==
        some (.fired .value, ["value " ++ toString finish])) = true := by native_decide

example : run (endpointModel "dd.MM" "-" "MM" "/" none .anchorStart)
    "YearFromDate(StartOfDateRange(Range1))" "0" "" = some (.fired .omission, ["value 0"]) ∧
    run (endpointModel "dd.MM" "-" "MM" "/" none .anchorStart)
      "YearFromDate(StartOfDateRange(Range1))" "0" "bad" = some (.unknown, ["cleared"]) ∧
    run (endpointModel "dd.MM" "-" "MM" "/" none .anchorStart)
      "YearFromDate(AddYears(StartOfDateRange(Range1),1))" "2001" "03/10" =
        some (.fired .value, ["value 2001"]) ∧
    run (endpointModel "dd.MM" "-" "MM" "/" none .anchorStart)
      "YearFromDate(Date(\"01\",\"02\",YearFromDate(EndOfDateRange(Range1))))" "2000" "03/10" =
        some (.fired .value, ["value 2000"]) := by native_decide

private def comparisonAdmitted (fixture : FlatModel) (text : String) : Bool :=
  ((parseText .english text).toOption.bind fun parsed =>
    (lowerCondition fixture ["Form"] false parsed.body).toOption).isSome

example : comparisonAdmitted (endpointModel "dd.MM" "-" "MM" "/" none .anchorStart)
    "StartOfDateRange(Range1) == \"01.03.2000\"" ∧
    ["HoursFromTime", "MinutesFromTime", "SecondsFromTime"].all (fun part =>
      !admitted (endpointModel "dd.MM" "-" "MM" "/" none .anchorStart)
        (part ++ "(StartOfDateRange(Range1))")) ∧
    !admitted (let fixture := endpointModel "MM" "/" "MM" "/" (some 2024) .anchorStart
      { fixture with fields := fixture.fields.map fun field =>
        { field with dateRangePolicy := field.dateRangePolicy.map fun policy =>
          { policy with interpretationOfYear := none } } })
      "DayFromDate(EndOfDateRange(Range1))" := by native_decide

private def keyedModel (direction : DateRangeYearInterpretation := .anchorStart) : FlatModel := {
  (endpointModel "dd.MM" "-" "MM" "/" none direction) with
  fields := ((endpointModel "dd.MM" "-" "MM" "/" none direction).fields.map fun field =>
    if field.id == 1 then { field with groupPath := ["Form", "Rows"], repeatableScope := [10] } else field) ++
    [{ id := 3, name := "Code", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .string } }]
  repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 2, indexField := some 3 }] }

private def selection : SurfaceSemanticIndex := {
  target := { base := .relative 0, groups := ["Rows"], field := "Range1" }, key := .literal (.text "A") }

private def keyedRead (text : String) (phase : Phase := .validation) (key : String := "A") :
    Option (NumericOperand × Bool) := do
  let fixture := keyedModel
  let dm : DmModel := { flat := fixture, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let input ← (readDocument dm (Json.mkObj [("Form", Json.mkObj [("Out", "99"), ("Rows", Json.arr #[
    Json.mkObj [("Code", "A"), ("Range1", Json.str text)],
    Json.mkObj [("Code", "B"), ("Range1", "bad")]])])])).toOption
  if !input.refusals.isEmpty then none
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } } builtinStringPatternCompiler fixture).toOption
  let document ← (checkDocument prepared "en_US" input.data).toOption
  let source ← (checkSemanticIndexDateRangeBoundPart fixture ["Form"]
    { selection with key := .literal (.text key) } .finish .year).toOption
  let preliminary ← document.applyFullIndexPreliminary.toOption
  let operand ← (source.resolvePreliminaryNumericOperand preliminary { read := fun _ => .empty } [] phase).toOption
  let observed ← (source.source.observePreliminaryRange preliminary { read := fun _ => .empty } phase).toOption
  pure (operand, match observed with | .poison _ => true | _ => false)

example : keyedRead "03/10" = some (.value 2000 .fixed, false) ∧
    keyedRead "03/10" .computation = some (.value 2000 .fixed, false) ∧
    keyedRead "" = some (.value 0 .both, false) ∧
    keyedRead "" .computation = some (.value 0 .both, false) ∧
    keyedRead "bad" = some (.unknown .dateRangeSeparator, false) ∧
    keyedRead "bad" .computation = some (.unknown .dateRangeSeparator, true) ∧
    keyedRead "bad" .validation "missing" = some (.value 0 .both, false) := by native_decide

private def keyedReferences : Option (Bool × List (List RepeatableLevel) × List MessagePointer) := do
  let source ← (checkSemanticIndexDateRangeBoundPart keyedModel ["Form"] selection .finish .day).toOption
  let references := source.source.referencesField 1 && source.source.referencesField 3 &&
    !source.source.referencesField 2
  let pointers ← (source.source.referencePointers [] (some {
    cache := { insertions := [{ group := 10, parentPath := [], key := .text "A", row := 1 }] },
    keyAt := fun _ => none })).toOption
  pure (references, source.source.bindingScopes, pointers)

example : keyedReferences = some (true, [[], []], [
    { field := 3, coordinates := [.concrete 1] }, { field := 1, coordinates := [.concrete 1] }]) := by native_decide

private def targetRun (crossed : Bool) (text : String) : Option (List String) := do
  let fields ← [("dd.MM", "-", DateRangeYearInterpretation.anchorStart),
    ("MM", "/", .anchorStart), ("MM", "/", if crossed then .anchorFinish else .anchorStart),
    ("MM", "/", .anchorStart)].zipIdx.mapM fun ((format, separator, direction), id) =>
      nativeDeclaration id format separator direction
  let fixture : FlatModel := {
    timeZoneId := "UTC"
    fields := fields ++ [
      { id := 4, name := "After", groupPath := ["Form"], policy := { kind := .number { scale := 0, signed := true } } },
      { id := 5, name := "Standard", groupPath := ["Form"], policy := { kind := .dateRange },
        dateRangePolicy := some { format := "MM", separator := "/" } },
      { id := 6, name := "StandardCopy", groupPath := ["Form"], policy := { kind := .dateRange },
        dateRangePolicy := some { format := "MM", separator := "/" } },
      { id := 7, name := "StandardEmpty", groupPath := ["Form"], policy := { kind := .dateRange },
        dateRangePolicy := some { format := "MM", separator := "/" } },
      { id := 8, name := "StandardMonth", groupPath := ["Form"], policy := { kind := .number { scale := 0, signed := true } } }] }
  let dm : DmModel := { flat := fixture, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let input ← (readDocument dm (Json.mkObj [("Form", Json.mkObj [
    ("Range1", Json.str text), ("Range2", "01/01"), ("After", "999999"),
    ("Standard", "03/10"), ("StandardCopy", "01/01"), ("StandardMonth", "999999")])])).toOption
  if !input.refusals.isEmpty then none
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler fixture).toOption
  let document ← (checkDocument prepared "en_US" input.data).toOption
  let steps ← [("Range2", "FirstFilledValue(Range1,Range3)"),
    ("After", "YearFromDate(EndOfDateRange(Range2))"),
    ("StandardCopy", "FirstFilledValue(Standard,StandardEmpty)"),
    ("StandardMonth", "MonthFromDate(StartOfDateRange(StandardCopy))")].mapM fun (target, operation) =>
      (lowerComputation fixture .english {
        name := target ++ "Comp", group := ["Form"], targetRelPath := "../" ++ target,
        commonPrecondition := none, alternatives := [{ precondition := none, operation }],
        errorCodesToSuppress := [] }).toOption
  let results ← (runComputations world prepared document (steps.reverse.map (·.2))).toOption
  pure ((results.map fun result => result.pointer ++ "=" ++ result.outcome).mergeSort (· ≤ ·))

private def withStandard (values : List String) : List String :=
  values ++ ["Form/StandardCopy=value 03/10", "Form/StandardMonth=value 3"]

example : targetRun false "03/10" = some (withStandard ["Form/After=value 2000", "Form/Range2=value 01.03-01.10"]) ∧
    targetRun true "03/10" = some (withStandard ["Form/After=value 2000", "Form/Range2=value 03/10"]) ∧
    targetRun true "11/02" = some (withStandard ["Form/After=cleared", "Form/Range2=errored 11/02"]) ∧
    targetRun true "" = some (withStandard ["Form/After=value 0", "Form/Range2=cleared"]) ∧
    targetRun true "bad" = some (withStandard ["Form/After=cleared", "Form/Range2=cleared"]) ∧
    targetRun false "" = some (withStandard ["Form/After=value 0", "Form/Range2=cleared"]) ∧
    targetRun false "bad" = some (withStandard ["Form/After=cleared", "Form/Range2=cleared"]) := by native_decide

private def storedRangeYears (direction : DateRangeYearInterpretation) (baseYear : Option Int) :
    Option (List String) := do
  let opposite := if direction == .anchorStart then .anchorFinish else .anchorStart
  let ranges ← [direction, opposite, direction].zipIdx.mapM fun (interpretation, id) =>
    nativeDeclaration id "dd.MM" "-" interpretation
  let fixture : FlatModel := {
    timeZoneId := "UTC", baseYear
    fields := ranges ++ [(3, "StartYear"), (4, "EndYear"), (5, "OriginalEndYear")].map fun (id, name) =>
      { id, name, groupPath := ["Form"], policy := { kind := .number { scale := 0, signed := true } } } }
  let dm : DmModel := { flat := fixture, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let input ← (readDocument dm (Json.mkObj [("Form", Json.mkObj [
    ("Range0", "01.11-28.02"), ("Range1", "01.01-02.01"),
    ("StartYear", "9"), ("EndYear", "9"), ("OriginalEndYear", "9")])])).toOption
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler fixture).toOption
  let document ← (checkDocument prepared "en_US" input.data).toOption
  let steps ← [("StartYear", "YearFromDate(StartOfDateRange(Range1))"),
    ("EndYear", "YearFromDate(EndOfDateRange(Range1))"),
    ("OriginalEndYear", "YearFromDate(EndOfDateRange(Range0))"),
    ("Range1", "FirstFilledValue(Range0,Range2)")].mapM fun (target, operation) =>
      (lowerComputation fixture .english {
        name := target ++ "Comp", group := ["Form"], targetRelPath := "../" ++ target,
        commonPrecondition := none, alternatives := [{ precondition := none, operation }],
        errorCodesToSuppress := [] }).toOption
  let results ← (runComputations world prepared document (steps.map (·.2))).toOption
  pure ((results.map fun result => result.pointer ++ "=" ++ result.outcome).mergeSort (· ≤ ·))

-- KF540 distinguishes a copied interval's years from reclassification under its target direction.
example : [none, some 2024].all (fun baseYear =>
    let year := baseYear.getD 2000
    storedRangeYears .anchorStart baseYear == some [
      "Form/EndYear=value " ++ toString year, "Form/OriginalEndYear=value " ++ toString (year + 1),
      "Form/Range1=value 01.11-28.02", "Form/StartYear=value " ++ toString (year - 1)] &&
    storedRangeYears .anchorFinish baseYear == some [
      "Form/EndYear=value " ++ toString (year + 1), "Form/OriginalEndYear=value " ++ toString year,
      "Form/Range1=value 01.11-28.02", "Form/StartYear=value " ++ toString year]) = true := by native_decide

private def keyedRun (operation expected text : String) : Option (Verdict × List String) :=
  run keyedModel operation expected text (some (Json.mkObj [("Form", Json.mkObj [
    ("Out", "99"), ("Rows", Json.arr #[Json.mkObj [("Code", "A"), ("Range1", Json.str text)],
      Json.mkObj [("Code", "B"), ("Range1", "bad")]])])]))

example : keyedRun "YearFromDate(StartOfDateRange(Rows/Range1 For \"A\"))" "2000" "03/10" =
    some (.fired .value, ["value 2000"]) ∧
    keyedRun "YearFromDate(AddYears(EndOfDateRange(Rows/Range1 For \"A\"),1))" "2001" "03/10" =
      some (.fired .value, ["value 2001"]) ∧
    keyedRun "DayFromDate(EndOfDateRange(Rows/Range1 For \"A\"))" "1" "03/10" =
      some (.fired .value, ["value 1"]) ∧
    keyedRun "YearFromDate(StartOfDateRange(Rows/Range1 For \"A\"))" "0" "" =
      some (.fired .omission, ["value 0"]) ∧
    keyedRun "YearFromDate(StartOfDateRange(Rows/Range1 For \"A\"))" "0" "bad" =
      some (.unknown, ["cleared"]) := by native_decide

private def keyedDslMetadata : Option ((List FieldId × List FieldId × List (List RepeatableLevel)) × (Bool × List MessagePointer)) := do
  let source ← (elaborateTemporalNumericExpression keyedModel ["Form"]
    (.indexedRangeBound selection .finish) (.date .year)).toOption
  let parsed ← (parseText .english "YearFromDate(EndOfDateRange(Rows/Range1 For \"A\")) == 2000").toOption
  let condition ← (lowerCondition keyedModel ["Form"] false parsed.body).toOption
  let pointers ← (condition.core.referencePointers [] (some {
    cache := { insertions := [{ group := 10, parentPath := [], key := .text "A", row := 1 }] },
    keyAt := fun _ => none })).toOption
  pure ((source.fieldIds, source.boundFieldIds, source.bindingScopes), (source.requiresAddressed, pointers))

example : keyedDslMetadata = some (([1, 3], [], [[], []]), (true, [
    { field := 3, coordinates := [.concrete 1] }, { field := 1, coordinates := [.concrete 1] }])) := by native_decide

private def partialKeyedProjection (row : Nat) (cell : Option CheckedCell)
    (scope : ValidationRelevanceScope := .full) :
    Option (Sum NumericValidationUnavailable NumericArithmeticOutcome) := do
  let document ← checked keyedModel "03/10" (some (Json.mkObj [("Form", Json.mkObj [
    ("Out", "99"), ("Rows", Json.arr #[Json.mkObj [("Code", "A"), ("Range1", "03/10")],
      Json.mkObj [("Code", "B"), ("Range1", "bad")]])])]))
  let source ← (elaborateTemporalNumericExpression keyedModel ["Form"]
    (.indexedRangeBound selection .finish) (.date .year)).toOption
  let partialRead : TemporalPartialReadContext keyedModel := {
    document, scope, read := fun environment current =>
      if current == 1 && environment == [(10, row)] then pure cell
      else (fun addressed => some addressed.cell) <$> document.addressedCell environment current }
  let result ← (source.evalResult .validation document.flatContext (some document.indexedComputationFillContext)
    [] (some partialRead)).toOption
  pure (match result with | .error cause => .inl cause | .ok value => .inr value)

example : partialKeyedProjection 1 none = some (.inl .nonRelevant) ∧
    partialKeyedProjection 2 none = some (.inr (.value 2000 .fixed)) ∧
    partialKeyedProjection 1 none (.partialSet []) = some (.inl .nonRelevant) := by native_decide

private def nestedModel : FlatModel := {
  keyedModel with
  fields := keyedModel.fields.map (fun field =>
      if field.id == 1 || field.id == 3 then
        { field with groupPath := ["Form", "Parents", "Rows"], repeatableScope := [5, 10] }
      else if field.id == 2 then
        { field with groupPath := ["Form", "Parents"], repeatableScope := [5] }
      else field) ++ [
    { id := 4, name := "Key", groupPath := ["Form", "Parents"], repeatableScope := [5], policy := { kind := .string } },
    { id := 6, name := "RootOut", groupPath := ["Form"], policy := { kind := .number { scale := 0, signed := true } } },
    { id := 7, name := "Out", groupPath := ["Form", "Parents", "Rows"], repeatableScope := [5, 10],
      policy := { kind := .number { scale := 0, signed := true } } },
    { id := 8, name := "Key", groupPath := ["Form", "Parents", "Keys"], repeatableScope := [5, 20],
      policy := { kind := .string } },
    { id := 9, name := "Out", groupPath := ["Form", "Parents", "Keys"], repeatableScope := [5, 20],
      policy := { kind := .number { scale := 0, signed := true } } }]
  repeatableGroups := [{ level := 5, path := ["Form", "Parents"], repeatability := some 2 },
    { level := 10, path := ["Form", "Parents", "Rows"], repeatability := some 2, indexField := some 3 },
    { level := 20, path := ["Form", "Parents", "Keys"], repeatability := some 2 }] }

private def nestedOperation (key : String) : String :=
  "YearFromDate(EndOfDateRange(/Form/Parents/Rows/Range1 For " ++ key ++ "))"

private def nestedConditionAdmitted (group : GroupPath) (key : String) : Bool :=
  ((parseText .english (nestedOperation key ++ " == 2000")).toOption.bind fun parsed =>
    (lowerCondition nestedModel group false parsed.body).toOption).isSome

private def nestedComputation (target key : String) : DmComputation := {
  name := "NestedEndpoint", group := ["Form"], targetRelPath := "../" ++ target,
  commonPrecondition := none, alternatives := [{ precondition := none, operation := nestedOperation key }],
  errorCodesToSuppress := [] }

example : nestedModel.validate.isOk ∧
    nestedConditionAdmitted ["Form", "Parents"] "\"A\"" ∧
    nestedConditionAdmitted ["Form", "Parents"] "/Form/Parents/Key" ∧
    !nestedConditionAdmitted ["Form"] "\"A\"" ∧
    !nestedConditionAdmitted ["Form", "Parents"] "/Form/Parents/Rows/Code" ∧
    !nestedConditionAdmitted ["Form", "Parents", "Rows"] "/Form/Parents/Rows/Code" ∧
    !nestedConditionAdmitted ["Form", "Parents"] "/Form/Parents/Keys/Key" ∧
    nestedConditionAdmitted ["Form", "Parents", "Keys"] "/Form/Parents/Keys/Key" ∧
    (lowerComputation nestedModel .english (nestedComputation "Parents/Out" "/Form/Parents/Key")).isOk ∧
    !(lowerComputation nestedModel .english (nestedComputation "RootOut" "/Form/Parents/Key")).isOk ∧
    !(lowerComputation nestedModel .english (nestedComputation "Parents/Out" "/Form/Parents/Rows/Code")).isOk ∧
    !(lowerComputation nestedModel .english (nestedComputation "Parents/Out" "/Form/Parents/Keys/Key")).isOk ∧
    (lowerComputation nestedModel .english (nestedComputation "Parents/Keys/Out" "/Form/Parents/Keys/Key")).isOk := by native_decide

private def nestedRun : Option (List String) := do
  let parent (key second : String) := Json.mkObj [("Key", Json.str key), ("Out", "99"),
    ("Rows", Json.arr #[Json.mkObj [("Code", "A"), ("Range1", "03/10"), ("Out", "99")],
      Json.mkObj [("Code", "B"), ("Range1", Json.str second), ("Out", "99")]])]
  let document ← checked nestedModel "" (some (Json.mkObj [("Form", Json.mkObj [
    ("RootOut", "99"), ("Parents", Json.arr #[parent "A" "bad", parent "B" "11/02"])])]))
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler nestedModel).toOption
  let source ← (lowerComputation nestedModel .english
    (nestedComputation "Parents/Out" "/Form/Parents/Key")).toOption
  let results ← (runComputations world prepared document [source.2]).toOption
  pure (results.map fun result => result.pointer ++ "=" ++ result.outcome)

example : nestedRun = some ["Form/Parents/Out=value 2000", "Form/Parents[2]/Out=value 2001"] := by native_decide

private def nestedMetadata : Option (List FieldId × List FieldId × List (List RepeatableLevel) × List MessagePointer) := do
  let source ← (elaborateTemporalNumericExpression nestedModel ["Form"] (.indexedRangeBound {
    target := { base := .absolute, groups := ["Form", "Parents", "Rows"], field := "Range1" },
    key := .field { base := .absolute, groups := ["Form", "Parents"], field := "Key" } } .finish)
    (.date .year) (some ["Form", "Parents"])).toOption
  let parsed ← (parseText .english (nestedOperation "/Form/Parents/Key" ++ " == 2001")).toOption
  let condition ← (lowerCondition nestedModel ["Form", "Parents"] false parsed.body).toOption
  let pointers ← (condition.core.referencePointers [(5, 2)] (some {
    cache := { insertions := [{ group := 10, parentPath := [2], key := .text "B", row := 2 }] },
    keyAt := fun address => if address.field == 4 && address.path == [2] then some (.text "B") else none })).toOption
  pure (source.fieldIds, source.boundFieldIds, source.bindingScopes, pointers)

example : nestedMetadata = some ([1, 3, 4], [4], [[5], [5]], [
    { field := 4, coordinates := [.concrete 2] },
    { field := 3, coordinates := [.concrete 2, .concrete 2] },
    { field := 1, coordinates := [.concrete 2, .concrete 2] }]) := by native_decide

end A12Kernel.Dm.DateRangeSharedInputLocks
