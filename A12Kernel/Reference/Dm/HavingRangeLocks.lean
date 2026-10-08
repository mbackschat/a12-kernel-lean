import A12Kernel.Reference.Dm.HavingFixture

namespace A12Kernel.Dm.HavingRangeLocks
open Lean A12Kernel

private def model (yearless : Bool := false) : FlatModel :=
  let format := if yearless then "MM-dd" else "yyyy-MM-dd"
  let date (id : FieldId) (name : String) (row : Bool) : FlatFieldDecl := {
    id, name, groupPath := if row then ["Form", "Rows"] else ["Form"]
    repeatableScope := if row then [10] else []
    policy := { kind := .temporal .date (TemporalComponents.ofFormat format) }
    temporalTargetPolicy := some { format } }
  let range (id : FieldId) (name : String) (row : Bool) (group : Bool := false) : FlatFieldDecl := {
    id, name, groupPath := (if row then ["Form", "Rows"] else ["Form"]) ++ (if group then ["Ranges"] else [])
    repeatableScope := if row then [10] else []
    policy := { kind := .dateRange }, dateRangePolicy := some { format, separator := "/" } }
  { HavingFixture.model with
    baseYear := if yearless then none else some 2024
    fields := (HavingFixture.model.fields.map fun field =>
      if field.id == 2 then range 2 "Expected" false
      else if field.id == 3 then range 3 "Tag" true else field) ++ [
        date 6 "Start" false, date 7 "Finish" false, date 8 "Start" true, date 9 "Finish" true,
        range 10 "Other" false, range 11 "Other" true, range 12 "Far" false, range 13 "Far" true,
        range 14 "A" false true, range 15 "B" false true, range 16 "A" true true, range 17 "B" true true] }

private structure Inputs where
  start : Option String := none
  finish : Option String := none
  range : Option String := none
  other : Option String := none
  far : Option String := none
  noRows : Bool := false
  starPair : Bool := false

private def run (filter selected : String) (yearless : Bool := false) (input : Inputs := {})
    (positiveRule : Bool := false) :=
  let text := fun value => if yearless then value.replace "2024-" "" else value
  let range := input.range.getD "2024-01-01/2024-01-03"
  let group := Json.mkObj [("A", .str (text "2024-01-01/2024-01-03")), ("B", .str (text "2024-01-03/2024-01-05"))]
  let row (second : Bool) := Json.mkObj [
    ("N", .str (if second then "11" else "7")),
    ("Tag", .str (text (input.range.getD (if second && !input.starPair then "2024-02-01/2024-02-02" else range)))),
    ("Start", .str (text (input.start.getD (if second then "2024-02-01" else "2024-01-01")))),
    ("Finish", .str (text (input.finish.getD (if second then "2024-02-02" else "2024-01-03")))),
    ("Other", .str (text (input.other.getD (if second then "2024-02-01/2024-02-02" else "2024-01-03/2024-01-05")))),
    ("Far", .str (text (input.far.getD "2024-02-01/2024-02-02"))), ("Ranges", group)]
  HavingFixture.runModel (model yearless) filter false (text range) "" ""
    (ruleExpected := selected) (zoneRules := ModelZone.concreteRules)
    (ruleCondition := if positiveRule then
      some ("FieldFilled(Error) And Sum(Rows*/N Having (" ++ filter ++ ")) > 0") else none)
    (rowsOverride := some (if input.noRows then #[] else #[row false, row true]))
    (extra := [("Out", .str "99"), ("Start", .str (text (input.start.getD "2024-01-01"))),
      ("Finish", .str (text (input.finish.getD "2024-01-03"))),
      ("Other", .str (text (input.other.getD "2024-01-03/2024-01-05"))),
      ("Far", .str (text (input.far.getD "2024-02-01/2024-02-02"))), ("Ranges", group)])

example : [false, true].all (fun yearless => run "[Rows/Tag] == [$Expected]" "7" yearless ==
    some (.fired .omission, ["value 7"])) = true := by native_decide

private def predicates : List (String × String) := [
  ("constructStored", "DateRange(Rows/Start,Rows/Finish) == [Rows/Tag]"),
  ("storedConstruct", "[Rows/Tag] == DateRange(Rows/Start,Rows/Finish)"),
  ("constructNotEqual", "DateRange(Rows/Start,Rows/Finish) != [Rows/Tag]"),
  ("constructPair", "DateRange(Rows/Start,Rows/Finish) == DateRange($Start,$Finish)"),
  ("mixedEndpoints", "DateRange(Rows/Start,$Finish) == [Rows/Tag]"),
  ("storedControl", "[Rows/Tag] == [$Expected]"),
  ("anyDirect", "DateRangesOverlap(Rows/Tag,Rows/Other)"),
  ("scalarDirect", "AtLeastOneDateRangeOverlaps(Rows/Tag In Rows/Other)"),
  ("anyCaptureLast", "DateRangesOverlap(Rows/Tag,Rows/Other,$Far)"),
  ("anyCaptureFirst", "DateRangesOverlap($Far,Rows/Tag,Rows/Other)"),
  ("scalarCapture", "AtLeastOneDateRangeOverlaps($Far In Rows/Tag,Rows/Other)"),
  ("scalarGroup", "AtLeastOneDateRangeOverlaps(Rows/Tag In Rows/Ranges)"),
  ("anyStar", "FieldFilled(Rows/N) And DateRangesOverlap(Rows*/Tag)")]

private def v0 : Verdict × List String := (.notFired, ["value 0"])
private def v7 : Verdict × List String := (.fired .omission, ["value 7"])
private def v11 : Verdict × List String := (.fired .omission, ["value 11"])
private def v18 : Verdict × List String := (.fired .omission, ["value 18"])
private def cleared : Verdict × List String := (.notFired, ["cleared"])
private def omissionCleared : Verdict × List String := (.fired .omission, ["cleared"])

private structure MatrixRow where
  name : String
  input : Inputs := {}
  expected : List (Verdict × List String)

-- Both strategies and profiles agree in having-range-family-2026-10-08/{exact,yearless}/artifact.json.
-- R_<predicate>Having message types and computation outcomes are independent oracle columns.
private def matrix : List MatrixRow := [
  { name := "filled",
    expected := [v18, v18, v0, v7, v7, v7, v18, v18, v18, v18, v11, v7, v0] },
  { name := "emptyStart", input := { start := some "" },
    expected := [v0, v0, v0, v0, v0, v7, v18, v18, v18, v18, v11, v7, v0] },
  { name := "badStart", input := { start := some "bad" },
    expected := [cleared, cleared, cleared, cleared, cleared, v7, v18, v18, v18, v18, v11, v7, v0] },
  { name := "emptyRange", input := { range := some "" },
    expected := [v0, v0, v0, v7, v0, v0, v0, v0, v11, v11, v11, v0, v0] },
  { name := "badRange", input := { range := some "bad" },
    expected := [cleared, cleared, cleared, v7, cleared, cleared, cleared, cleared,
      omissionCleared, omissionCleared, omissionCleared, cleared, cleared] },
  { name := "badOther", input := { other := some "bad" },
    expected := [v18, v18, v0, v7, v7, v7, cleared, cleared,
      omissionCleared, omissionCleared, omissionCleared, v7, v0] },
  { name := "emptyStartBadFinish", input := { start := some "", finish := some "bad" },
    expected := [cleared, cleared, cleared, cleared, cleared, v7, v18, v18, v18, v18, v11, v7, v0] },
  { name := "badCapturedSuffix", input := { far := some "bad" },
    expected := [v18, v18, v0, v7, v7, v7, v18, v18, v18, omissionCleared, cleared, v7, v0] },
  { name := "noRows", input := { noRows := true },
    expected := [v0, v0, v0, v0, v0, v0, v0, v0, v0, v0, v0, v0, v0] },
  { name := "starPair", input := { starPair := true },
    expected := [v7, v7, v11, v7, v7, v18, v7, v7, v18, v18, v11, v18, v18] },
  { name := "emptyScalarBadList", input := { range := some "", other := some "bad" },
    expected := [v0, v0, v0, v7, v0, v0, cleared, v0, cleared, cleared, cleared, v0, v0] }]

-- Silence in these captures cannot distinguish the two non-firing internal verdicts (Verdict.collapseUnknown in Core.lean).
private def observed (yearless : Bool) (row : MatrixRow) : List (Option (Verdict × List String)) :=
  predicates.map fun (_, predicate) =>
    (run predicate "" yearless row.input true).map fun (verdict, outcomes) =>
      (verdict.collapseUnknown, outcomes)

example : [false, true].flatMap (fun yearless => matrix.map (observed yearless)) =
    [false, true].flatMap (fun _ => matrix.map fun row => row.expected.map some) := by native_decide

private def construction := "DateRange(Rows/Start,Rows/Finish)"

example : [false, true].all (fun yearless =>
    let fixture := model yearless
    ["<", "<=", ">", ">="].all (fun operator =>
      HavingFixture.admissions fixture (construction ++ " " ++ operator ++ " [Rows/Tag]") == (false, false) &&
      HavingFixture.admissions fixture ("[Rows/Tag] " ++ operator ++ " " ++ construction) == (false, false)) &&
    ["DateRangesOverlap(" ++ construction ++ ",Rows/Tag)",
      "DateRangesOverlap(Rows/Tag," ++ construction ++ ")",
      "AtLeastOneDateRangeOverlaps(" ++ construction ++ " In Rows/Tag)",
      "AtLeastOneDateRangeOverlaps(Rows/Tag In " ++ construction ++ ")",
      "DateRangesOverlap(Rows/Ranges,Rows/Tag)",
      "AtLeastOneDateRangeOverlaps(Rows/Ranges In Rows/Tag)"].all (fun predicate =>
        HavingFixture.admissions fixture predicate == (false, false)) &&
    ["[Rows/Start]", "Today", "BaseYear", "\"01.01.2024\"", "Rows*/Start", "Rows/Ranges", "Rows*"].all
      (fun endpoint =>
        HavingFixture.admissions fixture ("DateRange(" ++ endpoint ++ ",Rows/Finish) == [Rows/Tag]") == (false, false) &&
        HavingFixture.admissions fixture ("DateRange(Rows/Start," ++ endpoint ++ ") == [Rows/Tag]") == (false, false))) = true := by
  native_decide

private def withFormats (fixture : FlatModel) (formats : List (FieldId × String)) : FlatModel :=
  { fixture with fields := fixture.fields.map fun field =>
    match formats.find? (fun replacement => replacement.1 == field.id) with
    | none => field
    | some (_, format) => match field.policy.kind with
      | .temporal kind _ => { field with
          policy := { field.policy with kind := .temporal kind (TemporalComponents.ofFormat format) }
          temporalTargetPolicy := some { format } }
      | .dateRange => { field with dateRangePolicy := some { format, separator := "/" } }
      | _ => field }

-- Date fragments omit components at full precision; partial precision remains a separate refusal (spec/05 §8).
example : [8, 9].all (fun endpoint =>
    let partialFixture := { model false with fields := (model false).fields.map fun field =>
      if field.id == endpoint then { field with
        temporalTargetPolicy := some { format := "yyyy-MM-dd", partialMode := .dayOptional } } else field }
    HavingFixture.admissions partialFixture (construction ++ " == [Rows/Tag]") == (false, false) &&
    HavingFixture.admissions (withFormats (model true) [(endpoint, "MM")])
      (construction ++ " == [Rows/Tag]") == (false, false)) = true := by native_decide

private def mixedYearPredicates := [
  "DateRangesOverlap(Rows/Tag,$Expected)", "DateRangesOverlap($Expected,Rows/Tag)",
  "AtLeastOneDateRangeOverlaps(Rows/Tag In $Expected)",
  "AtLeastOneDateRangeOverlaps($Expected In Rows/Tag)"]

example : mixedYearPredicates.all (fun predicate =>
    let mixed := withFormats (model true) [(2, "yyyy-MM-dd")]
    HavingFixture.admissions mixed predicate == (false, false) &&
    HavingFixture.admissions { mixed with baseYear := some 2024 } predicate == (true, true) &&
    HavingFixture.admissions (withFormats (model true) [(3, "MM")]) predicate == (true, true)) = true := by
  native_decide

example : ["==", "!="].all (fun operator =>
    let monthConstructor := withFormats (model true) [(8, "MM"), (9, "MM")]
    [construction ++ " " ++ operator ++ " [Rows/Tag]",
      "[Rows/Tag] " ++ operator ++ " " ++ construction,
      construction ++ " " ++ operator ++ " DateRange($Start,$Finish)",
      "DateRange($Start,$Finish) " ++ operator ++ " " ++ construction].all (fun predicate =>
        HavingFixture.admissions monthConstructor predicate == (false, false))) = true := by native_decide

private def pointerModel (yearless : Bool) : FlatModel :=
  { model yearless with fields := (model yearless).fields ++ [{
    id := 18, name := "Token", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .string } }] }

private def constructionOrigins (yearless : Bool) : Option Bool := do
  let parsed ← (parseText .english
    ("FieldValuesNotUnique(/Form/Rows*/Token Having " ++
      "DateRange(/Form/Rows/Start,/Form/Rows/Finish) == DateRange($/Form/Rows/Start,$/Form/Rows/Finish))")).toOption
  let checked ← (lowerCondition (pointerModel yearless) ["Form", "Rows"] false parsed.body).toOption
  let pointers ← (checked.core.referencePointers [(10, 2)]).toOption
  let expected : List MessagePointer := [
    { field := 18, coordinates := [.wildcard] },
    { field := 8, coordinates := [.wildcard] }, { field := 9, coordinates := [.wildcard] },
    { field := 8, coordinates := [.concrete 2] }, { field := 9, coordinates := [.concrete 2] }]
  pure (pointers.length == expected.length && expected.all pointers.contains)

example : [false, true].all (fun yearless =>
    HavingFixture.referencesFor "DateRangesOverlap(/Form/Rows/Tag,$/Form/Rows/Tag)"
      (pointerModel yearless) "Token" == some (true, true) &&
    constructionOrigins yearless == some true) = true := by native_decide

-- Validation retains the February seed; the dependent computation must instead select January after the range producer (spec/09).
example : HavingFixture.runModel (model false) "DateRangesOverlap(Rows/Tag,$Expected)" true
    "2024-02-01/2024-02-02" "2024-01-01/2024-01-03" "2024-02-01/2024-02-02"
    "DateRange(Start,Finish)" [("Out", .str "99"), ("Start", .str "2024-01-01"), ("Finish", .str "2024-01-03")]
    (ruleExpected := "5") (zoneRules := ModelZone.concreteRules) =
      some (.fired .omission, ["value 2024-01-01/2024-01-03", "value 9"]) := by native_decide

-- The plural list may expand a starred group; the same group is forbidden to the any-pair operator (spec/05 §8).
example : [false, true].all (fun yearless =>
    let predicate := "AtLeastOneDateRangeOverlaps(Rows/Tag In Rows*/Ranges)"
    HavingFixture.admissions (model yearless) predicate == (true, true) &&
    HavingFixture.admissions (model yearless) "DateRangesOverlap(Rows*/Ranges)" == (false, false) &&
    run predicate "7" yearless == some (.fired .omission, ["value 7"]) &&
    run predicate "18" yearless { starPair := true } == some (.fired .omission, ["value 18"]) &&
    run predicate "0" yearless { range := some "" } == some (.fired .omission, ["value 0"]) &&
    run predicate "0" yearless { noRows := true } == some (.fired .omission, ["value 0"])) = true := by native_decide

private def mixedSpellingModel : FlatModel := {
  model false with baseYear := none, fields := (model false).fields.map fun field =>
    if field.id == 17 then { field with dateRangePolicy := some { format := "dd.MM.yyyy", separator := "-" } }
    else field }

example : ["Rows/Ranges", "Rows*/Ranges"].all (fun source =>
    HavingFixture.admissions mixedSpellingModel
      ("AtLeastOneDateRangeOverlaps(Rows/Tag In " ++ source ++ ")") == (false, false) &&
    HavingFixture.admissions { mixedSpellingModel with baseYear := some 2024 }
      ("AtLeastOneDateRangeOverlaps(Rows/Tag In " ++ source ++ ")") == (true, true)) = true ∧
    HavingFixture.admissions mixedSpellingModel
      "AtLeastOneDateRangeOverlaps(Rows/Tag In Rows/Ranges/A,Rows/Ranges/B)" = (true, true) := by native_decide

end A12Kernel.Dm.HavingRangeLocks
