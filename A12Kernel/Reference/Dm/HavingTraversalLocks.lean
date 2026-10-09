import A12Kernel.Reference.Dm.HavingFixture
import A12Kernel.Elaboration.GeneratedComputationValidation

namespace A12Kernel.Dm.HavingTraversalLocks
open Lean A12Kernel HavingFixture

private def fixture : FlatModel := {
  model with
  timeZoneId := "Europe/Berlin"
  fields := (model.fields.map fun field =>
    if field.id == 3 then { field with
      policy := { kind := .temporal .dateTime (TemporalComponents.ofFormat "yyyy-MM-dd'T'HH:mm:ss") }
      temporalTargetPolicy := some { format := "yyyy-MM-dd'T'HH:mm:ss" } }
    else field) ++ [
      { id := 6, groupPath := ["Form", "Sibling"], name := "Note",
        policy := { kind := .string }, repeatableScope := [20] }]
  repeatableGroups := model.repeatableGroups ++ [
    { level := 20, path := ["Form", "Sibling"], repeatability := some 3 }] }

private def filledRow : Json := Json.mkObj [("N", "7"), ("Tag", "2024-03-31T01:30:00")]

private def filter : String := "[Rows/N] > 0 Or [Rows/Tag] == \"31.03.2024T02:30:00\""

private def run (rows : Array Json) (siblings : Array Json := #[])
    (readSibling : Bool := false) (operationHead : String := "Sum(Rows*/N")
    (expected : String := "7") (condition : String := filter) : Option (Verdict × List String) :=
  runModel fixture condition readSibling "" "" ""
    (producerOperation := "FirstFilledValue(Sibling*/Note)")
    (extra := [("Sibling", Json.arr siblings)]) (ruleExpected := expected) (rowsOverride := some rows)
    (operationOverride := some (operationHead ++ " Having " ++ condition ++ ")"))

private def blanks : Array Json := #[Json.mkObj [], Json.mkObj [], Json.mkObj []]

-- KF528, peer 40a510808: the gap label separates visiting an absent coordinate from
-- skipping it. The sibling is unread by this computation, so its extent affects validation only.
example : run #[filledRow] = some (.fired .omission, ["value 7"]) ∧
    run #[filledRow, Json.mkObj [], Json.mkObj []] = some (.fired .value, []) := by
  native_decide

example : run #[] = some (.fired .value, []) := by native_decide

example : run #[filledRow] #[Json.mkObj [], Json.mkObj [], Json.mkObj []] =
    some (.fired .value, ["value 7"]) := by native_decide

example : run #[filledRow] blanks true = some (.fired .value, []) := by native_decide

example : [("Sum(Rows*/N", "7"), ("MaxValue(Rows*/N", "7"),
    ("MinValue(Rows*/N", "7"), ("FirstFilledValue(Rows*/N", "7"),
    ("NumberOfFilledFields(Rows*/N", "1"), ("NumberOfValueInFields(7 In Rows*/N", "1")].all
    (fun (operationHead, expected) =>
      run #[filledRow] #[] false operationHead expected == some (.fired .omission, ["value " ++ expected]) &&
      run #[] #[] false operationHead expected == some (.fired .value, []) &&
      run #[filledRow] blanks false operationHead expected == some (.fired .value, ["value " ++ expected]) &&
      run #[filledRow] blanks true operationHead expected == some (.fired .value, [])) = true := by native_decide

private def runGuard (operator : String) (rows siblings : Array Json) : Option (Verdict × List String) :=
  let guard := operator ++ "(Rows*/N Having " ++ filter ++ ")"
  runModel fixture filter false "" "" "" (extra := [("Sibling", Json.arr siblings)])
    (rowsOverride := some rows) (operationOverride := some "1")
    (ruleCondition := some ("FieldFilled(Error) And " ++ guard))

example : [("AtLeastOneFieldFilled", Verdict.fired .omission), ("NoFieldFilled", Verdict.unknown),
    ("FieldValuesNotUnique", Verdict.notFired)].all (fun (operator, control) =>
      runGuard operator #[filledRow] #[] == some (control, ["value 1"]) &&
      runGuard operator #[] #[] == some (.fired .value, ["value 1"]) &&
      runGuard operator #[filledRow] blanks == some (.fired .value, ["value 1"])) = true := by native_decide

private def nested : FlatModel := {
  fixture with
  fields := fixture.fields.map fun field => if field.repeatableScope == [10] then
    { field with groupPath := ["Form", "Shipments", "Items"], repeatableScope := [30, 10] }
    else field
  repeatableGroups := [
    { level := 30, path := ["Form", "Shipments"], repeatability := some 2 },
    { level := 10, path := ["Form", "Shipments", "Items"], repeatability := some 3 },
    { level := 20, path := ["Form", "Sibling"], repeatability := some 3 },
    { level := 40, path := ["Form", "Rows"], repeatability := some 3 }] }

private def shipment (items : Nat) : Json := Json.mkObj [("Items", Json.arr (Array.replicate items filledRow))]

private def runNested (shipments : Array Json) (siblings : Array Json := #[])
    (expected : String := "14") : Option (Verdict × List String) :=
  let condition := "[Shipments/Items/N] > 0 Or [Shipments/Items/Tag] == \"31.03.2024T02:30:00\""
  runModel nested condition false "" "" ""
    (extra := [("Shipments", Json.arr shipments), ("Sibling", Json.arr siblings)])
    (operationOverride := some ("Sum(Shipments*/Items*/N Having " ++ condition ++ ")"))
    (ruleExpected := expected) (rowsOverride := some #[])

example : runNested #[shipment 1, shipment 1] = some (.fired .omission, ["value 14"]) ∧
    runNested #[shipment 1, shipment 3] = some (.fired .value, []) := by native_decide

example : runNested #[shipment 1] #[Json.mkObj []] "7" = some (.fired .omission, ["value 7"]) ∧
    runNested #[shipment 1] blanks "7" = some (.fired .value, ["value 7"]) := by native_decide

-- CalculationCommand retains target ancestors even before the target's calculation runs.
example : (runModel fixture filter true "" "" "" (producerOperation := "\"ok\"")
    (producerTargetRelPath := "../Sibling/Note") (extra := [("Sibling", Json.arr blanks)])
    (rowsOverride := some #[filledRow]) (ruleExpected := "7")) =
      some (.fired .value, ["value ok", "value ok", "value ok"]) ∧
    (runModel fixture filter true "" "" "" (producerOperation := "\"ok\"")
      (producerTargetRelPath := "../Sibling/Note") (extra := [("Sibling", Json.arr #[Json.mkObj []])])
      (rowsOverride := some #[filledRow]) (ruleExpected := "7")) =
      some (.fired .omission, ["value 7", "value ok"]) := by native_decide

private def typedFixture : FlatModel := { fixture with fields := fixture.fields ++ [
  { id := 7, groupPath := ["Form", "Rows"], name := "Text", policy := { kind := .string }, repeatableScope := [10] },
  { id := 8, groupPath := ["Form", "Rows"], name := "Flag", policy := { kind := .boolean }, repeatableScope := [10] }] }

private def typedRow := Json.mkObj [("N", "7"), ("Tag", "2024-03-31T01:30:00"), ("Text", "keep"), ("Flag", "true")]

private def typedRun (model : FlatModel) (operationHead expected : String)
    (rows siblings : Array Json) (readSibling : Bool := false) : Option (Verdict × List String) :=
  runModel model filter readSibling "" "" "" (producerOperation := "FirstFilledValue(Sibling*/Note)")
    (extra := [("Sibling", Json.arr siblings)]) (rowsOverride := some rows)
    (operationOverride := some (operationHead ++ " Having " ++ filter ++ ")")) (ruleExpected := expected)

private def stringTarget : FlatModel := { typedFixture with fields := typedFixture.fields.map fun field =>
  if field.id == 5 then { field with policy := { kind := .string } } else field }

private def enumTarget : FlatModel := { typedFixture with fields := typedFixture.fields.map fun field =>
  if field.id == 5 || field.id == 7 then
    { field with policy := { kind := .enumeration }, enumeration := some { storedTokens := ["keep", "drop"] } }
  else field }

private def stampTarget : FlatModel := { typedFixture with fields := typedFixture.fields.map fun field =>
  if field.id == 5 then { field with
    policy := { kind := .temporal .dateTime (TemporalComponents.ofFormat "yyyy-MM-dd'T'HH:mm:ss") },
    temporalTargetPolicy := some { format := "yyyy-MM-dd'T'HH:mm:ss" } } else field }

example : [(typedFixture, "NumberOfDifferentValues(Rows*/Text", "1", "value 1"),
    (typedFixture, "NumberOfDifferentValues(Rows*/Tag", "1", "value 1"),
    (typedFixture, "NumberOfValueInFields(\"keep\" In Rows*/Text", "1", "value 1"),
    (typedFixture, "NumberOfValueInFields(True In Rows*/Flag", "1", "value 1"),
    (stringTarget, "FirstFilledValue(Rows*/Text", "\"keep\"", "value keep"),
    (enumTarget, "FirstFilledValue(Rows*/Text", "\"keep\"", "value keep"),
    (stampTarget, "FirstFilledValue(Rows*/Tag", "\"31.03.2024T01:30:00\"", "value 2024-03-31T01:30:00"),
    (stampTarget, "MaxValue(Rows*/Tag", "\"31.03.2024T01:30:00\"", "value 2024-03-31T01:30:00")].all
    (fun (model, operationHead, expected, output) =>
      typedRun model operationHead expected #[typedRow] #[] == some (.fired .omission, [output]) &&
      typedRun model operationHead expected #[] #[] == some (.fired .value, []) &&
      typedRun model operationHead expected #[typedRow] blanks == some (.fired .value, [output]) &&
      typedRun model operationHead expected #[typedRow] blanks true == some (.fired .value, [])) = true := by native_decide

private def rowPath : StarPath := { axes := [{ level := 10, repeatability := some 3 }], firstStar := 0 }

example : (fixture.filterEnvironments rowPath [] []).toOption = some [[(10, 1)]] ∧
    (fixture.filterEnvironments rowPath [{ group := 20, path := [8] }] []).toOption =
      some [[(10, 1)], [(10, 2)], [(10, 3)]] := by native_decide

private def fixedDepth : FlatModel := {
  fixture with
  fields := fixture.fields.map fun field => if field.id == 6 then
    { field with groupPath := ["Form", "Fixed", "Sibling"] } else field
  repeatableGroups := fixture.repeatableGroups.map fun group => if group.level == 20 then
    { group with path := ["Form", "Fixed", "Sibling"] } else group }

example : fixedDepth.validate.isOk = true ∧
    (fixedDepth.filterEnvironments rowPath [{ group := 20, path := [3] }] []).toOption = some [[(10, 1)]] := by native_decide

example : (match ({ axes := [{ level := 10, repeatability := some 101 }], firstStar := 0 } : StarPath).boundedFilterEnvironments [] (fun _ => 101) true with
    | .error .sparseFilterTraversalRequired => true
    | _ => false) = true := by native_decide

example : run #[] #[] false "NumberOfFilledFields(Rows*/N" "0" "FieldNotFilled(Rows/N)" =
    some (.fired .omission, ["value 0"]) := by native_decide

private def generatedCacheResult (head : String) (includeSibling : Bool) (siblingCount : Nat := 3) : Option NumericTargetCheckResult := do
  let dm : DmModel := { flat := fixture, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let raw ← (readDocument dm (Json.mkObj [("Form", Json.mkObj [
    ("Rows", Json.arr #[filledRow]), ("Sibling", Json.arr (Array.replicate siblingCount (Json.mkObj [])))])])).toOption
  if !raw.refusals.isEmpty then none
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler fixture).toOption
  let input ← (checkDocument prepared "en_US" raw.data).toOption
  let input := input.withComputationFilterRows fun field => includeSibling || field != 6
  let (_, .number parsed _) ← (lowerComputation fixture .english {
    group := ["Form"], name := "Generated", targetRelPath := "../Out", commonPrecondition := none,
    alternatives := [{ precondition := none, operation := head ++ "(Rows*/N Having " ++ filter ++ ")" }],
    errorCodesToSuppress := [] }).toOption | none
  let table : GeneratedComputationTable (CheckedNumericComputationOperation fixture)
      (CheckedComputationCondition fixture) := {
    targetField := 5, name := "Generated", alternatives := .singleton { operation := parsed.first.operation.operation },
    messagePlan := { parts := [] } }
  let admission ← (admitGeneratedNumericOperationTable fixture table (some world)).toOption
  pure (← (admission.executeAddressedTargetResultWithRead world input input.read).toOption).targetCheck

example : ["Sum", "MaxValue"].all (fun head =>
    generatedCacheResult head false 1 == some (.supported (.accepted { unscaled := 7, scale := 0 })) &&
    generatedCacheResult head false == some (.supported (.accepted { unscaled := 7, scale := 0 })) &&
    (generatedCacheResult head true).isNone) = true := by
  native_decide

private def sparseNested : FlatModel := { nested with
  repeatableGroups := nested.repeatableGroups.map fun group =>
    if group.level == 10 then { group with repeatability := some 51 } else group }

private def runSparseNested (firstRows : Nat) (operator : String := "Sum")
    (expected : String := toString ((firstRows + 1) * 7)) : Option (Verdict × List String) :=
  let condition := "[Shipments/Items/N] > 0 Or [Shipments/Items/Tag] == \"31.03.2024T02:30:00\""
  runModel sparseNested condition false "" "" ""
    (extra := [("Shipments", Json.arr #[shipment firstRows, shipment 1])])
    (operationOverride := some (operator ++ "(Shipments*/Items*/N Having " ++ condition ++ ")"))
    (ruleExpected := expected) (rowsOverride := some #[])

example : runSparseNested 50 = some (.fired .value, []) ∧
    runSparseNested 51 = some (.fired .omission, ["value 364"]) := by native_decide

example : [("Sum", "364"), ("MinValue", "7"), ("MaxValue", "7"),
    ("NumberOfDifferentValues", "1"), ("NumberOfFilledFields", "52")].all
    (fun (operator, expected) => runSparseNested 51 operator expected ==
      some (.fired .omission, ["value " ++ expected])) = true := by native_decide

private def sparseTyped (base : FlatModel) : FlatModel := { base with
  fields := base.fields.map fun field => if field.repeatableScope == [10] then
    { field with groupPath := ["Form", "Shipments", "Items"], repeatableScope := [30, 10] }
    else field
  repeatableGroups := sparseNested.repeatableGroups }

private def runSparseTyped (base : FlatModel) (head expected : String) (firstRows : Nat := 51) (validationOnly : Bool := false) : Option (Verdict × List String) :=
  let condition := "[Shipments/Items/N] > 0 Or [Shipments/Items/Tag] == \"31.03.2024T02:30:00\""
  let parent count := Json.mkObj [("Items", Json.arr (Array.replicate count typedRow))]
  let operation := head ++ " Having " ++ condition ++ ")"
  runModel (sparseTyped base) condition false "" "" ""
    (extra := [("Shipments", Json.arr #[parent firstRows, parent 1])])
    (operationOverride := some (if validationOnly then "1" else operation))
    (ruleCondition := if validationOnly then some ("FieldFilled(Error) And " ++ operation ++ " == " ++ expected) else none)
    (ruleExpected := expected) (rowsOverride := some #[])

example : [(typedFixture, "NumberOfDifferentValues(Shipments*/Items*/Text", "1", "value 1"),
    (typedFixture, "NumberOfDifferentValues(Shipments*/Items*/Tag", "1", "value 1"),
    (stampTarget, "MaxValue(Shipments*/Items*/Tag", "\"31.03.2024T01:30:00\"", "value 2024-03-31T01:30:00"),
    (stampTarget, "MinValue(Shipments*/Items*/Tag", "\"31.03.2024T01:30:00\"", "value 2024-03-31T01:30:00")].all
    (fun (model, head, expected, output) => runSparseTyped model head expected ==
      some (.fired .omission, [output])) = true := by native_decide

example : ["NumberOfValueInFields(7 In Shipments*/Items*/N",
    "NumberOfValueInFields(\"keep\" In Shipments*/Items*/Text",
    "NumberOfValueInFields(True In Shipments*/Items*/Flag"].all
    (fun head => runSparseTyped typedFixture head "2" 1 == some (.fired .omission, ["value 2"]) &&
      runSparseTyped typedFixture head "52" 51 == some (.fired .value, [])) = true := by native_decide

example : [(enumTarget, "FirstFilledValue(Shipments*/Items*/Text", "\"keep\"", "value keep"),
    (stampTarget, "FirstFilledValue(Shipments*/Items*/Tag", "\"31.03.2024T01:30:00\"", "value 2024-03-31T01:30:00")].all
    (fun (model, head, expected, output) =>
      runSparseTyped model head expected 1 == some (.fired .omission, [output]) &&
      runSparseTyped model head expected 51 == some (.fired .value, [output])) = true := by native_decide

example : runSparseTyped typedFixture "FirstFilledValue(Shipments*/Items*/Text" "\"keep\"" 1 true =
    some (.fired .omission, ["value 1"]) ∧
    runSparseTyped typedFixture "FirstFilledValue(Shipments*/Items*/Text" "\"keep\"" 51 true =
    some (.fired .value, ["value 1"]) := by native_decide

private def runSparseOverlap (yearless : Bool) (firstRows : Nat) (scalar : Bool := false) : Option (Verdict × List String) :=
  let base := { typedFixture with fields := typedFixture.fields ++ [{
    id := 9, groupPath := ["Form", "Rows"], name := "Span", repeatableScope := [10],
    policy := { kind := .dateRange },
    dateRangePolicy := some { format := if yearless then "MM-dd" else "yyyy-MM-dd", separator := "/" } },
    { id := 10, groupPath := ["Form"], name := "RootSpan", policy := { kind := .dateRange },
      dateRangePolicy := some { format := if yearless then "MM-dd" else "yyyy-MM-dd", separator := "/" } }] }
  let condition := "[Shipments/Items/N] > 0 Or [Shipments/Items/Tag] == \"31.03.2024T02:30:00\""
  let guard := (if scalar then "AtLeastOneDateRangeOverlaps(RootSpan In " else "DateRangesOverlap(") ++
    "Shipments*/Items*/Span Having " ++ condition ++ ")"
  let row (filled : Bool) := Json.mkObj [("N", "7"), ("Tag", "2024-03-31T01:30:00"),
    ("Span", Json.str (if !filled then "" else if yearless then "01-01/01-10" else "2024-01-01/2024-01-10"))]
  let parent count first := Json.mkObj [("Items", Json.arr ((List.range count).map
    (fun i => row (i == 0 && !(scalar && first)))).toArray)]
  runModel (sparseTyped base) condition false "" "" ""
    (extra := [("RootSpan", Json.str (if yearless then "01-01/01-10" else "2024-01-01/2024-01-10")),
      ("Shipments", Json.arr #[parent firstRows true, parent 1 false])])
    (operationOverride := some "1") (computationPrecondition := some guard)
    (ruleCondition := some ("FieldFilled(Error) And " ++ guard)) (rowsOverride := some #[])

example : [false, true].all (fun yearless =>
    runSparseOverlap yearless 1 == some (.fired .omission, ["value 1"]) &&
    runSparseOverlap yearless 50 == some (.fired .value, []) &&
    runSparseOverlap yearless 51 == some (.fired .value, [])) = true := by native_decide

example : [false, true].all (fun yearless =>
    runSparseOverlap yearless 1 true == some (.fired .omission, ["value 1"]) &&
    runSparseOverlap yearless 50 true == some (.fired .value, []) &&
    runSparseOverlap yearless 51 true == some (.fired .omission, ["value 1"])) = true := by native_decide

end A12Kernel.Dm.HavingTraversalLocks
