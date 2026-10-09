import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Document
import A12Kernel.Elaboration.GeneratedComputationValidation.Assembly
import A12Kernel.Elaboration.ValidationCondition.Reference

namespace A12Kernel.Dm.IndexedOverlapLocks

private def rangeField (id : FieldId) (name : String) : FlatFieldDecl := {
  id, name, groupPath := ["Form"], policy := { kind := .dateRange }
  dateRangePolicy := some { format := "yyyy-MM-dd", separator := "/" } }

private def model : FlatModel := {
  fields := [rangeField 1 "A", rangeField 2 "B",
    { id := 3, name := "Out", groupPath := ["Form"], policy := { kind := .number { scale := 0, signed := true } } },
    { id := 4, name := "Dependent", groupPath := ["Form"], policy := { kind := .number { scale := 0, signed := true } } },
    { id := 5, name := "Code", groupPath := ["Form", "Rows"], repeatableScope := [10],
      policy := { kind := .string }, stringPolicy := { maxLength := some 3 } },
    { rangeField 6 "Span" with groupPath := ["Form", "Rows"], repeatableScope := [10] },
    { id := 7, name := "Key", groupPath := ["Form"], policy := { kind := .string } },
    { id := 8, name := "Out", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .number { scale := 0, signed := true } } },
    { id := 9, name := "Dependent", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .number { scale := 0, signed := true } } },
    { rangeField 10 "R" with groupPath := ["Form", "Rows", "Ranges"], repeatableScope := [10] },
    { rangeField 11 "Span" with groupPath := ["Form", "Rows", "Children"], repeatableScope := [10,20] } ]
  repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 3, indexField := some 5 },
    { level := 20, path := ["Form", "Rows", "Children"], repeatability := some 2 }] }

private def january := "2024-01-01/2024-01-10"
private def touching := "2024-01-10/2024-01-20"

private def profileModel (format : String) (baseYear : Option Int := none)
    (selectedOnly := false) (separator : String := "/") : FlatModel := {
  model with
  baseYear := baseYear
  fields := model.fields.map fun field =>
    if field.dateRangePolicy.isSome && (!selectedOnly || field.id == 6) then
      { field with dateRangePolicy := some { format, separator } }
    else field }

private def input (span : String) (secondCode : String := "two") (key : String := "one")
    (testModel : FlatModel := model) (a : String := january) (b : String := touching)
    (secondSpan : String := "2024-03-01/2024-03-10") (children : List String := []) : Option (CheckedDocument testModel) := do
  let dm : DmModel := { flat := testModel, computations := [], rules := [], conditionLanguage := "en_US", refusals := [] }
  let data := Lean.Json.mkObj [("Form", Lean.Json.mkObj [
    ("A", .str a), ("B", .str b), ("Key", .str key), ("Out", .str "99"), ("Dependent", .str "99"),
    ("Rows", .arr #[
      Lean.Json.mkObj [("Code", .str "one"), ("Span", .str span),
        ("Ranges", Lean.Json.mkObj [("R", .str span)]),
        ("Children", .arr (children.map fun value => Lean.Json.mkObj [("Span", .str value)]).toArray), ("Out", .str "99"), ("Dependent", .str "99")],
      Lean.Json.mkObj [("Code", .str secondCode), ("Span", .str secondSpan), ("Ranges", Lean.Json.mkObj [("R", .str secondSpan)]), ("Out", .str "99"), ("Dependent", .str "99")]])])]
  let document ← (readDocument dm data).toOption
  if !document.refusals.isEmpty then none
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } } builtinStringPatternCompiler testModel).toOption
  (checkDocument prepared "en_US" document.data).toOption

private def validation (expression span : String) (secondCode : String := "two")
    (testModel : FlatModel := model) (a : String := january) (b : String := touching)
    (secondSpan : String := "2024-03-01/2024-03-10") (children : List String := []) : Option Verdict := do
  let document ← input span secondCode (testModel := testModel) (a := a) (b := b) (secondSpan := secondSpan) (children := children)
  let parsed ← (parseText .english expression).toOption
  let condition ← (lowerCondition testModel ["Form"] false parsed.body).toOption
  (condition.core.evalAddressed {
    scalar := { fields := document.flatContext, groups := GroupPresenceContext.unavailable }
    outer := [], input := .checked document }).toOption

private def computation (expression span : String) (secondCode : String := "two")
    (key : String := "one") (producer : Option (String × String) := none)
    (rowTarget := false) (testModel : FlatModel := model) (a : String := january)
    (b : String := touching) (secondSpan : String := "2024-03-01/2024-03-10")
    (children : List String := []) : Option (List String) := do
  let document ← input span secondCode key testModel a b secondSpan children
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } } builtinStringPatternCompiler testModel).toOption
  let consumer ← (lowerComputation testModel .english {
    name := "Consumer", group := ["Form"], targetRelPath := if rowTarget then "../Rows/Out" else "../Out", commonPrecondition := some expression
    alternatives := [{ precondition := none, operation := "1" }], errorCodesToSuppress := [] }).toOption
  let dependent ← (lowerComputation testModel .english {
    name := "Dependent", group := ["Form"], targetRelPath := if rowTarget then "../Rows/Dependent" else "../Dependent", commonPrecondition := none
    alternatives := [{ precondition := none, operation := if rowTarget then "[Rows/Out] + 1" else "[Out] + 1" }], errorCodesToSuppress := [] }).toOption
  let producers ← producer.toList.mapM fun (target, operation) =>
    (lowerComputation testModel .english {
      name := "Producer", group := ["Form"], targetRelPath := "../" ++ target, commonPrecondition := none,
      alternatives := [{ precondition := none, operation }], errorCodesToSuppress := [] }).toOption
  let results ← (runComputations { now := { epochMillis := 0 } } prepared document
    ([consumer.2, dependent.2] ++ producers.map (·.2))).toOption
  pure ((results.filter fun result => result.pointer.endsWith "/Out" || result.pointer.endsWith "/Dependent").map (·.outcome))

private def selected := "DateRangesOverlap(Rows/Span For \"one\", A)"
private def leadingMatch := "DateRangesOverlap(A, B, Rows/Span For \"one\")"
private def reached := "DateRangesOverlap(Rows/Span For \"one\", A, B)"
private def holds := some ["value 1", "value 2"]
private def misses := some ["cleared", "value 1"]
private def poisoned := some ["cleared", "cleared"]

example : model.validate.isOk = true ∧
    validation "DateRangesOverlap(A,B)" touching = some (.fired .value) ∧
    computation "DateRangesOverlap(A,B)" touching = holds := by native_decide

example : validation selected touching = some (.fired .value) ∧
    computation selected touching = holds ∧
    validation selected "bad" = some .notFired ∧
    computation selected "bad" = poisoned ∧
    validation selected "" = some .notFired ∧
    computation selected "" = misses := by native_decide

example : validation selected touching "long" = some (.fired .value) ∧
    computation selected touching "long" = poisoned ∧
    validation reached touching "one" = some (.fired .value) ∧
    computation reached touching "one" = poisoned ∧
    computation leadingMatch touching "one" = holds ∧
    computation "DateRangesOverlap(Rows/Span For \"nil\", A)" touching = misses := by native_decide

private def dynamic := "DateRangesOverlap(Rows/Span For Key, A)"

example : computation dynamic touching (key := "nil") = misses ∧
    computation dynamic touching (key := "nil") (producer := some ("Key", "\"one\"")) = holds ∧
    computation selected "bad" (producer := some ("Rows/Span", "FirstFilledValue(A,B)")) = holds ∧
    computation "DateRangesOverlap(Rows/Span For \"one\", Rows/Span)" touching
      (rowTarget := true) = some ["value 1", "cleared", "value 2", "value 1"] ∧
    computation "DateRangesOverlap(Rows/Span For \"one\", Rows/Span)" touching = none := by native_decide

private def generatedGuard (span : String) (expression : String := selected)
    (testModel : FlatModel := model) (a : String := january) (b : String := touching) : Option Bool := do
  let document ← input span (testModel := testModel) (a := a) (b := b)
  let parsed ← (parseText .english expression).toOption
  let surface ← (lowerGuard testModel ["Form"] false parsed.body (some ["Form"])).toOption
  let guard ← (testModel.elaborateCheckedComputationCondition ["Form"] ["Form"] surface).toOption
  let operation ← (elaborateCompleteNumericComputationOperation testModel ["Form"] 3
    (.literal { value := 1, authoredScale := 0 }) false).toOption
  let table : GeneratedComputationTable (CheckedNumericComputationOperation testModel) (CheckedComputationCondition testModel) := {
    targetField := 3, name := "Computed", commonPrecondition := some guard
    alternatives := .singleton { operation }, messagePlan := { parts := [] } }
  let rule ← (assembleGeneratedNumericOperationTableRule testModel table).toOption
  let outcome ← (rule.evalAddressedFull {
    scalar := { fields := document.flatContext, groups := GroupPresenceContext.unavailable }
    outer := [], input := .checked document } true).toOption
  pure (match outcome with | .fired _ => true | _ => false)

example : generatedGuard touching = some true ∧ generatedGuard "bad" = some false := by native_decide

private def references (expression : String := dynamic) : Option (List MessagePointer) := do
  let parsed ← (parseText .english expression).toOption
  let checked ← (lowerCondition model ["Form"] false parsed.body).toOption
  (checked.core.referencePointers [] (some {
    cache := { insertions := [{ group := 10, parentPath := [], key := .text "one", row := 1 }] }
    keyAt := fun address => if address.field == 7 then some (.text "one") else none })).toOption

example : references dynamic = some [
    { field := 7, coordinates := [] }, { field := 5, coordinates := [.concrete 1] },
    { field := 6, coordinates := [.concrete 1] }, { field := 1, coordinates := [] }] := by native_decide

private def pluralScalar := "AtLeastOneDateRangeOverlaps(Rows/Span For \"one\" In A,B)"
private def pluralList := "AtLeastOneDateRangeOverlaps(A In Rows/Span For \"one\",B)"
private def selectedPair := "DateRangesOverlap(Rows/Span For \"one\", Rows/Span For \"two\")"
private def pluralPair := "AtLeastOneDateRangeOverlaps(Rows/Span For \"one\" In Rows/Span For \"two\")"

example : validation pluralScalar touching = some (.fired .value) ∧
    computation pluralScalar touching = holds ∧
    validation pluralList touching = some (.fired .value) ∧
    computation pluralList touching = holds ∧
    validation selectedPair january (secondSpan := touching) = some (.fired .value) ∧
    computation selectedPair january (secondSpan := touching) = holds ∧
    validation pluralPair january (secondSpan := touching) = some (.fired .value) ∧
    computation pluralPair january (secondSpan := touching) = holds := by native_decide

example : validation pluralScalar "bad" = some .notFired ∧
    computation pluralScalar "bad" = poisoned ∧
    validation pluralScalar touching "long" = some (.fired .value) ∧
    computation pluralScalar touching "long" = poisoned ∧
    computation "AtLeastOneDateRangeOverlaps(Rows/Span For \"nil\" In Rows/Span For \"one\")" "bad" = misses ∧
    validation "AtLeastOneDateRangeOverlaps(A In Rows/Span For \"one\")" "bad" (a := "") = some .notFired ∧
    computation "AtLeastOneDateRangeOverlaps(A In Rows/Span For \"one\")" "bad" (a := "") = misses ∧
    computation pluralList touching "long" (a := "") = misses ∧
    computation "AtLeastOneDateRangeOverlaps(A In B,Rows/Span For \"one\")" "bad" = holds := by native_decide

private def profileControl (format : String) (baseYear : Option Int)
    (a b : String) (separator : String := "/") : Bool :=
  let testModel := profileModel format baseYear (separator := separator)
  testModel.validate.isOk &&
    ["DateRangesOverlap(A,B)", "AtLeastOneDateRangeOverlaps(A In B)"].all fun expression =>
      validation expression b (testModel := testModel) (a := a) (b := b) == some (.fired .value) &&
      computation expression b (testModel := testModel) (a := a) (b := b) == holds

private def selectedProfile (format : String) (baseYear : Option Int)
    (a b : String) (separator : String := "/") : Bool :=
  let testModel := profileModel format baseYear (separator := separator)
  [selected, pluralScalar, pluralList, selectedPair, pluralPair].all fun expression =>
    validation expression a (testModel := testModel) (a := a) (b := b) (secondSpan := b) == some (.fired .value) &&
    computation expression a (testModel := testModel) (a := a) (b := b) (secondSpan := b) == holds

example : profileControl "MM" none "01/02" "02/03" = true ∧
    profileControl "MM-dd" none "02-01/02-29" "02-29/03-01" = true ∧
    profileControl "yyyy" none "2024/2025" "2025/2026" = true ∧
    profileControl "yyyy-MM" none "2024-01/2024-02" "2024-02/2024-03" = true ∧
    profileControl "MM" (some 2024) "01/02" "02/03" = true ∧
    profileControl "MM-dd" (some 2024) "02-01/02-29" "02-29/03-01" = true := by native_decide

example : selectedProfile "MM" none "01/02" "02/03" = true ∧
    selectedProfile "MM-dd" none "02-01/02-29" "02-29/03-01" = true ∧
    selectedProfile "yyyy" none "2024/2025" "2025/2026" = true ∧
    selectedProfile "yyyy-MM" none "2024-01/2024-02" "2024-02/2024-03" = true ∧
    selectedProfile "MM" (some 2024) "01/02" "02/03" = true ∧
    selectedProfile "MM-dd" (some 2024) "02-01/02-29" "02-29/03-01" = true := by native_decide

example : profileControl "MM" none "0102" "0203" "" = true ∧
    selectedProfile "MM" none "0102" "0203" "" = true ∧
    profileControl "dd.MM" none "01.02-29.02" "29.02-01.03" "-" = true ∧
    selectedProfile "dd.MM" none "01.02-29.02" "29.02-01.03" "-" = true ∧
    profileControl "MM" (some 2024) "0102" "0203" "" = true ∧
    selectedProfile "MM" (some 2024) "0102" "0203" "" = true ∧
    profileControl "dd.MM" (some 2024) "01.02-29.02" "29.02-01.03" "-" = true ∧
    selectedProfile "dd.MM" (some 2024) "01.02-29.02" "29.02-01.03" "-" = true := by native_decide

example : validation pluralScalar "bad" (testModel := profileModel "MM") (a := "01/02") (b := "02/03") = some .notFired ∧
    computation pluralScalar "bad" (testModel := profileModel "MM") (a := "01/02") (b := "02/03") = poisoned ∧
    computation "AtLeastOneDateRangeOverlaps(A In Rows/Span For \"one\")" "bad"
      (testModel := profileModel "MM") (a := "") (b := "02/03") = misses ∧
    computation "AtLeastOneDateRangeOverlaps(Rows/Span For \"nil\" In Rows/Span For \"one\")" "bad"
      (testModel := profileModel "MM") (a := "01/02") (b := "02/03") = misses ∧
    computation "DateRangesOverlap(A,B,Rows/Span For \"one\")" "bad"
      (testModel := profileModel "MM") (a := "01/02") (b := "02/03") = holds := by native_decide

example : generatedGuard touching pluralScalar = some true ∧
    generatedGuard "bad" pluralScalar = some false ∧
    generatedGuard "01/02" pluralScalar (profileModel "MM") "01/02" "02/03" = some true ∧
    generatedGuard "bad" pluralScalar (profileModel "MM") "01/02" "02/03" = some false ∧
    computation "AtLeastOneDateRangeOverlaps(Rows/Span For Key In A)" touching
      (key := "nil") (producer := some ("Key", "\"one\"")) = holds ∧
    computation pluralScalar "bad" (producer := some ("Rows/Span", "FirstFilledValue(A,B)")) = holds ∧
    computation "AtLeastOneDateRangeOverlaps(Rows/Span For \"one\" In Rows/Span)" touching
      (rowTarget := true) = some ["value 1", "cleared", "value 2", "value 1"] ∧
    computation "AtLeastOneDateRangeOverlaps(Rows/Span For \"one\" In Rows/Span)" touching = none ∧
    references "AtLeastOneDateRangeOverlaps(Rows/Span For Key In A)" = some [
      { field := 7, coordinates := [] }, { field := 5, coordinates := [.concrete 1] },
      { field := 6, coordinates := [.concrete 1] }, { field := 1, coordinates := [] }] := by native_decide

private def admission (expression : String) (testModel : FlatModel := model) : Option String := do
  let parsed ← (parseText .english expression).toOption
  pure (match lowerCondition testModel ["Form"] false parsed.body with
    | .ok _ => "accepted"
    | .error error => error.detail)

example : admission selectedPair = some "accepted" ∧
    admission pluralPair = some "accepted" ∧
    admission "DateRangesOverlap(Rows/Span For \"one\", Rows/Span For \"one\")" =
      some "MVK_DUPLICATE_PARAM1" ∧
    admission "AtLeastOneDateRangeOverlaps(Rows/Span For \"one\" In Rows/Span For \"one\")" =
      some "MVK_DUPLICATE_PARAM1" ∧
    admission selected (profileModel "MM" none true) = some "MVK_DATE_WITH_AND_WITHOUT_YEAR" ∧
    admission "DateRangesOverlap(A, Rows/Span For \"one\")" (profileModel "MM" none true) =
      some "MVK_DATE_WITH_AND_WITHOUT_YEAR" ∧
    admission pluralScalar (profileModel "MM" none true) = some "MVK_DATE_WITH_AND_WITHOUT_YEAR" ∧
    admission pluralList (profileModel "MM" none true) = some "MVK_DATE_WITH_AND_WITHOUT_YEAR" ∧
    admission selected (profileModel "MM" (some 2024) true) = some "accepted" ∧
    admission "DateRangesOverlap(A, Rows/Span For \"one\")" (profileModel "MM" (some 2024) true) = some "accepted" ∧
    admission pluralScalar (profileModel "MM" (some 2024) true) = some "accepted" ∧
    admission pluralList (profileModel "MM" (some 2024) true) = some "accepted" := by native_decide

private def resolvedPlural (expression span : String)
    (secondSpan : String := "2024-03-01/2024-03-10") :
    Option (CheckedAtLeastOneDateRangeOverlapsResult model) := do
  let document ← input span (secondSpan := secondSpan)
  let parsed ← (parseText .english expression).toOption
  let .call _ [scalar] (some values) none := parsed.body | none
  let scalar ← (lowerEntityOperand model ["Form"] scalar).toOption
  let list ← (lowerEntitySource model ["Form"] values).toOption
  let source ← (elaborateAtLeastOneDateRangeOverlapsSource model ["Form"] { scalar, list }).toOption
  (source.evaluateCheckedDocument document []).toOption

example : (resolvedPlural "AtLeastOneDateRangeOverlaps(Rows/Span For \"two\" In A)" january touching).bind
      (fun result => match result.scalar.core with
        | .selected (.value cells) => some (
            result.source.scalarSelection?.map (·.targetDeclaration.id),
            result.scalar.selection?.map (·.targetDeclaration.id),
            cells.map fun cell => (cell.address.field, cell.address.path))
        | _ => none) = some (some 6, some 6, [(6, [2])]) ∧
    (resolvedPlural "AtLeastOneDateRangeOverlaps(Rows/Span For \"nil\" In Rows/Span For \"one\")" "bad").map
      (fun result => match result.scalar.core with
        | .selected .empty => result.scalar.selection?.isSome && result.operands.isEmpty
        | _ => false) = some true := by native_decide

private def selectedLower := "DateRangesOverlap(A, Rows/Children*/Span For \"one\")"
private def selectedGroup := "AtLeastOneDateRangeOverlaps(A In Rows/Ranges For \"one\")"

example : validation selectedLower touching (children := [touching]) = some (.fired .value) ∧
    computation selectedLower touching (children := [touching]) = holds ∧
    computation selectedLower touching (children := [touching, "bad"]) = holds ∧
    computation selectedLower touching (children := ["2024-03-01/2024-03-10", "bad"]) = poisoned ∧
    validation selectedLower touching (children := ["bad", touching]) = some (.fired .value) ∧
    computation selectedLower touching (children := ["bad", touching]) = poisoned ∧
    computation selectedLower touching = misses := by native_decide

example : validation selectedGroup touching = some (.fired .value) ∧
    computation selectedGroup touching = holds ∧
    computation selectedGroup "bad" = poisoned ∧
    computation selectedGroup "bad" (a := "") = misses ∧
    computation selectedGroup touching "long" = poisoned ∧
    validation selectedGroup touching "long" = some (.fired .value) := by native_decide

example : admission "DateRangesOverlap(A, Rows/Ranges For \"one\")" = some "MVK_NO_GROUPS_ALLOWED" ∧
    admission "AtLeastOneDateRangeOverlaps(Rows/Ranges For \"one\" In A)" =
      some "MVK_INVALID_PARAMETER_FOR_DATE_RANGE_COMPARISON" ∧
    admission "AtLeastOneDateRangeOverlaps(Rows/Children*/Span For \"one\" In A)" =
      some "MVK_INVALID_PARAMETER_FOR_DATE_RANGE_COMPARISON" := by native_decide

example : validation selectedGroup "02/03" (testModel := profileModel "MM") (a := "01/02") (b := "02/03") = some (.fired .value) ∧
    computation selectedGroup "02/03" (testModel := profileModel "MM") (a := "01/02") (b := "02/03") = holds ∧
    validation selectedLower "" (testModel := profileModel "MM") (a := "01/02") (b := "02/03")
      (children := ["bad", "02/03"]) = some (.fired .value) ∧
    computation selectedLower "" (testModel := profileModel "MM") (a := "01/02") (b := "02/03")
      (children := ["02/03", "bad"]) = holds ∧
    computation selectedLower "" (testModel := profileModel "MM") (a := "01/02") (b := "02/03")
      (children := ["03/04", "bad"]) = poisoned := by native_decide

example : computation "AtLeastOneDateRangeOverlaps(A In Rows/Ranges For Key)" touching
      (key := "nil") (producer := some ("Key", "\"one\"")) = holds ∧
    computation selectedGroup "bad" (producer := some ("Rows/Ranges/R", "FirstFilledValue(A,B)")) = holds ∧
    computation selectedLower "bad" (children := ["bad", "bad"])
      (producer := some ("Rows/Children/Span", "FirstFilledValue(A,B)")) = holds ∧
    computation "AtLeastOneDateRangeOverlaps(Rows/Span In Rows/Ranges For \"one\")" touching
      (rowTarget := true) = some ["value 1", "cleared", "value 2", "value 1"] ∧
    computation "AtLeastOneDateRangeOverlaps(Rows/Span In Rows/Ranges For \"one\")" touching = none ∧
    generatedGuard touching selectedGroup = some true ∧
    generatedGuard "bad" selectedGroup = some false ∧
    references "AtLeastOneDateRangeOverlaps(A In Rows/Ranges For Key)" = some [
      { field := 1, coordinates := [] }, { field := 7, coordinates := [] },
      { field := 5, coordinates := [.concrete 1] }, { field := 10, coordinates := [.concrete 1] }] ∧
    references selectedLower = some [
      { field := 1, coordinates := [] }, { field := 5, coordinates := [.concrete 1] },
      { field := 11, coordinates := [.concrete 1, .wildcard] }] := by native_decide

private def yearlessExtents : FlatModel := { model with fields := model.fields.map fun field =>
  if field.id == 10 || field.id == 11 then
    { field with dateRangePolicy := some { format := "MM", separator := "/" } }
  else field }

example : admission selectedGroup = some "accepted" ∧ admission selectedLower = some "accepted" ∧
    admission selectedGroup (profileModel "MM") = some "accepted" ∧
    admission selectedLower (profileModel "MM") = some "accepted" ∧
    admission selectedGroup yearlessExtents = some "MVK_DATE_WITH_AND_WITHOUT_YEAR" ∧
    admission selectedLower yearlessExtents = some "MVK_DATE_WITH_AND_WITHOUT_YEAR" ∧
    admission "AtLeastOneDateRangeOverlaps(A In Rows/Ranges For \"one\", Rows/Ranges For \"two\")" = some "accepted" ∧
    admission "AtLeastOneDateRangeOverlaps(A In Rows/Ranges For \"one\", Rows/Ranges For \"one\")" =
      some "MVK_DUPLICATE_PARAM1" := by native_decide

end A12Kernel.Dm.IndexedOverlapLocks
