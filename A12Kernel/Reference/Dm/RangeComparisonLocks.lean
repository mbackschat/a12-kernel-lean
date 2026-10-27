import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Document
import A12Kernel.Elaboration.GeneratedComputationValidation.Assembly
import A12Kernel.Elaboration.ValidationCondition.Reference

namespace A12Kernel.Dm.RangeComparisonLocks

private def model (yearless : Bool := false) (repeated : Bool := false) : FlatModel :=
  let format := if yearless then "MM-dd" else "yyyy-MM-dd"
  let date (id : FieldId) (name : String) : FlatFieldDecl := {
    id, name, groupPath := ["Form"], policy := { kind := .temporal .date (TemporalComponents.ofFormat format) }
    temporalTargetPolicy := some { format } }
  let fields := [date 1 "Start", date 2 "Finish",
      { id := 3, name := "Range", groupPath := ["Form"], policy := { kind := .dateRange }
        dateRangePolicy := some { format, separator := "/" } },
      { id := 4, name := "Out", groupPath := ["Form"], policy := { kind := .number { scale := 0, signed := true } } },
      { id := 5, name := "After", groupPath := ["Form"], policy := { kind := .number { scale := 0, signed := true } } },
      { id := 6, name := "Anchor", groupPath := ["Form"], policy := { kind := .number { scale := 0, signed := true } } }]
  { fields := fields.map fun field => if repeated then { field with groupPath := ["Form", "Rows"], repeatableScope := [10] } else field
    repeatableGroups := if repeated then [{ level := 10, path := ["Form", "Rows"], repeatability := some 2 }] else [] }

private def run (condition : String) (yearless : Bool := false)
    (start : String := "2024-01-01") (finish : String := "2024-01-03")
    (range : String := "2024-01-01/2024-01-03")
    (producer : Option (String × String) := none) (repeated : Bool := false)
    (generated : Bool := false) (omitted : List String := [])
    (second : Option (String × String × String) := none) (swapRows : Bool := false)
    (rowIndex : Nat := 1) (withPointers : Bool := false) : Option (Verdict × List String) := do
  let model := model yearless repeated
  let group := if repeated then ["Form", "Rows"] else ["Form"]
  let text := fun value => if yearless then value.replace "2024-" "" else value
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let values := fun start finish range => Lean.Json.mkObj ([("Start", .str (text start)), ("Finish", .str (text finish)),
      ("Range", .str (text range)), ("Out", .str "99"), ("After", .str "99"), ("Anchor", .str "99")].filter
        (fun (key, _) => !omitted.contains key))
  let rows := [values start finish range] ++ second.toList.map fun (start, finish, range) => values start finish range
  let rows := if swapRows then rows.reverse else rows
  let document ← (readDocument { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
    (Lean.Json.mkObj [("Form", if repeated then Lean.Json.mkObj [("Rows", .arr rows.toArray)] else values start finish range)])).toOption
  if !document.refusals.isEmpty then none
  let input ← (checkDocument prepared "en_US" document.data).toOption
  let parsed ← (parseText .english condition).toOption
  let checked ← (lowerCondition model group false parsed.body world).toOption
  let context : AddressedValidationEvaluationContext model := {
    scalar := { fields := input.flatContext, groups := GroupPresenceContext.unavailable }
    outer := if repeated then [(10, rowIndex)] else [], input := .checked input }
  let verdict ← if generated then do
      let surface ← (lowerGuard model group false parsed.body (some group)).toOption
      let guard ← (model.elaborateCheckedComputationCondition group group surface).toOption
      let operation ← (elaborateCompleteNumericComputationOperation model group 4
        (.literal { value := 1, authoredScale := 0 }) false).toOption
      let table : GeneratedComputationTable (CheckedNumericComputationOperation model) (CheckedComputationCondition model) := {
        targetField := 4, name := "Computed", commonPrecondition := some guard
        alternatives := .singleton { operation }, messagePlan := { parts := [] } }
      let rule ← (assembleGeneratedNumericOperationTableRule model table).toOption
      pure (← (rule.evalAddressedFull context true).toOption).verdict
    else (checked.core.evalAddressed context).toOption
  let consumer ← (lowerComputation model .english {
    name := "Consumer", group, targetRelPath := "../Out", commonPrecondition := some condition
    alternatives := [{ precondition := none, operation := "1" }], errorCodesToSuppress := [] }).toOption
  let dependent ← (lowerComputation model .english {
    name := "After", group, targetRelPath := "../After", commonPrecondition := none
    alternatives := [{ precondition := none, operation := "[Out] + 1" }], errorCodesToSuppress := [] }).toOption
  let producers ← producer.toList.mapM fun (target, operation) =>
    (lowerComputation model .english {
      name := "Producer", group, targetRelPath := "../" ++ target, commonPrecondition := none
      alternatives := [{ precondition := none, operation }], errorCodesToSuppress := [] }).toOption
  let results ← (runComputations world prepared input
    ([consumer.2, dependent.2] ++ producers.map (·.2))).toOption
  let results := results.filter fun result => result.pointer.endsWith "/Out" || result.pointer.endsWith "/After"
  pure (verdict, if withPointers then (results.map fun result => result.pointer ++ "=" ++ result.outcome).mergeSort (· ≤ ·)
    else results.map (·.outcome))

private def predicates := ["DateRange(Start,Finish) == [Range]", "[Range] == DateRange(Start,Finish)",
  "DateRange(Start,Finish) == DateRange(Start,Finish)", "[Range] == [Range]"]

private def holds := ["value 1", "value 2"]
private def misses := ["cleared", "value 1"]
private def poisoned := ["cleared", "cleared"]

example : [false, true].all (fun yearless => predicates.all (fun condition =>
    run condition yearless == some (.fired .value, holds) &&
    run (condition.replace "==" "!=") yearless == some (.notFired, misses))) = true := by native_decide

private def mixed := predicates.take 2

example : [false, true].all (fun yearless => mixed.all (fun condition =>
    run condition yearless (range := "2024-01-02/2024-01-03") == some (.notFired, misses) &&
    run (condition.replace "==" "!=") yearless (range := "2024-01-02/2024-01-03") ==
      some (.fired .value, holds))) = true := by native_decide

example : [false, true].all (fun yearless =>
    run "DateRange(Start,Finish) == DateRange(Finish,Start)" yearless == some (.notFired, misses) &&
    run "DateRange(Start,Finish) != DateRange(Finish,Start)" yearless == some (.fired .value, holds) &&
    run "DateRange(Finish,Start) == DateRange(Finish,Start)" yearless == some (.fired .value, holds)) =
    true := by native_decide

private def mixedStates : List (String × String × String × Verdict × List String) := [
  ("", "2024-01-03", "2024-01-01/2024-01-03", .notFired, misses),
  ("2024-01-01", "", "2024-01-01/2024-01-03", .notFired, misses),
  ("2024-01-01", "2024-01-03", "", .notFired, misses),
  ("bad", "2024-01-03", "2024-01-01/2024-01-03", .unknown, poisoned),
  ("2024-01-01", "bad", "2024-01-01/2024-01-03", .unknown, poisoned),
  ("2024-01-01", "2024-01-03", "bad", .unknown, poisoned),
  ("", "bad", "2024-01-01/2024-01-03", .unknown, poisoned),
  ("", "2024-01-03", "bad", .unknown, poisoned),
  ("2024-01-01", "", "bad", .unknown, poisoned),
  ("bad", "2024-01-03", "", .unknown, poisoned)]

-- Empty operands still reach a malformed partner; the retained range-family capture also
-- separates an empty start from its malformed finish (spec/05 §8, 2026-10-08).
example : [false, true].all (fun yearless => mixed.all (fun condition =>
    [condition, condition.replace "==" "!="].all (fun condition =>
      mixedStates.all (fun (start, finish, range, verdict, outcomes) =>
        run condition yearless start finish range == some (verdict, outcomes))))) = true := by native_decide

example : [false, true].all (fun yearless =>
    [predicates[2]!, predicates[2]!.replace "==" "!="].all (fun condition =>
      [("", "2024-01-03", Verdict.notFired, misses),
       ("2024-01-01", "", .notFired, misses), ("bad", "2024-01-03", .unknown, poisoned),
       ("2024-01-01", "bad", .unknown, poisoned), ("", "bad", .unknown, poisoned)].all
        (fun (start, finish, verdict, outcomes) =>
          run condition yearless start finish == some (verdict, outcomes))) &&
    [predicates[3]!, predicates[3]!.replace "==" "!="].all (fun condition =>
      run condition yearless (range := "") == some (.notFired, misses) &&
      run condition yearless (range := "bad") == some (.unknown, poisoned))) = true := by native_decide

example : [false, true].all (fun yearless => predicates.all (fun condition =>
    ["FieldFilled(Anchor) And (" ++ condition ++ ")", "(" ++ condition ++ ") And FieldFilled(Anchor)"].all
      (fun conjunction => run conjunction yearless == some (.fired .value, holds)) &&
    run ("FieldFilled(Anchor) And (" ++ condition.replace "==" "!=" ++ ")") yearless ==
      some (.notFired, misses))) = true := by native_decide

example : [false, true].all (fun yearless => mixed.all (fun condition =>
    run ("FieldFilled(Anchor) And (" ++ condition ++ ")") yearless (start := "bad") ==
      some (.unknown, poisoned) &&
    run ("FieldFilled(Anchor) Or (" ++ condition ++ ")") yearless (start := "bad") ==
      some (.fired .value, holds) &&
    run ("(" ++ condition ++ ") Or FieldFilled(Anchor)") yearless (start := "bad") ==
      some (.fired .value, poisoned) &&
    run ("(" ++ condition ++ ") Or FieldFilled(Anchor)") yearless (start := "") ==
      some (.fired .value, holds) &&
    run ("FieldNotFilled(Anchor) And (" ++ condition ++ ")") yearless (start := "bad") ==
      some (.notFired, misses) &&
    run ("FieldNotFilled(Anchor) Or (" ++ condition ++ ")") yearless (start := "bad") ==
      some (.unknown, poisoned))) = true := by native_decide

private def admission (condition : String) (testModel : FlatModel := model) : Option (Bool × Bool) := do
  let parsed ← (parseText .english condition).toOption
  let validation := (lowerCondition testModel ["Form"] false parsed.body).isOk
  let computation := (lowerComputation testModel .english {
      name := "Consumer", group := ["Form"], targetRelPath := "../Out", commonPrecondition := some condition
      alternatives := [{ precondition := none, operation := "1" }], errorCodesToSuppress := [] }).isOk
  pure (validation, computation)

private def endpointFormat (field : FieldId) (format : String) : FlatModel := {
  model with fields := model.fields.map fun declaration =>
    if declaration.id == field then { declaration with
      policy := { kind := .temporal .date (TemporalComponents.ofFormat format) }
      temporalTargetPolicy := some { format } }
    else declaration }

private def rangeFormat (format : String) : FlatModel := {
  model with fields := model.fields.map fun declaration =>
    if declaration.id == 3 then { declaration with dateRangePolicy := some { format, separator := "/" } }
    else declaration }

-- The producer is authored after its consumers, so these locks separate scheduled current-cell
-- reads from original-document reads (spec/09 §2); the original validation read stays unknown.
example : mixed.all (fun condition =>
    run condition (start := "bad") (producer := some ("Start", "Date(\"1\",\"1\",\"2024\")")) ==
      some (.unknown, holds) &&
    run condition (finish := "bad") (producer := some ("Finish", "Date(\"3\",\"1\",\"2024\")")) ==
      some (.unknown, holds) &&
    run condition (range := "bad") (producer := some ("Range", "DateRange(Start,Finish)")) ==
      some (.unknown, holds)) = true := by native_decide

example : model.validate.isOk = true ∧
    [false, true].all (fun yearless => predicates.all (fun condition =>
      admission condition (model yearless) == some (true, true))) = true ∧
    -- A bare name as a comparison side is a parse defect (spec/12 §3.2), refused before lowering.
    ["DateRange(Start,Finish) == Range", "Range == DateRange(Start,Finish)"].all
      (fun condition => admission condition == none) = true ∧
    ["DateRange([Start],Finish) == [Range]", "DateRange(Start,[Finish]) == [Range]",
     "DateRange(Start,Finish) < [Range]", "[Range] > DateRange(Start,Finish)",
     "DateRange(Start,Finish) <= DateRange(Start,Finish)", "[Range] >= [Range]",
     "DateRange(Out,Finish) == [Range]", "DateRange(Start,Finish) == [Out]",
     "DateRange(Start,Finish) == DateRange(Start,Out)"].all
      (fun condition => admission condition == some (false, false)) = true := by native_decide

example : [endpointFormat 2 "yyyy-MM", endpointFormat 1 "HH:mm:ss", rangeFormat "MM-dd"].all
    (fun testModel => testModel.validate.isOk &&
      mixed.all (fun condition => admission condition testModel == some (false, false))) = true ∧
    admission "DateRange(Start,Finish) == DateRange(Finish,Start)" = some (true, true) := by native_decide

example : [false, true].all (fun yearless => predicates.all (fun condition =>
    run condition yearless (repeated := true) == some (.fired .value, holds) &&
    run condition yearless (generated := true) == some (.fired .value, holds))) = true := by native_decide

example : [false, true].all (fun yearless => mixed.all (fun condition =>
    run condition yearless (start := "") (repeated := true) == some (.notFired, misses) &&
    run condition yearless (start := "bad") (repeated := true) == some (.unknown, poisoned) &&
    run ("(" ++ condition ++ ") Or FieldFilled(Anchor)") yearless (start := "bad")
      (generated := true) == some (.fired .value, poisoned) &&
    run condition yearless (range := "bad") (producer := some ("Range", "DateRange(Start,Finish)")) ==
      some (.unknown, holds))) = true := by native_decide

private def scopedAdmission (condition : String) (bound : Bool) : Option (Bool × Bool) := do
  let source : FlatModel := { model false true with fields := (model false true).fields ++ [
    { id := 7, name := "RootOut", groupPath := ["Form"], policy := { kind := .number { scale := 0, signed := true } } }] }
  let expression := condition.replace "Start" "Rows/Start" |>.replace "Finish" "Rows/Finish" |>.replace "Range]" "Rows/Range]"
  let parsed ← (parseText .english expression).toOption
  let binding := if bound then ["Form", "Rows"] else ["Form"]
  let validation := (lowerCondition source ["Form"] false parsed.body (bindingGroup := binding)).isOk
  let computation := (lowerComputation source .english {
    name := "Consumer", group := ["Form"], targetRelPath := if bound then "../Rows/Out" else "../RootOut"
    commonPrecondition := some expression, alternatives := [{ precondition := none, operation := "1" }]
    errorCodesToSuppress := [] }).isOk
  pure (validation, computation)

example : predicates.all (fun condition => scopedAdmission condition true == some (true, true) &&
    scopedAdmission condition false == some (false, false)) = true := by native_decide

example : [false, true].all (fun yearless => mixed.all (fun condition =>
    [condition, condition.replace "==" "!="].all (fun condition =>
      ["Start", "Finish", "Range"].all (fun field =>
        run condition yearless (omitted := [field]) == some (.notFired, misses)) &&
      run condition yearless (finish := "bad") (omitted := ["Start"]) == some (.unknown, poisoned) &&
      run condition yearless (range := "bad") (omitted := ["Finish"]) == some (.unknown, poisoned)))) = true := by native_decide

private def rowOutcomes (swapped : Bool) : List String :=
  ["Form/Rows/After=" ++ (if swapped then "value 1" else "value 2"),
   "Form/Rows/Out=" ++ (if swapped then "cleared" else "value 1"),
   "Form/Rows[2]/After=" ++ (if swapped then "value 2" else "value 1"),
   "Form/Rows[2]/Out=" ++ (if swapped then "value 1" else "cleared")]

example : [false, true].all (fun yearless => mixed.all (fun condition =>
    [false, true].all (fun swapped => [1, 2].all fun row =>
      run condition yearless (repeated := true)
        (second := some ("2024-02-01", "2024-02-03", "2024-02-02/2024-02-03"))
        (swapRows := swapped) (rowIndex := row) (withPointers := true) ==
          some ((if (row == 1) != swapped then .fired .value else .notFired), rowOutcomes swapped)))) = true := by native_decide

example : [false, true].all (fun yearless => [false, true].all (fun swapped => [1, 2].all fun row =>
    run "DateRange(Start,Finish) == DateRange(Start,Start)" yearless
      (finish := "2024-01-01") (repeated := true)
      (second := some ("2024-02-01", "2024-02-03", "2024-02-01/2024-02-03"))
      (swapRows := swapped) (rowIndex := row) (withPointers := true) ==
        some ((if (row == 1) != swapped then .fired .value else .notFired), rowOutcomes swapped))) = true := by native_decide

end A12Kernel.Dm.RangeComparisonLocks
