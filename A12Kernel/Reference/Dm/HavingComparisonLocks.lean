import A12Kernel.Reference.Dm.Replay
import A12Kernel.Reference.Dm.LowerDocument
import A12Kernel.Reference.Dm.Compute

namespace A12Kernel.Dm.HavingComparisonLocks
open Lean A12Kernel

private def model : FlatModel := {
  fields := [
    { id := 1, groupPath := ["Form"], name := "Error", policy := { kind := .string } },
    { id := 2, groupPath := ["Form"], name := "Expected", policy := { kind := .string } },
    { id := 3, groupPath := ["Form", "Rows"], name := "Tag", policy := { kind := .string }, repeatableScope := [10] },
    { id := 4, groupPath := ["Form", "Rows"], name := "N", policy := { kind := .number { scale := 0, signed := true } }, repeatableScope := [10] },
    { id := 5, groupPath := ["Form"], name := "Out", policy := { kind := .number { scale := 0, signed := true } } }]
  repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 3 }] }

private def runModel (model : FlatModel) (filter : String) (fresh : Bool)
    (expected first second : String) : Option (Verdict × List String) := do
  let dm : DmModel := {
    flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let row := fun (tag n : String) => Json.mkObj [("Tag", Json.str tag), ("N", Json.str n)]
  let input ← (readDocument dm (Json.mkObj [("Form", Json.mkObj [
    ("Error", Json.str "ready"), ("Expected", Json.str expected),
    ("Rows", Json.arr #[row first "2", row second "5", row first "7"])])])).toOption
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let document ← (checkDocument prepared "en_US" input.data).toOption
  let operation := "Sum(Rows*/N Having " ++ filter ++ ")"
  let rule ← (checkRule dm .english {
    group := ["Form"], name := "Selected", errorCode := "SELECTED", errorEntityRelPath := "../Error",
    condition := "FieldFilled(Error) And " ++ operation ++ " == 9", severity := "ERROR" }).toOption
  let context : AddressedValidationEvaluationContext model := {
    scalar := { fields := document.flatContext.withWorld world, groups := GroupPresenceContext.unavailable }
    outer := [], input := .checked document }
  let verdict := (← (rule.evalAddressedFull context true).toOption).verdict
  let (_, computation) ← (lowerComputation model .english {
    group := ["Form"], name := "Total", targetRelPath := "../Out", commonPrecondition := none,
    alternatives := [{ precondition := none, operation }], errorCodesToSuppress := [] }).toOption
  let computations ← if fresh then do
      let (_, producer) ← (lowerComputation model .english {
        group := ["Form"], name := "Expected", targetRelPath := "../Expected", commonPrecondition := none,
        alternatives := [{ precondition := none, operation := "\"drop\"" }], errorCodesToSuppress := [] }).toOption
      pure [computation, producer]
    else pure [computation]
  let outcomes ← (runComputations world prepared document computations).toOption
  pure (verdict, outcomes.map (·.outcome))

private def run (filter : String) (fresh : Bool := false)
    (kind : FieldKind := .string) (expected : String := "keep")
    (first : String := "keep") (second : String := "drop")
    (enumeration : Option EnumerationDeclaration := none) : Option (Verdict × List String) :=
  runModel { model with fields := model.fields.map fun field =>
    if field.id == 2 || field.id == 3 then { field with policy := { kind }, enumeration } else field }
    filter fresh expected first second

example : run "[Rows/Tag] == [$Expected]" = some (.fired .omission, ["value 9"]) ∧
    run "[$Expected] == [Rows/Tag]" = some (.fired .omission, ["value 9"]) ∧
    run "[Rows/Tag] != [$Expected]" = some (.notFired, ["value 5"]) := by native_decide

example : (run "[Rows/Tag] == [$Expected]" true).map (·.2) = some ["value drop", "value 5"] := by native_decide

example : run "[Rows/Tag] == [$Expected]" false .boolean "false" "false" "true" =
      some (.fired .omission, ["value 9"]) ∧
    run "[Rows/Tag] == False" false .boolean "true" "false" "true" =
      some (.fired .omission, ["value 9"]) ∧
    run "True != [Rows/Tag]" false .confirm "true" "" "true" =
      some (.fired .omission, ["value 9"]) := by native_decide

private def domain : EnumerationDeclaration := {
  storedTokens := ["keep", "drop"], categories := [{ name := "Swap", tokens := ["drop", "keep"] }] }

example : run "[Rows/Tag] == [$Expected]" false .enumeration "keep" "keep" "drop" (some domain) =
      some (.fired .omission, ["value 9"]) ∧
    run "[Rows/Tag -> Swap] == [$Expected]" false .enumeration "keep" "keep" "drop" (some domain) =
      some (.notFired, ["value 5"]) ∧
    run "[Rows/Tag -> Swap] == [$Expected -> Swap]" false .enumeration "keep" "keep" "drop" (some domain) =
      some (.fired .omission, ["value 9"]) := by native_decide


example : run "[Rows/Tag] == False" false .confirm "true" "true" "" = none ∧
    run "[Rows/Tag] == [$Expected]" false .confirm "true" "true" "" = none ∧
    run "[Rows/Tag] != [$Expected]" false .confirm "true" "" "true" =
      some (.fired .omission, ["value 9"]) ∧
    run "[Rows/Tag] == False" false .boolean "false" "bad" "false" =
      some (.notFired, []) := by native_decide

private def references : Option (Bool × Bool) := do
  let parsed ← (parseText .english
    "FieldValuesNotUnique(/Form/Rows*/Tag Having [/Form/Rows/Tag] == [$/Form/Rows/Tag])").toOption
  let checked ← (lowerCondition model ["Form", "Rows"] false parsed.body).toOption
  let pointers ← (checked.core.referencePointers [(10, 2)]).toOption
  pure (pointers.contains { field := 3, coordinates := [.wildcard] },
    pointers.contains { field := 3, coordinates := [.concrete 2] })

example : references = some (true, true) := by native_decide

private def temporalRun (filter : String) (leftKind rightKind : TemporalKind)
    (leftFormat rightFormat expected first second : String)
    (partialMode : TemporalPartialMode := .full) : Option (Verdict × List String) :=
  let fields := model.fields.map fun field =>
    if field.id == 2 || field.id == 3 then
      let kind := if field.id == 3 then leftKind else rightKind
      let format := if field.id == 3 then leftFormat else rightFormat
      { field with
        policy := { kind := .temporal kind (TemporalComponents.ofFormat format) }
        temporalTargetPolicy := some { format, partialMode } }
    else field
  runModel { model with fields } filter false expected first second

private def dateRun (filter : String) (first : String := "2024-01-01") := temporalRun filter .date .date
  "yyyy-MM-dd" "yyyy-MM-dd" "2024-01-02" first "2024-01-03"

example : ["==", "!=", "<", "<=", ">", ">="].map (fun op =>
    (dateRun ("[Rows/Tag] " ++ op ++ " [$Expected]")).map (·.2)) =
      [some ["value 0"], some ["value 14"], some ["value 9"], some ["value 9"],
       some ["value 5"], some ["value 5"]] ∧
    (dateRun "[$Expected] < [Rows/Tag]").map (·.2) = some ["value 5"] ∧
    (dateRun "[Rows/Tag] < [$Expected]").map (·.1) = some (.fired .omission) := by native_decide

example : ["==", "!=", "<", "<=", ">", ">="].map (fun op =>
    dateRun ("[Rows/Tag] " ++ op ++ " [$Expected]") "2024-01-02") =
      [some (.fired .omission, ["value 9"]), some (.notFired, ["value 5"]),
       some (.notFired, ["value 0"]), some (.fired .omission, ["value 9"]),
       some (.notFired, ["value 5"]), some (.notFired, ["value 14"])] := by native_decide

example : [TemporalKind.date, .dateTime, .time].all (fun kind =>
    temporalRun "[Rows/Tag] == [$Expected]" kind kind "HH:mm:ss" "HH:mm:ss"
      "12:30:00" "12:30:00" "15:30:00" == some (.fired .omission, ["value 9"])) = true := by native_decide

example : temporalRun "[Rows/Tag] < [$Expected]" .date .dateTime
    "yyyy-MM-dd" "yyyy-MM-dd'T'HH:mm:ss" "2024-01-02T12:00:00" "2024-01-01" "2024-01-03" =
      some (.fired .omission, ["value 9"]) ∧
    temporalRun "[Rows/Tag] == [$Expected]" .date .dateTime
    "yyyy-MM-dd" "yyyy-MM-dd'T'HH:mm:ss" "2024-01-02T12:00:00" "2024-01-01" "2024-01-03" = none ∧
    temporalRun "[Rows/Tag] < [$Expected]" .date .time
    "yyyy-MM-dd" "HH:mm:ss" "12:00:00" "2024-01-01" "2024-01-03" = none ∧
    temporalRun "[Rows/Tag] == [$Expected]" .date .date
    "yyyy-MM-dd" "yyyy-MM-dd" "2024-01-02" "2024-01-01" "2024-01-03" .dayOptional = none := by native_decide

example : temporalRun "[Rows/Tag] == [$Expected]" .dateTime .dateTime
    "yyyy-MM-dd'T'HH:mm:ss" "yyyy-MM-dd'T'HH:mm:ss"
    "2024-01-02T12:00:00" "2024-01-02T12:00:00" "2024-01-02T13:00:00" =
      some (.fired .omission, ["value 9"]) ∧
    temporalRun "[Rows/Tag] == [$Expected]" .date .date
    "yyyy-MM-dd" "yyyy-MM-dd" "2024-01-02" "" "2024-01-02" =
      some (.notFired, ["value 5"]) ∧
    temporalRun "[Rows/Tag] == [$Expected]" .date .date
    "yyyy-MM-dd" "yyyy-MM-dd" "2024-01-02" "bad" "2024-01-02" =
      some (.notFired, []) := by native_decide

private def rangeRun (op leftFormat rightFormat expected first second : String)
    (leftSeparator rightSeparator : Option String := none) :=
  let fields := model.fields.map fun field =>
    if field.id == 2 || field.id == 3 then
      { field with policy := { kind := .dateRange }, dateRangePolicy := some {
          format := if field.id == 3 then leftFormat else rightFormat
          separator := if field.id == 3 then leftSeparator.getD (if leftFormat.startsWith "dd." then "-" else "/")
            else rightSeparator.getD (if rightFormat.startsWith "dd." then "-" else "/") } }
    else field
  runModel { model with fields } ("[Rows/Tag] " ++ op ++ " [$Expected]") false expected first second

example : rangeRun "==" "dd.MM.yyyy" "yyyy-MM-dd" "2024-01-01/2024-02-01"
    "01.01.2024-01.02.2024" "01.01.2024-01.03.2024" = some (.fired .omission, ["value 9"]) ∧
    rangeRun "!=" "MM" "MM" "01/02" "01/03" "01/02" = some (.fired .omission, ["value 9"]) ∧
    rangeRun "==" "MM-dd" "dd.MM" "01.01-01.02" "01-01/02-01" "01-01/03-01" =
      some (.fired .omission, ["value 9"]) := by native_decide

example : rangeRun "==" "MM" "MM-dd" "01-01/02-01" "01/02" "01/03" = none ∧
    rangeRun "<" "MM" "MM" "01/02" "01/02" "01/03" = none ∧
    rangeRun "==" "MM" "MM" "01/02" "" "01/02" = some (.notFired, ["value 5"]) ∧
    rangeRun "==" "MM" "MM" "01/02" "bad" "01/02" = some (.notFired, []) := by native_decide

example : rangeRun "==" "yyyy" "yyyy" "2024/2025" "2024/2025" "2024/2026" =
      some (.fired .omission, ["value 9"]) ∧
    rangeRun "==" "yyyy-MM" "yyyy-MM" "2024-01/2024-02" "2024-01/2024-02" "2024-01/2024-03" =
      some (.fired .omission, ["value 9"]) ∧
    rangeRun "==" "MM" "MM" "01/02" "0102" "0103" (some "") =
      some (.fired .omission, ["value 9"]) := by native_decide

end A12Kernel.Dm.HavingComparisonLocks
