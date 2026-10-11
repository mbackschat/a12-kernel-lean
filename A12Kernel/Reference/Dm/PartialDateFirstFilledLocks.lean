import A12Kernel.Reference.Dm.Replay
import A12Kernel.Reference.Dm.Compute

namespace A12Kernel.Dm.PartialDateFirstFilledLocks
open Lean A12Kernel

private def run (mode : TemporalPartialMode) (star : Bool) (first second expected : String)
    (secondMode : Option TemporalPartialMode := none) (directRead : Bool := false)
    (targetMode : TemporalPartialMode := .full) (format : String := "yyyy-MM-dd") :
    Option (Verdict × List String) := do
  let sourceGroup := if star then ["Form", "Rows"] else ["Form"]
  let sourceScope := if star then [10] else []
  let source : FlatFieldDecl := {
    id := 1, groupPath := sourceGroup, name := "A", repeatableScope := sourceScope
    policy := { kind := .temporal .date TemporalComponents.fullDate }
    temporalTargetPolicy := some { format, partialMode := mode } }
  let full : FlatFieldDecl := { source with
    groupPath := ["Form"], repeatableScope := []
    temporalTargetPolicy := some { format } }
  let model : FlatModel := {
    timeZoneId := "Europe/Berlin"
    fields := [source, { source with
      id := 2, name := "B"
      temporalTargetPolicy := some { format, partialMode := secondMode.getD mode } },
      { full with id := 3, name := "Fallback" },
      { full with id := 4, name := "Out", temporalTargetPolicy := some { format, partialMode := targetMode } },
      { id := 5, groupPath := ["Form"], name := "Error", policy := { kind := .string } }]
    repeatableGroups := if star then [{ level := 10, path := sourceGroup, repeatability := some 2 }] else [] }
  let dm : DmModel := { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let sourceValues := if star then
    [("Rows", Json.arr #[Json.mkObj [("A", .str first)], Json.mkObj [("A", .str second)]])]
    else [("A", Json.str first), ("B", Json.str second)]
  let initial := if format == "dd.MM.yyyy" then "01.01.2000" else "2000-01-01"
  let input ← (readDocument dm (Json.mkObj [("Form", Json.mkObj
    (sourceValues ++ [("Fallback", Json.str expected), ("Out", Json.str initial), ("Error", Json.str "ready")]))])).toOption
  if !input.refusals.isEmpty then none
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let document ← (checkDocument prepared "en_US" input.data).toOption
  let operation := if star then "FirstFilledValue(Rows*/A, Fallback)" else "FirstFilledValue(A, B, Fallback)"
  let rule ← (checkRule dm .english {
    group := ["Form"], name := "Selected", errorCode := "SELECTED", errorEntityRelPath := "../Error",
    condition := "FieldFilled(Error) And (" ++ (if directRead then "[A]" else operation) ++ " == [Fallback])",
    severity := "ERROR" }).toOption
  let context : AddressedValidationEvaluationContext model := {
    scalar := { fields := document.flatContext.withWorld world, groups := GroupPresenceContext.unavailable }
    outer := [], input := .checked document }
  let verdict := (← (rule.evalAddressedFull context true).toOption).verdict
  let lowered ← (lowerComputation model .english {
    group := ["Form"], name := "Selected", targetRelPath := "../Out", commonPrecondition := none,
    alternatives := [{ operation, precondition := none }], errorCodesToSuppress := [] }).toOption
  let outcomes ← (runComputations world prepared document [lowered.2]).toOption
  pure (verdict, outcomes.map (·.outcome))

example : [false, true].all (fun star =>
    run .full star "2024-06-01" "bad" "2024-06-01" ==
      some (.fired .value, ["value 2024-06-01"])) = true := by native_decide

private def partialCompletions : List (TemporalPartialMode × String × String) := [
  (.dayOptional, "2024-06-00", "2024-06-01"),
  (.monthOptional, "2024-00-00", "2024-01-01"),
  (.monthOptional, "2024-06-00", "2024-06-01"),
  (.yearOptional, "2024-00-00", "2024-01-01"),
  (.yearOptional, "2024-06-00", "2024-06-01")]

example : [false, true].all (fun star => partialCompletions.all fun (mode, stored, expected) =>
    run mode star stored "2024-06-15" expected ==
      some (.fired .value, ["value " ++ expected]) &&
    run mode star "" stored expected ==
      some (.fired .omission, ["value " ++ expected]) &&
    run mode star stored "bad" expected ==
      some (.fired .value, ["value " ++ expected])) = true := by native_decide

example : [false, true].all (fun star => [.full, .dayOptional, .monthOptional, .yearOptional].all fun mode =>
    run mode star "2024-06-15" "bad" "2024-06-15" ==
      some (.fired .value, ["value 2024-06-15"]) &&
    run mode star "" "" "2024-06-15" ==
      some (.fired .omission, ["value 2024-06-15"])) = true := by native_decide

example : [false, true].all (fun star =>
    run .yearOptional star "0000-00-00" "2024-06-15" "2024-06-15" ==
      some (.unknown, ["cleared"]) &&
    run .yearOptional star "2024-06-15" "0000-00-00" "2024-06-15" ==
      some (.fired .value, ["value 2024-06-15"])) = true := by native_decide

example : [false, true].all (fun star => [.full, .dayOptional, .monthOptional, .yearOptional].all fun mode =>
    run mode star "bad" "2024-06-15" "2024-06-15" ==
      some (.unknown, ["cleared"])) = true := by native_decide

private def excessiveOmissions : List (TemporalPartialMode × String) := [
  (.full, "2024-06-00"), (.dayOptional, "2024-00-00"), (.monthOptional, "0000-00-00")]

example : [false, true].all (fun star => excessiveOmissions.all fun (mode, stored) =>
    run mode star stored "2024-06-15" "2024-06-15" ==
      some (.unknown, ["cleared"]) &&
    run mode star "2024-06-15" stored "2024-06-15" ==
      some (.fired .value, ["value 2024-06-15"])) = true := by native_decide

example : run .full false "" "2024-00-00" "2024-01-01" (secondMode := some .monthOptional) =
      some (.fired .omission, ["value 2024-01-01"]) ∧
    run .dayOptional false "" "2024-00-00" "2024-01-01" (secondMode := some .yearOptional) =
      some (.fired .omission, ["value 2024-01-01"]) := by native_decide

private def scannerDistinctions : Option Bool := do
  let declaration : FlatFieldDecl := {
    id := 1, groupPath := ["Form"], name := "A"
    policy := { kind := .temporal .date TemporalComponents.fullDate }
    temporalTargetPolicy := some { format := "yyyy-MM-dd", partialMode := .yearOptional } }
  let model : FlatModel := { timeZoneId := "Europe/Berlin", fields := [declaration] }
  let cell (stored : String) : Option CheckedAddressedCell := do
    let raw ← (CheckedDocument.canonicalTemporalCell? model declaration stored).join
    pure {
      environment := []
      address := { field := 1, path := [] }
      stored := some stored
      cell := checkAdmittedRawCell raw }
  let unknownYear ← cell "0000-00-00"
  let malformed ← cell "bad"
  let empty ← cell ""
  let present ← cell "2024-06-01"
  let project := fullDateFirstFilledCellAt .yearMonthDayDashes .europeBerlin
  let scan := evalFullDateFirstFilledCells .yearMonthDayDashes .europeBerlin
  pure (observeCell .computation unknownYear.cell == .value (.partialDate "0000-00-00") &&
    unknownYear.cell.findings.isEmpty && project unknownYear == .noValue &&
    scan [unknownYear, present] == .noValue &&
    project malformed == .poison .dateFormat && scan [malformed, present] == .poison .dateFormat &&
    observeCell .computation empty.cell == .empty && project empty == .noValue &&
    match scan [empty, present] with
    | .value instant => project present == .value instant
    | _ => false)

example : scannerDistinctions = some true := by native_decide

example : run .full false "2024-06-15" "" "2024-06-15" (directRead := true) =
    some (.fired .value, ["value 2024-06-15"]) ∧
    [.dayOptional, .monthOptional, .yearOptional].all (fun mode =>
      (run mode false "2024-06-15" "" "2024-06-15" (directRead := true)).isNone &&
      (run .full false "2024-06-15" "" "2024-06-15" (targetMode := mode)).isNone) = true := by native_decide

example : [false, true].all (fun star =>
    run .dayOptional star "00.06.2024" "15.06.2024" "01.06.2024" (format := "dd.MM.yyyy") ==
      some (.fired .value, ["value 01.06.2024"]) &&
    run .yearOptional star "00.00.0000" "15.06.2024" "15.06.2024" (format := "dd.MM.yyyy") ==
      some (.unknown, ["cleared"])) = true := by native_decide

end A12Kernel.Dm.PartialDateFirstFilledLocks
