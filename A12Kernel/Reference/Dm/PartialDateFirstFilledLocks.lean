import A12Kernel.Reference.Dm.Replay
import A12Kernel.Reference.Dm.Compute

namespace A12Kernel.Dm.PartialDateFirstFilledLocks
open Lean A12Kernel

private def run (mode : TemporalPartialMode) (star : Bool) (first second expected : String)
    (secondMode : Option TemporalPartialMode := none) (directRead : Bool := false)
    (targetMode : TemporalPartialMode := .full) (format : String := "yyyy-MM-dd")
    (targetFormat : Option String := none) :
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
      { full with
        id := 4, name := "Out"
        policy := { kind := .temporal .date (TemporalComponents.ofFormat (targetFormat.getD format)) }
        temporalTargetPolicy := some {
          format := targetFormat.getD format, partialMode := targetMode } },
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

example : [false, true].all (fun star =>
    run .full star "06.05.2024" "11.12.2023" "06.05.2024"
      (format := "dd.MM.yyyy") (targetFormat := some "yyyy-MM-dd") ==
      some (.fired .value, ["value 2024-05-06"]) &&
    run .dayOptional star "00.05.2024" "11.12.2023" "01.05.2024"
      (format := "dd.MM.yyyy") (targetFormat := some "yyyy-MM-dd") ==
      some (.fired .value, ["value 2024-05-01"])) := by native_decide

example : [false, true].all (fun star =>
    run .full star "06.05.2024" "11.12.2023" "06.05.2024"
      (format := "dd.MM.yyyy") (targetFormat := some "yyyy") ==
      some (.fired .value, ["value 2024"])) := by native_decide

example : run .full false "2024-06-11" "2023-12-11" "2024-06-11"
    (targetFormat := some "yyyyMMdd") = some (.fired .value, ["value 20240611"]) := by
  native_decide

private def profileRun (sourceFormat targetFormat first second : String)
    (baseYear : Option Int := none) (repeated : Bool := false)
    (sourceChecked : Bool := false) (targetChecked : Bool := false)
    (clean : String := "2022-07-08") (secondFormat : Option String := none)
    (downstream : Bool := false) :
    Option (List (String × String)) := do
  let group := if repeated then ["Form", "Rows"] else ["Form"]
  let scope := if repeated then [10] else []
  let declaration (id : FieldId) (name format : String) (checked : Bool) :=
    readFieldType id group name scope (Json.mkObj [("fieldType", Json.mkObj [
      ("type", .str "DateType"), ("DateType", Json.mkObj [
        ("format", .str format), ("youngerThan1900Check", .bool checked)])])])
  let a ← (declaration 1 "A" sourceFormat sourceChecked).toOption
  let b ← (declaration 2 "B" (secondFormat.getD sourceFormat) sourceChecked).toOption
  let target ← (declaration 3 "Out" targetFormat targetChecked).toOption
  let fallback ← (declaration 4 "Empty" targetFormat false).toOption
  let consumer ← (declaration 5 "Next" "yyyy-MM-dd" false).toOption
  let model : FlatModel := {
    timeZoneId := "Europe/Berlin", baseYear
    fields := [a, b, target] ++ if downstream then [fallback, consumer] else []
    repeatableGroups := if repeated then
      [{ level := 10, path := group, repeatability := some 2 }] else [] }
  let dm : DmModel := {
    flat := model, computations := [], rules := [], conditionLanguage := "en_US", refusals := [] }
  let seed := match FullDateTargetFormat.ofSource? targetFormat with
    | some format => (format.renderParts { year := 1990, month := 1, day := 1 }).text
    | none => ((OmittingDateFormat.ofSource? targetFormat).map fun format =>
        (format.renderParts { year := 1990, month := 1, day := 1 }).text).getD "seed"
  let row (a b : String) := Json.mkObj [("A", .str a), ("B", .str b), ("Out", .str seed)]
  let data := Json.mkObj [("Form", if repeated then
    Json.mkObj [("Rows", .arr #[row first second, row clean "bad"])]
    else row first second)]
  let input ← (readDocument dm data).toOption
  if !input.refusals.isEmpty then none
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let document ← (checkDocument prepared "en_US" input.data).toOption
  let path := if repeated then "/Form/Rows/" else "/Form/"
  let (_, step) ← (lowerComputation model .english {
    group := ["Form"], name := "Selected"
    targetRelPath := if repeated then "../Rows/Out" else "../Out"
    commonPrecondition := none
    alternatives := [{ precondition := none, operation :=
      "FirstFilledValue(" ++ path ++ "A," ++ path ++ "B)" }]
    errorCodesToSuppress := [] }).toOption
  let steps ← if downstream then do
      let (_, next) ← (lowerComputation model .english {
        group := ["Form"], name := "ReadReducedPrecision"
        targetRelPath := if repeated then "../Rows/Next" else "../Next"
        commonPrecondition := none
        alternatives := [{ precondition := none, operation :=
          "FirstFilledValue(" ++ path ++ "Out," ++ path ++ "Empty)" }]
        errorCodesToSuppress := [] }).toOption
      pure [next, step]
    else pure [step]
  let outcomes ← (runComputations world prepared document steps).toOption
  pure ((outcomes.filter fun outcome => !downstream || outcome.pointer.endsWith "/Next").map
    fun outcome => (outcome.pointer, outcome.outcome))

private def expectedProfiles (repeated : Bool) (first clean : String) :
    Option (List (String × String)) :=
  some (if repeated then [("Form/Rows/Out", first), ("Form/Rows[2]/Out", clean)]
    else [("Form/Out", first)])

private def profileOutputs : List (String × String × String) := [
  ("yyyy-MM-dd", "2024-06-11", "2022-07-08"),
  ("dd.MM.yyyy", "11.06.2024", "08.07.2022"),
  ("yyyyMMdd", "20240611", "20220708"),
  ("yyyy", "2024", "2022"), ("yyyy-MM", "2024-06", "2022-07"),
  ("yyyyMM", "202406", "202207"), ("MM", "06", "07"),
  ("MM-dd", "06-11", "07-08"), ("MMdd", "0611", "0708"),
  ("ddMM", "1106", "0807"), ("dd.MM.", "11.06.", "08.07.")]

example : [false, true].all (fun repeated => profileOutputs.all fun (format, first, clean) =>
    profileRun "yyyy-MM-dd" format "2024-06-11" "2023-12-11" (some 2023) repeated ==
      expectedProfiles repeated ("value " ++ first) ("value " ++ clean)) := by native_decide

example : [false, true].all (fun repeated =>
    profileRun "yyyy-MM-dd" "yyyy-MM-dd" "1899-12-31" "2024-06-11" none repeated
      (sourceChecked := true) == expectedProfiles repeated "cleared" "value 2022-07-08" &&
    profileRun "yyyy-MM-dd" "yyyy-MM-dd" "1900-01-01" "bad" none repeated
      (sourceChecked := true) == expectedProfiles repeated "value 1900-01-01" "value 2022-07-08" &&
    profileRun "yyyy-MM-dd" "yyyy-MM-dd" "1899-12-31" "2024-06-11" none repeated
      (targetChecked := true) == expectedProfiles repeated "errored 1899-12-31" "value 2022-07-08") := by native_decide

example : [false, true].all (fun repeated =>
    profileRun "dd.MM." "yyyy-MM-dd" "11.06." "12.12." (some 2023) repeated
      (clean := "08.07.") == expectedProfiles repeated "value 2023-06-11" "value 2023-07-08" &&
    (profileRun "dd.MM." "yyyy-MM-dd" "11.06." "12.12." none repeated
      (clean := "08.07.")).isNone &&
    profileRun "yyyy-MM-dd" "ddMM" "2024-02-29" "2024-06-11" (some 2023) repeated ==
      expectedProfiles repeated "errored 2902" "value 0807" &&
    profileRun "dd.MM." "yyyy-MM-dd" "29.02." "11.06." (some 2023) repeated
      (clean := "08.07.") == expectedProfiles repeated "cleared" "value 2023-07-08") := by native_decide

example : [false, true].all (fun repeated =>
    profileRun "yyyyMMdd" "dd.MM.yyyy" "20240611" "20231211" none repeated
      (clean := "20220708") == expectedProfiles repeated "value 11.06.2024" "value 08.07.2022" &&
    (profileRun "yyyyMMdd" "dd.MM.yyyy" "20240611" "2023-12-11" none repeated
      (clean := "20220708") (secondFormat := some "yyyy-MM-dd")).isNone &&
    (profileRun "yyyy-MM-dd" "MM-dd" "2024-06-11" "2023-12-11" none repeated).isNone) := by native_decide

example : run .dayOptional false "20240600" "20231211" "20240601"
    (format := "yyyyMMdd") (targetFormat := some "yyyy-MM-dd") =
      some (.fired .value, ["value 2024-06-01"]) := by native_decide

example : [("yyyy-MM", "2024-06-01", "2022-07-01"),
    ("yyyy", "2024-01-01", "2022-01-01")].all (fun (format, first, clean) =>
    [false, true].all fun repeated =>
      profileRun "yyyy-MM-dd" format "2024-06-11" "2023-12-11" none repeated
        (downstream := true) == some (if repeated then
          [("Form/Rows/Next", "value " ++ first), ("Form/Rows[2]/Next", "value " ++ clean)]
          else [("Form/Next", "value " ++ first)])) := by native_decide

end A12Kernel.Dm.PartialDateFirstFilledLocks
