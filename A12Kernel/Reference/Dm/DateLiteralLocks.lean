import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.ComputeMessages
import A12Kernel.Reference.Dm.Document

/-! # Date literal computation carriers

The literal/target pair owns year agreement; the declared target format owns storage. These reader
locks exercise fixed and repeatable execution through the same carrier decisions. The retained
Base Year and yearless-literal checkpoints own the measured scope.
-/

namespace A12Kernel.Dm.DateLiteralLocks

open A12Kernel A12Kernel.Dm Lean

/-- The call's raw result, a refusal included; `zone` is the model's time zone. `none` only when the
fixture itself does not read or check. -/
private def runResult (format literal : String) (baseYear : Option Int := none)
    (repeated : Bool := false) (zone : String := "UTC") :
    Option (Lowering (List ComputedOutcome × List ComputedMessage)) := do
  let group := if repeated then ["Form", "Rows"] else ["Form"]
  let model : FlatModel := {
    timeZoneId := zone, baseYear
    fields := [
      { id := 1, name := "Value", groupPath := group
        repeatableScope := if repeated then [10] else []
        policy := { kind := .temporal .date (TemporalComponents.ofFormat format) }
        temporalTargetPolicy := some { format } }]
    repeatableGroups := if repeated then
      [{ level := 10, path := group, repeatability := some 2 }] else [] }
  let computation : DmComputation := {
    group := ["Form"], name := "Constant"
    targetRelPath := if repeated then "../Rows/Value" else "../Value"
    commonPrecondition := none
    alternatives := [{ precondition := none, operation := s!"\"{literal}\"" }]
    errorCodesToSuppress := [] }
  let dm : DmModel := {
    flat := model, computations := [computation], rules := []
    conditionLanguage := "en_US", refusals := [] }
  let row := Json.mkObj [("Value", "old")]
  let data := Json.mkObj [("Form", if repeated then Json.mkObj [
    ("Rows", Json.arr #[row, row, row])] else row)]
  let input ← (readDocument dm data).toOption
  if !input.refusals.isEmpty then none
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  pure (runModelComputationsWithMessages dm .english world prepared checked)

/-- The call's outcomes beside its formal-error channel. -/
private def runWithMessages (format literal : String) (baseYear : Option Int := none)
    (repeated : Bool := false) (zone : String := "UTC") :
    Option (List ComputedOutcome × List ComputedMessage) :=
  (runResult format literal baseYear repeated zone).bind (·.toOption)

/-- The refusal of a call that cannot assemble its result: its construct and whether its detail names
a duplicate report pointer. -/
private def assemblyRefusal (format literal : String) (baseYear : Option Int := none)
    (repeated : Bool := false) : Option (String × Bool) :=
  match runResult format literal baseYear repeated with
  | some (.error refusal) => some (refusal.construct, (refusal.detail.splitOn "duplicatePointer").length > 1)
  | _ => none

private def run (format literal : String) (baseYear : Option Int := none)
    (repeated : Bool := false) (zone : String := "UTC") : Option (List String) :=
  (runWithMessages format literal baseYear repeated zone).map (·.1.map (·.outcome))

example : [("dd.MM.yyyy", "11.06.2024"), ("yyyy-MM-dd", "2024-06-11"), ("yyyyMMdd", "20240611"),
    ("yyyy", "2024"), ("yyyy-MM", "2024-06"), ("yyyyMM", "202406"),
    ("MM", "06"), ("MM-dd", "06-11"), ("MMdd", "0611"), ("ddMM", "1106"),
    ("dd.MM.", "11.06.")].all
    (fun (format, stored) =>
      run format "11.06.2024" (some 2023) == some [s!"value {stored}"] &&
      run format "11.06.2024" (some 2023) true ==
        some [s!"value {stored}", s!"value {stored}", "cleared"]) := by native_decide

example : [false, true].all (fun repeated =>
    let stored (text : String) := if repeated then some [s!"value {text}", s!"value {text}", "cleared"]
      else some [s!"value {text}"]
    run "yyyy-MM-dd" "11.06.2024" none repeated == stored "2024-06-11" &&
    run "yyyy-MM-dd" "29.02.2024" none repeated == stored "2024-02-29" &&
    run "yyyy-MM-dd" "29.02.2023" none repeated == none &&
    run "MM-dd" "11.06." none repeated == stored "06-11" &&
    run "dd.MM." "11.06." none repeated == stored "11.06." &&
    run "MM" "11.06." none repeated == stored "06" &&
    run "MM-dd" "11.06.2024" none repeated == none &&
    run "yyyy-MM-dd" "11.06." none repeated == none &&
    run "yyyy-MM-dd" "11.06." (some 2023) repeated == stored "2023-06-11" &&
    run "yyyy-MM-dd" "11.06." (some 2024) repeated == stored "2024-06-11" &&
    run "MM-dd" "29.02." (some 2024) repeated == none) := by native_decide

/- A leap literal into a day-month target under a common Base Year draws two diagnostics at the target
pointer, the re-completed label's format refusal and the store's failed re-parse, so the whole call fails
result assembly; under a leap Base Year it stores, and a year-carrying target stores the full date (spec/05
§3.1; a12-dmkits `CalendarTargetCompletionDiffTest` at `1124b523f`, every day-month format). -/
example : [false, true].all (fun repeated =>
    ["MM-dd", "MMdd", "dd.MM.", "ddMM"].all (fun format =>
      assemblyRefusal format "29.02.2024" (some 2023) repeated == some ("ComputationRun", true)) &&
    [("MM-dd", "02-29"), ("dd.MM.", "29.02.")].all (fun (format, stored) =>
      run format "29.02.2024" (some 2024) repeated ==
        some (if repeated then [s!"value {stored}", s!"value {stored}", "cleared"]
          else [s!"value {stored}"])) &&
    run "yyyy-MM-dd" "29.02.2024" (some 2023) repeated ==
      some (if repeated then ["value 2024-02-29", "value 2024-02-29", "cleared"]
        else ["value 2024-02-29"])) := by native_decide

private def downstreamRun (rejected : Bool) (leap : Bool := false) :
    Option (Lowering (List ComputedOutcome)) := do
  let format := if leap then "MM-dd" else if rejected then "yyyy-MM-dd" else "MM"
  let model : FlatModel := {
    timeZoneId := "UTC", baseYear := if leap then some 2023 else none
    fields := [
      { id := 1, name := "Value", groupPath := ["Form"]
        policy := { kind := .temporal .date (TemporalComponents.ofFormat format) }
        temporalTargetPolicy := some { format, youngerThan1900Check := rejected } },
      { id := 2, name := "Out", groupPath := ["Form"]
        policy := { kind := .number { scale := 0, signed := true } } }] }
  let dm : DmModel := {
    flat := model, computations := [], rules := [], conditionLanguage := "en_US", refusals := [] }
  let input ← (readDocument dm (Json.mkObj [("Form", Json.mkObj [
    ("Value", "01"), ("Out", "9")])])).toOption
  if !input.refusals.isEmpty then none
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  let definition (name target operation : String) : DmComputation := {
    group := ["Form"], name, targetRelPath := target, commonPrecondition := none
    alternatives := [{ precondition := none, operation }], errorCodesToSuppress := [] }
  let steps ← [definition "Consumer" "../Out" "MonthFromDate(Value)",
      definition "Producer" "../Value" (if leap then "\"29.02.2024\""
        else if rejected then "\"31.12.1899\"" else "\"05.03.\"")].mapM
    fun computation => (lowerComputation model .english computation).toOption.map (·.2)
  pure (runComputations world prepared checked steps)

private def downstream (rejected : Bool) : Option (List String) :=
  (downstreamRun rejected).bind fun run => run.toOption.map (·.map (·.outcome))

/- A dependent consumer does not rescue the leap call: the colliding target still fails assembly
(spec/05 §3.1). -/
example : downstream false = some ["value 03", "value 3"] ∧
    downstream true = some ["errored 1899-12-31", "cleared"] ∧
    (match downstreamRun false true with
      | some (.error refusal) => refusal.construct == "ComputationRun" &&
          (refusal.detail.splitOn "duplicatePointer").length > 1
      | _ => false) = true := by native_decide

/- A date constant is a stored label resolved in the model zone when it is reached (spec/05 §1). The
Julian leap day `29.02.1500` is admitted statically and resolves under UTC to its Julian instant, which
renders as the proleptic 10 March 1500 and which the target's own floor check then marks errored. Under
Europe/Berlin it has no instant, so the target takes the value failure the DateTime constant carrier takes
and reports the value-less target error, for a fixed target and for every row of a repeatable one. The
adjacent real labels resolve as themselves. Unmeasured on 31.1.1. -/
example : (runWithMessages "yyyy-MM-dd" "29.02.1500" none false "UTC").map
      (fun (outcomes, messages) => (outcomes.map (·.outcome), messages.map (·.code))) =
        some (["errored 1500-03-10"], []) ∧
    run "yyyy-MM-dd" "29.02.1500" none true "UTC" =
      some ["errored 1500-03-10", "errored 1500-03-10", "cleared"] ∧
    (runWithMessages "yyyy-MM-dd" "29.02.1500" none false "Europe/Berlin").map
      (fun (outcomes, messages) => (outcomes.map (·.outcome), messages.map (·.code))) =
        some (["cleared"], ["berechnungsWertFehler"]) ∧
    (runWithMessages "yyyy-MM-dd" "29.02.1500" none true "Europe/Berlin").map
      (fun (outcomes, messages) => (outcomes.map (·.outcome),
        (messages.filter (·.code == "berechnungsWertFehler")).map (·.pointer))) =
        some (["cleared", "cleared", "cleared"], ["Form/Rows/Value", "Form/Rows[2]/Value"]) ∧
    run "yyyy-MM-dd" "28.02.1500" none false "Europe/Berlin" = some ["errored 1500-02-28"] ∧
    run "yyyy-MM-dd" "04.10.1582" none false "Europe/Berlin" = some ["errored 1582-10-04"] := by
  native_decide

end A12Kernel.Dm.DateLiteralLocks
