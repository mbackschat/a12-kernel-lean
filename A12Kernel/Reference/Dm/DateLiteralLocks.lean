import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Document

/-! # Date literal computation carriers

The literal/target pair owns year agreement; the declared target format owns storage. These reader
locks exercise fixed and repeatable execution through the same carrier decisions. The retained
Base Year and yearless-literal checkpoints own the measured scope.
-/

namespace A12Kernel.Dm.DateLiteralLocks

open A12Kernel A12Kernel.Dm Lean

private def run (format literal : String) (baseYear : Option Int := none)
    (repeated : Bool := false) : Option (List String) := do
  let group := if repeated then ["Form", "Rows"] else ["Form"]
  let model : FlatModel := {
    timeZoneId := "UTC", baseYear
    fields := [
      { id := 1, name := "Value", groupPath := group
        repeatableScope := if repeated then [10] else []
        policy := { kind := .temporal .date (TemporalComponents.ofFormat format) }
        temporalTargetPolicy := some { format } }]
    repeatableGroups := if repeated then
      [{ level := 10, path := group, repeatability := some 2 }] else [] }
  let dm : DmModel := {
    flat := model, computations := [], rules := []
    conditionLanguage := "en_US", refusals := [] }
  let row := Json.mkObj [("Value", "old")]
  let data := Json.mkObj [("Form", if repeated then Json.mkObj [
    ("Rows", Json.arr #[row, row, row])] else row)]
  let input ← (readDocument dm data).toOption
  if !input.refusals.isEmpty then none
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  let computation : DmComputation := {
    group := ["Form"], name := "Constant"
    targetRelPath := if repeated then "../Rows/Value" else "../Value"
    commonPrecondition := none
    alternatives := [{ precondition := none, operation := s!"\"{literal}\"" }]
    errorCodesToSuppress := [] }
  let (_, step) ← (lowerComputation model .english computation).toOption
  pure ((← (runComputations world prepared checked [step]).toOption).map (·.outcome))

example : [("dd.MM.yyyy", "11.06.2024"), ("yyyy-MM-dd", "2024-06-11"),
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

example : [false, true].all (fun repeated =>
    [("MM-dd", "02-29"), ("dd.MM.", "29.02.")].all (fun (format, stored) =>
      run format "29.02.2024" (some 2023) repeated ==
        some (if repeated then [s!"value {stored}", s!"value {stored}", "cleared"]
          else [s!"value {stored}"]))) := by native_decide

private def downstream (rejected : Bool) (leap : Bool := false) : Option (List String) := do
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
  pure ((← (runComputations world prepared checked steps).toOption).map (·.outcome))

example : downstream false = some ["value 03", "value 3"] ∧
    downstream true = some ["errored 1899-12-31", "cleared"] ∧
    downstream false true = some ["value 02-29", "cleared"] := by native_decide

end A12Kernel.Dm.DateLiteralLocks
