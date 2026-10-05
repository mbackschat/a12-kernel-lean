import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Document

namespace A12Kernel.Dm.DateRangeConstructionLocks
open A12Kernel A12Kernel.Dm Lean

private def run (endpointFormat targetFormat separator : String) (rows : List Json)
    (repeated : Bool := true) (alternatives : List DmAlternative := [{ operation := "DateRange(Start, Finish)", precondition := none }])
    (baseYear : Option Int := none) (consumer : Bool := false) (declaredAtRoot : Bool := false)
    (kind : TemporalKind := .date) : Option (List (String × String)) := do
  let group := if repeated then ["Form", "Rows"] else ["Form"]
  let scope := if repeated then [10] else []
  let endpoint (id : FieldId) (name : String) : FlatFieldDecl := {
    id, name, groupPath := group, repeatableScope := scope
    policy := { kind := .temporal kind (TemporalComponents.ofFormat endpointFormat) }
    temporalTargetPolicy := some { format := endpointFormat } }
  let model : FlatModel := {
    baseYear, timeZoneId := "Europe/Berlin"
    fields := [endpoint 1 "Start", endpoint 2 "Finish",
      { id := 3, name := "Window", groupPath := group, repeatableScope := scope
        policy := { kind := .dateRange }, dateRangePolicy := some { format := targetFormat, separator } },
      { id := 4, name := "Gate", groupPath := group, repeatableScope := scope, policy := { kind := .string } },
      { id := 5, name := "Year", groupPath := group, repeatableScope := scope, policy := { kind := .number { scale := 0, signed := true } } }]
    repeatableGroups := if repeated then [{ level := 10, path := group, repeatability := some 2 }] else [] }
  let computation : DmComputation := {
    group := if declaredAtRoot then ["Form"] else group, name := "Construct",
    targetRelPath := if declaredAtRoot && repeated then "../Rows/Window" else "../Window", alternatives, commonPrecondition := none, errorCodesToSuppress := [] }
  let consumerDefinition : DmComputation := {
    group, name := "Consumer", targetRelPath := "../Year",
    alternatives := [{ operation := "YearFromDate(StartOfDateRange(Window))", precondition := none }],
    commonPrecondition := none, errorCodesToSuppress := [] }
  let definitions := if consumer then [consumerDefinition, computation] else [computation]
  let dm : DmModel := { flat := model, rules := [], computations := definitions, conditionLanguage := "en_US", refusals := [] }
  let raw := if repeated then Json.mkObj [("Rows", Json.arr rows.toArray)] else rows.headD (Json.mkObj [])
  let input ← (readDocument dm (Json.mkObj [("Form", raw)])).toOption
  if !input.refusals.isEmpty then none
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let document ← (checkDocument prepared "en_US" input.data).toOption
  let steps ← definitions.mapM fun definition => (lowerComputation model .english definition).toOption.map (·.2)
  pure ((← (runComputations world prepared document steps).toOption).map fun result => (result.pointer, result.outcome))

private def row (start finish : String) (stored : String := "") (gate : String := "yes") : Json :=
  Json.mkObj [("Start", Json.str start), ("Finish", Json.str finish), ("Window", Json.str stored), ("Gate", Json.str gate), ("Year", "9")]

example : run "yyyy-MM-dd" "dd.MM.yyyy" "-" [row "2024-03-05" "2024-04-06"] false =
    some [("Form/Window", "value 05.03.2024-06.04.2024")] := by native_decide

example : run "yyyy-MM-dd" "yyyy-MM-dd" "/"
    [row "2024-03-05" "2024-04-06", row "2025-01-02" "2025-02-03"] =
    some [("Form/Rows/Window", "value 2024-03-05/2024-04-06"),
      ("Form/Rows[2]/Window", "value 2025-01-02/2025-02-03")] := by native_decide

example : run "MM" "MM" "/" [row "03" "05"] false =
    some [("Form/Window", "value 03/05")] ∧
    run "MM-dd" "dd.MM" "-" [row "03-05" "04-06"] =
    some [("Form/Rows/Window", "value 05.03-06.04")] := by native_decide

example : run "yyyy-MM-dd" "yyyy-MM-dd" "/"
    [row "" "2024-04-06" "2020-01-01/2020-02-02", row "bad" "2024-04-06" "2020-01-01/2020-02-02"] =
    some [("Form/Rows/Window", "cleared"), ("Form/Rows[2]/Window", "cleared")] := by native_decide

example : run "yyyy-MM-dd" "yyyy-MM-dd" "/" [row "2024-03-05" "2024-04-06"] true
    [{ operation := "DateRange(Start, Finish)", precondition := some "FieldFilled(Gate)" },
     { operation := "DateRange(Finish, Start)", precondition := some "FieldFilled(Gate)" }] =
    some [("Form/Rows/Window", "value 2024-03-05/2024-04-06")] := by native_decide

example : [false, true].all (fun repeated =>
    let pointer := if repeated then "Form/Rows/Window" else "Form/Window"
    [("yyyy", "yyyy", "/", "2023", "2024", "2023/2024"),
     ("yyyy-MM", "yyyy-MM", "/", "2023-03", "2024-04", "2023-03/2024-04"),
     ("MM", "MM", "", "03", "04", "0304"),
     ("MM-dd", "MM-dd", "/", "03-05", "04-06", "03-05/04-06"),
     ("dd.MM.yyyy", "yyyy-MM-dd", "/", "05.03.2024", "06.04.2024", "2024-03-05/2024-04-06")].all
      (fun (sourceFormat, targetFormat, separator, start, finish, expected) =>
        run sourceFormat targetFormat separator [row start finish] repeated == some [(pointer, "value " ++ expected)])) := by native_decide

example : run "MM" "MM" "/" [row "03" "05"] (baseYear := some 2024) =
    some [("Form/Rows/Window", "value 03/05")] ∧
    [TemporalKind.date, .time, .dateTime].all (fun kind =>
      run "yyyy-MM-dd" "yyyy-MM-dd" "/" [row "2024-03-05" "2024-04-06"] (kind := kind) ==
        some [("Form/Rows/Window", "value 2024-03-05/2024-04-06")]) := by native_decide

example : run "yyyy-MM-dd" "yyyy-MM-dd" "/" [row "2024-03-05" "2024-04-06"] true
    [{ operation := "DateRange(Rows/Start, Rows/Finish)", precondition := none }]
    (declaredAtRoot := true) = some [("Form/Rows/Window", "value 2024-03-05/2024-04-06")] := by native_decide

example : run "yyyy-MM-dd" "yyyy-MM-dd" "/" [row "2024-03-05" "2024-04-06"] (consumer := true) =
    some [("Form/Rows/Window", "value 2024-03-05/2024-04-06"), ("Form/Rows/Year", "value 2024")] ∧
    run "yyyy-MM-dd" "yyyy-MM-dd" "/" [row "bad" "2024-04-06"] (consumer := true) =
    some [("Form/Rows/Year", "cleared")] := by native_decide

example : run "yyyy-MM-dd" "yyyy-MM-dd" "/" [row "2024-03-05" "2024-04-06" "2024-03-05/2024-04-06"] = some [] ∧
    run "HH:mm:ss" "yyyy-MM-dd" "/" [row "03:04:05" "04:05:06"] = none ∧
    run "yyyy" "yyyy-MM-dd" "/" [row "2023" "2024"] = none ∧
    run "yyyy-MM-dd" "yyyy-MM-dd" "/" [row "2024-03-05" "2024-04-06"] true
      [{ operation := "DateRange(Start, Finish)", precondition := none },
       { operation := "DateRange(Finish, Start)", precondition := some "FieldFilled(Gate)" }] = none := by native_decide

example : run "yyyy-MM-dd" "yyyy-MM-dd" "/" [row "2024-04-06" "2024-03-05"] =
    some [("Form/Rows/Window", "errored 2024-04-06/2024-03-05")] ∧
    run "yyyy-MM-dd" "yyyy-MM-dd" "/" [row "bad" "bad" "2020-01-01/2020-02-02" ""] true
      [{ operation := "DateRange(Start, Finish)", precondition := some "FieldFilled(Gate)" }] =
    some [("Form/Rows/Window", "cleared")] ∧
    run "yyyy-MM-dd" "yyyy-MM-dd" "/" [] = some [] := by native_decide

end A12Kernel.Dm.DateRangeConstructionLocks
