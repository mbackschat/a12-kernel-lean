import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Document

/-! # Parallel numeric reader and mixed-plan locks

The staffing replay calibrates key matching, missing keys and invalid operands. These internal
compositions additionally distinguish fresh producer state, poison, selection and target capacity.
-/
namespace A12Kernel.Dm.ParallelComputationLocks
open A12Kernel A12Kernel.Dm Lean

private def field (id : FieldId) (group name : String) (kind : FieldKind) : FlatFieldDecl := {
  id, name, groupPath := ["Form", group], repeatableScope := [if group == "Demand" then 10 else 20]
  policy := { kind } }
private def number (id : FieldId) (group name : String) :=
  field id group name (.number { scale := 0, signed := true })
private def model : FlatModel := {
  fields := [field 1 "Demand" "Key" .string, number 2 "Demand" "Amount",
    field 3 "Supply" "Key" .string, number 4 "Supply" "Amount", number 5 "Supply" "Total",
    { id := 6, name := "Out", groupPath := ["Form"], policy := { kind := .number { scale := 0, signed := true } } }]
  repeatableGroups := [
    { level := 10, path := ["Form", "Demand"], repeatability := some 2, indexField := some 1 },
    { level := 20, path := ["Form", "Supply"], repeatability := some 2, indexField := some 3 }] }
private def definition (group target : String) (alternatives : List DmAlternative)
    (common : Option String := none) : DmComputation := {
  group := ["Form", group], name := target, targetRelPath := "../" ++ target,
  alternatives, commonPrecondition := common, errorCodesToSuppress := [] }
private def total (guard : Option String := none) : DmComputation :=
  definition "Supply" "Total" [{ operation := "[/Form/Demand/Amount] + [Amount]", precondition := guard }]
private def row (key amount : String) : Json :=
  Json.mkObj [("Key", Json.str key), ("Amount", Json.str amount), ("Total", "999")]
private def demandRow (key amount : String) : Json :=
  Json.mkObj [("Key", Json.str key), ("Amount", Json.str amount)]
private structure Summary where
  outcomes : List (String × String)
  findings : List ComputationFormalInputFinding

private def summary (definitions : List DmComputation) (demand supply : List Json) : Option Summary := do
  let dm : DmModel := {
    flat := model, rules := [], computations := definitions, conditionLanguage := "en_US", refusals := [] }
  let input ← (readDocument dm (Json.mkObj [("Form", Json.mkObj [
    ("Demand", Json.arr demand.toArray), ("Supply", Json.arr supply.toArray), ("Out", "999")])])).toOption
  if !input.refusals.isEmpty then none
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  let lowered ← definitions.mapM fun definition => (lowerComputation model .english definition).toOption.map (·.2)
  let steps := lowered.map (·.toMixedStep builtinStringPatternCompiler)
  let plan ← (certifyAuthoredMixedComputationPlan steps).toOption
  let formalPlan ← plan.formalInputPlan.toOption
  let formalInputs ← (formalPlan.prepare checked).toOption
  let results ← (runComputations world prepared checked lowered).toOption
  pure {
    outcomes := results.map fun value => (value.pointer, value.outcome)
    findings := formalInputs.formalErrorsInOperands }

private def run (definitions : List DmComputation) (demand supply : List Json) :
    Option (List (String × String)) :=
  (summary definitions demand supply).map (·.outcomes)

example : run [total] [demandRow "A" "10", demandRow "B" "20"] [row "B" "2", row "A" "1"] =
    some [("Form/Supply/Total", "value 22"), ("Form/Supply[2]/Total", "value 11")] ∧
    run [total] [demandRow "A" "10"] [row "B" "2"] = some [("Form/Supply/Total", "value 2")] := by native_decide

example : run [total] [demandRow "A" "10"] [row "" "2"] = some [("Form/Supply/Total", "cleared")] ∧
    run [total] [demandRow "A" "bad"] [row "A" "2"] = some [("Form/Supply/Total", "cleared")] ∧
    run [total] [] [] = some [] := by native_decide

private def downstream : DmComputation := {
  group := ["Form"], name := "Out", targetRelPath := "../Out", commonPrecondition := none,
  alternatives := [{ operation := "Sum(Supply*/Total) + 1", precondition := none }], errorCodesToSuppress := [] }

example : run [downstream, total, definition "Demand" "Amount" [{ operation := "7", precondition := none }]]
    [demandRow "A" "100"] [row "A" "2"] = some [
      ("Form/Demand/Amount", "value 7"), ("Form/Supply/Total", "value 9"), ("Form/Out", "value 10")] := by native_decide

example : run [downstream, total] [demandRow "A" "bad"] [row "A" "2"] =
    some [("Form/Supply/Total", "cleared"), ("Form/Out", "cleared")] ∧
    run [downstream, total] [demandRow "A" "10"] [row "" "2"] =
    some [("Form/Supply/Total", "cleared"), ("Form/Out", "value 1")] := by native_decide


example : run [downstream, total] [demandRow "A" "10", demandRow "A" "20"] [row "A" "2"] =
    some [("Form/Supply/Total", "cleared"), ("Form/Out", "value 1")] ∧
    run [downstream, total] [demandRow "A" "10"] [row "A" "1", row "B" "2", row "C" "bad"] =
    some [("Form/Supply/Total", "value 11"), ("Form/Supply[2]/Total", "value 2"),
      ("Form/Supply[3]/Total", "cleared"), ("Form/Out", "value 14")] := by native_decide

private def alternatives (common : Option String := none) : DmComputation :=
  definition "Supply" "Total" [
    { operation := "[/Form/Demand/Amount] + [Amount]", precondition := some "FieldNotFilled(Amount)" },
    { operation := "[/Form/Demand/Amount] - [Amount]", precondition := some "FieldFilled(Amount)" }] common

example : run [alternatives] [demandRow "A" "10"] [row "A" "2"] =
    some [("Form/Supply/Total", "value 8")] ∧
    run [downstream, alternatives (some "FieldNotFilled(Amount)")]
      [demandRow "A" "bad"] [row "A" "2"] =
    some [("Form/Supply/Total", "cleared"), ("Form/Out", "value 1")] := by native_decide

example : run [downstream, total (some "FieldFilled(/Form/Demand/Amount)")]
    [demandRow "A" "bad"] [row "A" "2"] =
    some [("Form/Supply/Total", "cleared"), ("Form/Out", "cleared")] ∧
    run [downstream, total (some "FieldNotFilled(Amount)")]
      [demandRow "A" "bad"] [row "A" "2"] =
    some [("Form/Supply/Total", "cleared"), ("Form/Out", "value 1")] := by native_decide

example : [
    definition "Supply" "Total" [{ operation := "[/Form/Demand/Amount] + [Total]", precondition := none }],
    total (some "FieldFilled(Total)"),
    definition "Supply" "Total" [
      { operation := "[/Form/Demand/Amount] + [Amount]", precondition := none },
      { operation := "[/Form/Demand/Amount] - [Amount]", precondition := some "FieldFilled(Amount)" }]
      (some "FieldFilled(Amount)")].all (fun definition =>
        !(lowerComputation model .english definition).isOk) = true := by native_decide

private def outsideTarget : DmComputation := {
  definition "Demand" "Total" [{ operation := "[/Form/Demand/Amount] + [/Form/Supply/Amount]", precondition := none }]
  with targetRelPath := "../../Supply/Total" }

example : (lowerComputation model .english outsideTarget).isOk = false := by native_decide

example : ["1", "[Amount] + 1"].map (fun operation =>
    run [definition "Supply" "Total"
      [{ operation, precondition := some "FieldFilled(/Form/Demand/Amount)" }]]
      [demandRow "A" "10"] [row "A" "2"]) = [
    some [("Form/Supply/Total", "value 1")], some [("Form/Supply/Total", "value 3")]] := by native_decide

example : run [definition "Supply" "Total"
      [{ operation := "[/Form/Demand/Amount] + 1", precondition := some "FieldFilled(Amount)" }],
    definition "Supply" "Amount" [{ operation := "7", precondition := none }]]
    [demandRow "A" "10"] [row "A" ""] =
    some [("Form/Supply/Amount", "value 7"), ("Form/Supply/Total", "value 11")] := by native_decide

example : run [total (some "FieldNotFilled(Amount)"), total (some "FieldFilled(Amount)")]
    [demandRow "A" "10"] [row "A" "2"] =
    some [("Form/Supply/Total", "value 12")] := by native_decide

example : run [total (some "FieldNotFilled(Amount)"), total]
    [demandRow "A" "10"] [row "A" "2"] =
    some [("Form/Supply/Total", "value 12")] := by native_decide

private def difference (guard : Option String := none) : DmComputation :=
  definition "Supply" "Total" [{ operation := "[/Form/Demand/Amount] - [Amount]", precondition := guard }]

private def unselectedAlternatives : DmComputation :=
  definition "Supply" "Total" [
    { operation := "[/Form/Demand/Amount] + [Amount]", precondition := some "FieldNotFilled(Amount)" },
    { operation := "[/Form/Demand/Amount] - [Amount]", precondition := some "FieldNotFilled(Amount)" }]

private def positiveAlternatives : DmComputation :=
  definition "Supply" "Total" [
    { operation := "[/Form/Demand/Amount] + [Amount]", precondition := some "FieldFilled(Amount)" },
    { operation := "[/Form/Demand/Amount] - [Amount]", precondition := some "FieldNotFilled(Amount)" }]

private def constantTotal (guard : String) : DmComputation :=
  definition "Supply" "Total" [{ operation := "7", precondition := some guard }]

example : [
    ([total (some "FieldFilled(Amount)"), difference (some "FieldFilled(Amount)")], "value 12"),
    ([difference (some "FieldFilled(Amount)"), total (some "FieldFilled(Amount)")], "value 8"),
    ([total (some "FieldFilled(Amount)"), difference], "value 12"),
    ([difference, total (some "FieldFilled(Amount)")], "value 8"),
    ([alternatives, total (some "FieldFilled(Amount)")], "value 8"),
    ([total (some "FieldFilled(Amount)"), alternatives], "value 12"),
    ([unselectedAlternatives, total (some "FieldFilled(Amount)")], "value 12"),
    ([total (some "FieldNotFilled(Amount)"), alternatives], "value 8"),
    ([unselectedAlternatives, alternatives], "value 8"),
    ([alternatives, unselectedAlternatives], "value 8"),
    ([alternatives, positiveAlternatives], "value 8"),
    ([positiveAlternatives, alternatives], "value 12")].all (fun (declarations, expected) =>
      run declarations [demandRow "A" "10"] [row "A" "2"] ==
        some [("Form/Supply/Total", expected)]) = true := by native_decide

example : run [downstream,
    { total (some "FieldFilled(Amount)") with commonPrecondition := some "FieldNotFilled(Amount)" },
    difference (some "FieldFilled(Amount)")]
    [demandRow "A" "10"] [row "A" "2"] =
    some [("Form/Supply/Total", "value 8"), ("Form/Out", "value 9")] := by native_decide

example : [
    [downstream, constantTotal "FieldFilled(/Form/Demand/Amount)", constantTotal "FieldFilled(/Form/Demand/Key)"],
    [downstream, total (some "FieldFilled(Amount)"), constantTotal "FieldFilled(/Form/Demand/Key)"],
    [downstream, constantTotal "FieldFilled(/Form/Demand/Key)", total (some "FieldFilled(Amount)")]].map (fun declarations =>
      run declarations [demandRow "A" "bad"] [row "A" "2"]) = [
    some [("Form/Supply/Total", "cleared"), ("Form/Out", "cleared")],
    some [("Form/Supply/Total", "cleared"), ("Form/Out", "cleared")],
    some [("Form/Supply/Total", "value 7"), ("Form/Out", "value 8")]] := by native_decide

example : run [downstream, constantTotal "FieldNotFilled(/Form/Demand/Key)", total (some "FieldFilled(Amount)"),
    definition "Demand" "Amount" [{ operation := "7", precondition := none }]]
    [demandRow "A" "100"] [row "A" "2"] = some [
    ("Form/Demand/Amount", "value 7"), ("Form/Supply/Total", "value 9"), ("Form/Out", "value 10")] := by native_decide

private def scalarFallback : DmComputation :=
  definition "Supply" "Total" [{ operation := "7", precondition := none }]

example : run [total (some "FieldNotFilled(Amount)"), scalarFallback]
    [demandRow "A" "10"] [row "A" "2"] =
    some [("Form/Supply/Total", "value 7")] := by native_decide

example : run [scalarFallback, total (some "FieldFilled(Amount)")]
    [demandRow "A" "10"] [row "A" "2"] =
    some [("Form/Supply/Total", "value 7")] := by native_decide

private def starredFallback : DmComputation :=
  definition "Supply" "Total" [{ operation := "Sum(/Form/Demand*/Amount)", precondition := none }]

example : run [starredFallback, total (some "FieldFilled(Amount)")]
    [demandRow "A" "10", demandRow "B" "20"] [row "B" "2", row "A" "1"] =
    some [("Form/Supply/Total", "value 30"), ("Form/Supply[2]/Total", "value 30")] := by native_decide

example : run [total (some "FieldNotFilled(Amount)"), starredFallback]
    [demandRow "A" "10", demandRow "B" "20"] [row "B" "2", row "A" "1"] =
    some [("Form/Supply/Total", "value 30"), ("Form/Supply[2]/Total", "value 30")] := by native_decide

example : run [scalarFallback, total (some "FieldFilled(Amount)")]
    [demandRow "A" "10", demandRow "A" "20"] [row "A" "2"] =
    some [("Form/Supply/Total", "cleared")] := by native_decide

example : run [downstream, starredFallback, total (some "FieldFilled(Amount)")]
    [demandRow "A" "bad"] [row "A" "2"] =
    some [("Form/Supply/Total", "cleared"), ("Form/Out", "cleared")] := by native_decide

private def boundLocal (guard : Option String := none) : DmComputation :=
  definition "Supply" "Total" [{ operation := "[Amount] + 1", precondition := guard }]

example : run [downstream, constantTotal "FieldNotFilled(/Form/Demand/Key)", boundLocal,
    definition "Supply" "Amount" [{ operation := "7", precondition := none }]]
    [demandRow "A" "10"] [row "A" "2"] = some [
    ("Form/Supply/Amount", "value 7"), ("Form/Supply/Total", "value 8"), ("Form/Out", "value 9")] := by native_decide

example : run [constantTotal "FieldNotFilled(/Form/Demand/Key)", boundLocal]
    [demandRow "A" "10", demandRow "B" "20"] [row "B" "2", row "A" "1"] =
    some [("Form/Supply/Total", "value 3"), ("Form/Supply[2]/Total", "value 2")] := by native_decide

example : [
    ([boundLocal, total (some "FieldFilled(Amount)"), scalarFallback], "value 3"),
    ([boundLocal (some "FieldNotFilled(Amount)"), total (some "FieldFilled(Amount)"), scalarFallback], "value 12"),
    ([boundLocal (some "FieldNotFilled(Amount)"), total (some "FieldNotFilled(Amount)"), scalarFallback], "value 7")].all
    (fun (declarations, expected) => run declarations [demandRow "A" "10"] [row "A" "2"] ==
      some [("Form/Supply/Total", expected)]) = true := by native_decide

example : (lowerComputation model .english (boundLocal (some "GroupFilled(/Form/Supply)"))).isOk = true ∧
    run [boundLocal (some "GroupFilled(/Form/Supply)")]
      [demandRow "A" "10"] [row "A" "2"] = some [("Form/Supply/Total", "value 3")] ∧
    run [constantTotal "FieldNotFilled(/Form/Demand/Key)", boundLocal (some "GroupFilled(/Form/Supply)")]
      [demandRow "A" "10"] [row "A" "2"] = some [("Form/Supply/Total", "value 3")] := by native_decide

example : [
    [scalarFallback, total (some "FieldFilled(Amount)")],
    [total (some "FieldNotFilled(Amount)"), scalarFallback],
    [scalarFallback, constantTotal "FieldNotFilled(/Form/Demand/Key)", starredFallback]].all
    (fun declarations => (summary declarations [demandRow "A" "bad"] [row "A" "2"]).map
      (fun result => (result.outcomes, result.findings)) == some (
        [("Form/Supply/Total", "value 7")],
        [{ address := { field := 2, path := [1] }, cause := .malformed }])) = true := by native_decide

end A12Kernel.Dm.ParallelComputationLocks
