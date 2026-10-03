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
private def run (definitions : List DmComputation) (demand supply : List Json) :
    Option (List (String × String)) := do
  let dm : DmModel := {
    flat := model, rules := [], computations := definitions, conditionLanguage := "en_US", refusals := [] }
  let input ← (readDocument dm (Json.mkObj [("Form", Json.mkObj [
    ("Demand", Json.arr demand.toArray), ("Supply", Json.arr supply.toArray), ("Out", "999")])])).toOption
  if !input.refusals.isEmpty then none
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  let steps ← definitions.mapM fun definition => (lowerComputation model .english definition).toOption.map (·.2)
  pure ((← (runComputations world prepared checked steps).toOption).map fun value =>
    (value.pointer, value.outcome))

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

private def refusalOf (result : Lowering α) : Option (String × String) :=
  match result with | .ok _ => none | .error refusal => some (refusal.construct, refusal.detail)

private def originalGuardRefusal : Option (String × String) :=
  refusalOf (elaborated "Guard" (model.elaborateCheckedComputationCondition ["Form", "Supply"] ["Form", "Supply"]
    (.fieldFilled { base := .absolute, groups := ["Form", "Demand"], field := "Amount" })))

example : originalGuardRefusal.isSome ∧ ["1", "[Amount] + 1"].all (fun operation =>
    refusalOf (lowerComputation model .english (definition "Supply" "Total"
      [{ operation, precondition := some "FieldFilled(/Form/Demand/Amount)" }])) == originalGuardRefusal) := by
  native_decide

example : run [definition "Supply" "Total"
      [{ operation := "[/Form/Demand/Amount] + 1", precondition := some "FieldFilled(Amount)" }],
    definition "Supply" "Amount" [{ operation := "7", precondition := none }]]
    [demandRow "A" "10"] [row "A" ""] =
    some [("Form/Supply/Amount", "value 7"), ("Form/Supply/Total", "value 11")] := by native_decide

end A12Kernel.Dm.ParallelComputationLocks
