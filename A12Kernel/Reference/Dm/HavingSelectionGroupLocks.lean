import A12Kernel.Reference.Dm.HavingFixture

namespace A12Kernel.Dm.HavingSelectionGroupLocks
open Lean A12Kernel

private def model (temporal : Bool := false) : FlatModel := {
  HavingFixture.model with
  fields := HavingFixture.model.fields ++
    [(["Form", "Pool"], [20], 6, "A"), (["Form", "Pool"], [20], 7, "B"),
     (["Form", "Fixed"], [], 8, "A"), (["Form", "Fixed"], [], 9, "B")].map fun (groupPath, repeatableScope, id, name) => {
      id, name, groupPath, repeatableScope
      policy := { kind := if temporal then .temporal .time TemporalComponents.time else .string }
      temporalTargetPolicy := if temporal then some { format := "HH:mm:ss" } else none }
  repeatableGroups := HavingFixture.model.repeatableGroups ++ [{ level := 20, path := ["Form", "Pool"], repeatability := some 2 }] }
private def row (first second : String) := Json.mkObj [("A", Json.str first), ("B", Json.str second)]
private def run (filter selected : String) (temporal : Bool := false) (emptyPool : Bool := false) :=
  let chosen := if temporal then "12:30:00" else "chosen"
  let later := if temporal then "13:00:00" else "later"
  HavingFixture.runModel (model temporal) (filter ++ " And FieldFilled(Rows/N)") false "keep" "keep" "drop"
    (ruleExpected := selected) (extra := [
      ("Pool", Json.arr (if emptyPool then #[] else #[row "" chosen, row later later])),
      ("Fixed", row "" chosen)])

example : run "FirstFilledValue(Pool*) == \"later\"" "14" = some (.fired .omission, ["value 14"]) ∧
    run "FirstFilledValue(Pool*) == \"chosen\"" "0" = some (.fired .omission, ["value 0"]) ∧
    run "FirstFilledValue(Fixed) == \"chosen\"" "14" = some (.fired .omission, ["value 14"]) ∧
    run "FirstFilledValue(Pool*,Fixed) == \"chosen\"" "14" (emptyPool := true) =
      some (.fired .omission, ["value 14"]) := by native_decide

example : [("FirstFilledValue", "13:00:00"), ("MinValue", "12:30:00"), ("MaxValue", "13:00:00")].all
    (fun (operator, expected) =>
      run (operator ++ "(Pool*) == \"" ++ expected ++ "\"") "14" true ==
        some (.fired .omission, ["value 14"])) = true ∧
    run "FirstFilledValue(Fixed) == \"12:30:00\"" "14" true =
      some (.fired .omission, ["value 14"]) := by native_decide

end A12Kernel.Dm.HavingSelectionGroupLocks
