import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Document

/-! Reader-to-overlay controls for the two-group C14 kernel matrix. The stale producer and reversed
keys distinguish dependency scheduling from storage reads and positional pairing. -/
namespace A12Kernel.Dm.ParallelNumericOperationLocks
open A12Kernel A12Kernel.Dm Lean

private def field (id : FieldId) (group name : String) (kind : FieldKind) : FlatFieldDecl := {
  id, name, groupPath := ["Staffing", group], repeatableScope := [if group == "Demand" then 10 else 20]
  policy := { kind } }
private def number (id : FieldId) (group name : String) :=
  field id group name (.number { scale := 0, signed := true })
private def model : FlatModel := {
  fields := [field 1 "Demand" "Department" .string, number 2 "Demand" "Headcount",
    number 3 "Demand" "Base",
    { field 4 "Demand" "Stamp" (.temporal .date .fullDate) with temporalTargetPolicy := some { format := "yyyy-MM-dd" } },
    field 5 "Supply" "Department" .string, number 6 "Supply" "Headcount",
    number 7 "Supply" "SumOut", number 8 "Supply" "DayOut", number 9 "Supply" "Choice"]
  repeatableGroups := [
    { level := 10, path := ["Staffing", "Demand"], repeatability := some 50, indexField := some 1 },
    { level := 20, path := ["Staffing", "Supply"], repeatability := some 50, indexField := some 5 }] }
private def definition (group target : String) (alternatives : List DmAlternative) : DmComputation := {
  group := ["Staffing", group], name := target, targetRelPath := "../" ++ target,
  alternatives, commonPrecondition := none, errorCodesToSuppress := [] }
private def definitions : List DmComputation := [
  definition "Supply" "SumOut" [{ operation := "Sum(/Staffing/Demand/Headcount, Headcount)", precondition := none }],
  definition "Supply" "DayOut" [{ operation := "DayFromDate(/Staffing/Demand/Stamp) + [Headcount]", precondition := none }],
  definition "Supply" "Choice" [
    { operation := "Sum(/Staffing/Demand/Headcount, Headcount)", precondition := some "[/Staffing/Demand/Headcount] > 10" },
    { operation := "7", precondition := some "FieldFilled(Department)" }],
  definition "Demand" "Headcount" [{ operation := "[Base] + 1", precondition := none }]]
private def demand (key base stamp : String) : Json := Json.mkObj [
  ("Department", Json.str key), ("Base", Json.str base), ("Headcount", "123"), ("Stamp", Json.str stamp)]
private def supply (key amount : String) : Json := Json.mkObj [
  ("Department", Json.str key), ("Headcount", Json.str amount),
  ("SumOut", "999"), ("DayOut", "999"), ("Choice", "999")]
private def run (demandRows supplyRows : List Json) (computations := definitions) : Option (List (String × String)) := do
  let dm : DmModel := {
    flat := model, rules := [], computations, conditionLanguage := "en_US", refusals := [] }
  let input ← (readDocument dm (Json.mkObj [("Staffing", Json.mkObj [
    ("Demand", Json.arr demandRows.toArray), ("Supply", Json.arr supplyRows.toArray)])])).toOption
  if !input.refusals.isEmpty then none
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  let steps ← computations.mapM fun definition => (lowerComputation model .english definition).toOption.map (·.2)
  pure (((← (runComputations world prepared checked steps).toOption).map fun value =>
    (value.pointer, value.outcome)).mergeSort fun a b => a.1 ≤ b.1)

example : definitions.all (fun definition => (lowerComputation model .english definition).isOk) = true := by native_decide

example : run [demand "A" "9" "2026-10-03", demand "B" "19" "2026-10-08"] [supply "B" "2", supply "A" "1"] = some [
    ("Staffing/Demand/Headcount", "value 10"), ("Staffing/Demand[2]/Headcount", "value 20"),
    ("Staffing/Supply/Choice", "value 22"), ("Staffing/Supply/DayOut", "value 10"), ("Staffing/Supply/SumOut", "value 22"),
    ("Staffing/Supply[2]/Choice", "value 7"), ("Staffing/Supply[2]/DayOut", "value 4"), ("Staffing/Supply[2]/SumOut", "value 11")] := by native_decide

example : run [demand "A" "9" "2026-10-08"] [supply "C" "2"] = some [
    ("Staffing/Demand/Headcount", "value 10"), ("Staffing/Supply/Choice", "value 7"),
    ("Staffing/Supply/DayOut", "value 2"), ("Staffing/Supply/SumOut", "value 2")] := by native_decide

example : run [demand "A" "9" ""] [supply "A" "2"] = some [
    ("Staffing/Demand/Headcount", "value 10"), ("Staffing/Supply/Choice", "value 7"),
    ("Staffing/Supply/DayOut", "value 2"), ("Staffing/Supply/SumOut", "value 12")] := by native_decide

example : run [demand "A" "19" "bad"] [supply "A" "2"] = some [
    ("Staffing/Demand/Headcount", "value 20"), ("Staffing/Supply/Choice", "value 22"),
    ("Staffing/Supply/DayOut", "cleared"), ("Staffing/Supply/SumOut", "value 22")] := by native_decide

example : run [demand "A" "bad" "2026-10-08"] [supply "A" "2"] = some [
    ("Staffing/Demand/Headcount", "cleared"), ("Staffing/Supply/Choice", "cleared"),
    ("Staffing/Supply/DayOut", "value 10"), ("Staffing/Supply/SumOut", "cleared")] := by native_decide

example : run [demand "A" "" "2026-10-08"] [supply "A" "2"] = some [
    ("Staffing/Demand/Headcount", "value 1"), ("Staffing/Supply/Choice", "value 7"),
    ("Staffing/Supply/DayOut", "value 10"), ("Staffing/Supply/SumOut", "value 3")] := by native_decide

example : [
    ("Sum(/Staffing/Demand/Headcount, SumOut)", none),
    ("Sum(/Staffing/Demand/Headcount, /Staffing/Demand/Headcount)", none),
    ("Sum(/Staffing/Demand/Headcount)", none),
    ("DayFromDate(/Staffing/Demand/Headcount)", none),
    ("[/Staffing/Demand/Headcount]", some "[/Staffing/Demand/Department] > 10")].all (fun (operation, guard) =>
      !(lowerComputation model .english (definition "Supply" "SumOut"
        [{ operation, precondition := guard }])).isOk) = true := by native_decide

private def guardedChoice (guard : String) : DmComputation :=
  definition "Supply" "Choice" [{ operation := "7", precondition := some guard }]

private def guardedChoiceFallback (guard : String) : DmComputation :=
  definition "Supply" "Choice" [
    { operation := "7", precondition := some guard },
    { operation := "11", precondition := some "FieldFilled(Headcount)" }]

example : run [demand "A" "9" "2026-10-03"] [supply "A" "2"]
    [guardedChoice "Sum(/Staffing/Demand/Headcount, Headcount) > 10"] =
    some [("Staffing/Supply/Choice", "value 7")] := by native_decide

example : run [demand "A" "9" "2026-10-03"] [supply "A" "2"]
    [guardedChoice "DayFromDate(/Staffing/Demand/Stamp) > 2"] =
    some [("Staffing/Supply/Choice", "value 7")] := by native_decide

-- These guard compositions are internal controls; the captured joined-operation matrix lives at
-- docs/sources/computation-scheduling-probes.md#src-parallel-numeric-operations.
example : [
    ("Sum", "124", "125"), ("MinValue", "1", "2"),
    ("MaxValue", "122", "123"), ("NumberOfDifferentValues", "1", "2")].all
    (fun (operator, trueThreshold, falseThreshold) =>
      run [demand "A" "9" "2026-10-03"] [supply "A" "2"]
        [guardedChoice (operator ++ "(/Staffing/Demand/Headcount, Headcount) > " ++ trueThreshold)] ==
          some [("Staffing/Supply/Choice", "value 7")] &&
      run [demand "A" "9" "2026-10-03"] [supply "A" "2"]
        [guardedChoice (operator ++ "(/Staffing/Demand/Headcount, Headcount) > " ++ falseThreshold)] ==
          some [("Staffing/Supply/Choice", "cleared")]) = true := by native_decide

example : run [demand "A" "9" "2026-10-03", demand "B" "19" "2026-10-08"]
    [supply "B" "2", supply "A" "1"]
    [guardedChoice "Sum(/Staffing/Demand/Headcount, Headcount) > 20",
      definition "Demand" "Headcount" [{ operation := "[Base] + 1", precondition := none }]] = some [
    ("Staffing/Demand/Headcount", "value 10"), ("Staffing/Demand[2]/Headcount", "value 20"),
    ("Staffing/Supply/Choice", "value 7"), ("Staffing/Supply[2]/Choice", "cleared")] := by native_decide

example : [
    "DayFromDate(/Staffing/Demand/Stamp) > 2",
    "FieldNotFilled(Headcount) And DayFromDate(/Staffing/Demand/Stamp) > 2",
    "FieldFilled(Headcount) Or DayFromDate(/Staffing/Demand/Stamp) > 2"].map (fun guard =>
      run [demand "A" "9" "bad"] [supply "A" "2"] [guardedChoiceFallback guard]) = [
    some [("Staffing/Supply/Choice", "cleared")], some [("Staffing/Supply/Choice", "value 11")],
    some [("Staffing/Supply/Choice", "value 7")]] := by native_decide

example : [
    ("C", "2026-10-03", "Sum(/Staffing/Demand/Headcount, Headcount) == 2"),
    ("C", "2026-10-03", "DayFromDate(/Staffing/Demand/Stamp) == 0"),
    ("A", "", "DayFromDate(/Staffing/Demand/Stamp) == 0"),
    ("A", "bad", "DayFromDate(/Staffing/Demand/Stamp) == 0")].map (fun (key, stamp, guard) =>
      run [demand "A" "9" stamp] [supply key "2"] [guardedChoiceFallback guard]) = [
    some [("Staffing/Supply/Choice", "value 7")], some [("Staffing/Supply/Choice", "value 7")],
    some [("Staffing/Supply/Choice", "value 7")], some [("Staffing/Supply/Choice", "cleared")]] := by native_decide

example : [
    ("DayFromDate(/Staffing/Demand/Headcount) > 2", "DayFromDate(/Staffing/Demand/Stamp) > 2"),
    ("HoursFromTime(/Staffing/Demand/Stamp) > 2", "DayFromDate(/Staffing/Demand/Stamp) > 2"),
    ("Sum(/Staffing/Demand/Headcount, /Staffing/Demand/Headcount) > 10", "Sum(/Staffing/Demand/Headcount, Headcount) > 10"),
    ("Sum(/Staffing/Demand/Headcount) > 10", "Sum(/Staffing/Demand/Headcount, Headcount) > 10"),
    ("Sum(/Staffing/Demand/Headcount, Choice) > 10", "Sum(/Staffing/Demand/Headcount, Headcount) > 10")].all
    (fun (refused, admitted) =>
      !(lowerComputation model .english (guardedChoice refused)).isOk &&
      (lowerComputation model .english (guardedChoice admitted)).isOk) = true := by native_decide

end A12Kernel.Dm.ParallelNumericOperationLocks
