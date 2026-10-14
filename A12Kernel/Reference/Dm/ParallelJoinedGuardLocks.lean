import Lean.Data.Json
import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Document

/-! # Ordinary guard leaves beside a key join

Reader-to-evaluator locks for joined computation guards whose leaves the instance view cannot
check: a clock read, a starred or filtered aggregate, a keyed read of a third or of the partner
group, and a pattern test. Each such leaf keeps its ordinary meaning at the common row, beside the
joined operation `[/Staffing/Demand/Base] + [Headcount]`. The model and documents are reductions of
the retained Kernel 30.8.1 capture
`evidence/kernel-30.8.1/captures/joined-carrier-admission-2026-10-14/`, whose clock this world
pins; every expectation is the capture's own change.

The documents separate a matched partner, an unmatched row whose partner reads as empty, a clock
read on each side of the join, and a filtered aggregate, keyed read or keyed partner read that
selects nothing.
-/

namespace A12Kernel.Dm.ParallelJoinedGuardLocks

open Lean A12Kernel

private def element (kind id name : String) (body : List (String × Json)) : Json :=
  Json.mkObj [("type", .str kind), ("id", .str id), ("name", .str name), (kind, Json.mkObj body)]

private def field (group name : String) (fieldType : Json) : Json :=
  element "Field" s!"/Staffing/{group}/{name}" name [("fieldType", fieldType)]

private def text : Json := Json.mkObj [("type", "StringType")]
private def number : Json :=
  Json.mkObj [("type", "NumberType"), ("NumberType", Json.mkObj [("maxFractionalDigits", toJson 0)])]
private def date : Json :=
  Json.mkObj [("type", "DateType"), ("DateType", Json.mkObj [("format", "yyyy-MM-dd")])]

private def keyed (name key : String) (fields : List Json) : Json :=
  element "Group" s!"/Staffing/{name}" name [("repeatability", toJson 50),
    ("elements", Json.arr (field name key text :: fields).toArray), ("indexFieldName", .str key)]

private def guards : List (String × String) := [
  ("Out01", "[/Staffing/Demand/Stamp] > Today"),
  ("Out02", "[Due] > Today"),
  ("Out03", "Sum(/Staffing/Demand*/Base) > 0"),
  ("Out04", "Sum(/Staffing/Supply*/Headcount) > 0"),
  ("Out05", "Sum(/Staffing/Demand*/Base Having [/Staffing/Demand/Headcount] > 0) > 0"),
  ("Out06", "[/Staffing/Ledger/Amount For \"k1\"] > 0"),
  ("Out07", "[/Staffing/Demand/Base For \"A\"] > 0"),
  ("Out08", "[Note] PatternMatched \"[A-Z]+\""),
  ("Out10", "AtLeastOneFieldFilled(/Staffing/Demand*/Base)")]

private def computation (target guard : String) : Json :=
  element "Computation" s!"/Staffing/Supply/C{target}" s!"C{target}" [("computedFieldRelPath", .str s!"../{target}"),
    ("computationAlternatives", Json.arr #[Json.mkObj [("precondition", .str guard),
      ("operation", "[/Staffing/Demand/Base] + [Headcount]")]]),
    ("errorMessage", Json.arr #[Json.mkObj [("locale", "en_US"), ("text", "m")]])]

private def dm? : Option DmModel :=
  (readModel (Json.mkObj [("content", Json.mkObj [("modelRoot", Json.mkObj [("rootGroups", Json.arr #[
    element "Group" "/Staffing" "Staffing" [("repeatability", toJson 1), ("elements", Json.arr #[
      element "Field" "/Staffing/PlanName" "PlanName" [("fieldType", text)],
      keyed "Demand" "Department" [field "Demand" "Headcount" number, field "Demand" "Base" number,
        field "Demand" "Stamp" date],
      keyed "Supply" "Department" ([field "Supply" "Headcount" number, field "Supply" "Note" text,
        field "Supply" "Due" date] ++ guards.map (fun (target, _) => field "Supply" target number) ++
        guards.map (fun (target, guard) => computation target guard)),
      keyed "Ledger" "Code" [field "Ledger" "Amount" number]])]])])])])).toOption

-- The capture's clock, 2026-10-14T10:00:00Z.
private def world : World := { now := { epochMillis := 1791972000000 }, modelZoneRules := ModelZone.concreteRules }

private def row (entries : List (String × String)) : Json :=
  Json.mkObj (entries.map fun (key, value) => (key, Json.str value))

private def outs : List (String × String) := guards.map (·.1, "999")

private def staffing (groups : List (String × List (List (String × String)))) (fixed : List (String × String) := []) : Json :=
  Json.mkObj [("Staffing", Json.mkObj (fixed.map (fun (key, value) => (key, Json.str value)) ++
    groups.map fun (name, rows) => (name, Json.arr (rows.map row).toArray)))]

/-- Every reported target change, as `pointer outcome`. -/
private def computed (document : Json) : Option (List String) := do
  let dm ← dm?
  let input ← (readDocument dm document).toOption
  if !input.refusals.isEmpty then none
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler dm.flat).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  let lowered ← dm.computations.mapM fun source => (lowerComputation dm.flat .english source).toOption
  let outcomes ← (runComputations world prepared checked (lowered.map (·.2))).toOption
  pure (outcomes.map fun outcome => s!"{outcome.pointer} {outcome.outcome}")

private def changes (row : String) (outcomes : List String) : List String :=
  (guards.zip outcomes).map fun ((target, _), outcome) => s!"Staffing/Supply{row}/{target} {outcome}"

-- Row C has no partner: its clock read on the partner side decides nothing, its own `Due` does.
example : (computed (staffing [
    ("Ledger", [[("Code", "k1"), ("Amount", "4")], [("Code", "x"), ("Amount", "9")]]),
    ("Demand", [[("Department", "A"), ("Base", "10"), ("Headcount", "1"), ("Stamp", "2026-10-01")],
      [("Department", "B"), ("Base", "20"), ("Stamp", "2026-11-20")]]),
    ("Supply", [[("Department", "A"), ("Headcount", "1"), ("Note", "x"), ("Due", "2026-09-01")] ++ outs,
      [("Department", "B"), ("Headcount", "7"), ("Note", "AB"), ("Due", "2026-12-01")] ++ outs,
      [("Department", "C"), ("Headcount", "3"), ("Note", "k1"), ("Due", "2026-12-01")] ++ outs])])).map
      (·.mergeSort) = some (
    changes "" ["cleared", "cleared", "value 11", "value 11", "value 11", "value 11", "value 11",
      "cleared", "value 11"] ++
    changes "[2]" (List.replicate 9 "value 27") ++
    changes "[3]" ["cleared", "value 3", "value 3", "value 3", "value 3", "value 3", "value 3",
      "cleared", "value 3"]).mergeSort := by native_decide

-- A filter that keeps no row sums to zero; an absent keyed row and a keyed partner without the read
-- field read as empty. Each guard fails and clears its target.
example : (computed (staffing [
    ("Demand", [[("Department", "A"), ("Headcount", "0")],
      [("Department", "B"), ("Base", "5"), ("Stamp", "2026-01-01")]]),
    ("Supply", [[("Department", "A")] ++ outs,
      [("Department", "B"), ("Headcount", "2"), ("Due", "2026-02-01"), ("Note", "k1")] ++ outs])]
    [("PlanName", "P")])).map (·.mergeSort) = some (
    changes "" ["cleared", "cleared", "value 0", "value 0", "cleared", "cleared", "cleared", "cleared",
      "value 0"] ++
    changes "[2]" ["cleared", "cleared", "value 7", "value 7", "cleared", "cleared", "cleared", "cleared",
      "value 7"]).mergeSort := by native_decide

end A12Kernel.Dm.ParallelJoinedGuardLocks
