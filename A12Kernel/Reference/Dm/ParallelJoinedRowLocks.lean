import Lean.Data.Json
import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Document
import A12Kernel.Reference.Dm.GeneratedComputationRule
import A12Kernel.Reference.Dm.ParallelValidation

/-! # String and Date targets beside a key join

Reader-to-evaluator locks for a String and a Date row target whose operation copies a field of the
partner row the target's key matches: `[/Staffing/Demand/Label]` guarded and unguarded, and
`[/Staffing/Demand/Stamp]` guarded, each with its generated rule. The model and documents are
reductions of the retained Kernel 30.8.1 capture
`evidence/kernel-30.8.1/captures/joined-carrier-admission-2026-10-14/`; every expectation is the
capture's own change or message.

The documents separate a partner holding the copied field, a partner holding only the other one, and
a target row without a partner. The capture's one failing guard meets a partner holding neither field,
so no row separates the guard from the copy.
-/

namespace A12Kernel.Dm.ParallelJoinedRowLocks

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

private def computation (name target operation : String) (guard : Option String) : Json :=
  element "Computation" s!"/Staffing/Supply/{name}" name [("computedFieldRelPath", .str s!"../{target}"),
    ("computationAlternatives", Json.arr #[Json.mkObj ((guard.map fun guard =>
      [("precondition", Json.str guard)]).getD [] ++ [("operation", .str operation)])]),
    ("errorMessage", Json.arr #[Json.mkObj [("locale", "en_US"), ("text", "m")]])]

private def dm? : Option DmModel :=
  (readModel (Json.mkObj [("content", Json.mkObj [("modelRoot", Json.mkObj [("rootGroups", Json.arr #[
    element "Group" "/Staffing" "Staffing" [("repeatability", toJson 1), ("elements", Json.arr #[
      keyed "Demand" "Department" [field "Demand" "Label" text, field "Demand" "Stamp" date],
      keyed "Supply" "Department" [field "Supply" "Headcount" number, field "Supply" "OutS1" text,
        field "Supply" "OutS2" text, field "Supply" "OutD1" date,
        computation "Ct01" "OutS1" "[/Staffing/Demand/Label]" (some "FieldFilled(Headcount)"),
        computation "Ct02" "OutS2" "[/Staffing/Demand/Label]" none,
        computation "Ct03" "OutD1" "[/Staffing/Demand/Stamp]" (some "FieldFilled(Headcount)")]])]])])])])).toOption

-- The capture's clock, 2026-10-14T10:00:00Z.
private def world : World := { now := { epochMillis := 1791972000000 }, modelZoneRules := ModelZone.concreteRules }

private def row (entries : List (String × String)) : Json :=
  Json.mkObj (entries.map fun (key, value) => (key, Json.str value))

private def outs : List (String × String) := [("OutS1", "zz"), ("OutS2", "zz"), ("OutD1", "2000-01-01")]

private def staffing (demand supply : List (List (String × String))) : Json :=
  Json.mkObj [("Staffing", Json.mkObj [("Demand", Json.arr (demand.map row).toArray),
    ("Supply", Json.arr (supply.map fun entries => row (entries ++ outs)).toArray)])]

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

/-- Each generated rule's firings, as `code pointer type`. -/
private def fired (document : Json) : Option (List String) := do
  let dm ← dm?
  let input ← (readDocument dm document).toOption
  if !input.refusals.isEmpty then none
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler dm.flat).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  let generated ← dm.computations.mapM (·.generatedRule? .english)
  let messages ← generated.mapM fun source => do
    let plan ← (checkValidationRule dm .english source world).toOption
    let fired ← (runValidationRule world checked plan).toOption
    pure (fired.map fun message =>
      s!"{source.errorCode} {renderPointer dm.flat message.errorAddress} {reprStr message.messageType}")
  pure messages.flatten

private def matched : Json := staffing
  [[("Department", "A"), ("Label", "LA"), ("Stamp", "2026-10-01")],
    [("Department", "B"), ("Stamp", "2026-11-20")]]
  [[("Department", "A"), ("Headcount", "1")], [("Department", "B"), ("Headcount", "7")],
    [("Department", "C"), ("Headcount", "3")]]

private def sparse : Json := staffing
  [[("Department", "A")], [("Department", "B"), ("Stamp", "2026-01-01")]]
  [[("Department", "A")], [("Department", "B"), ("Headcount", "2")]]

-- A partner's field is copied; a partner without it and a row without a partner clear the target.
example : (computed matched).map (·.mergeSort) = some [
    "Staffing/Supply/OutD1 value 2026-10-01", "Staffing/Supply/OutS1 value LA",
    "Staffing/Supply/OutS2 value LA", "Staffing/Supply[2]/OutD1 value 2026-11-20",
    "Staffing/Supply[2]/OutS1 cleared", "Staffing/Supply[2]/OutS2 cleared",
    "Staffing/Supply[3]/OutD1 cleared", "Staffing/Supply[3]/OutS1 cleared",
    "Staffing/Supply[3]/OutS2 cleared"] := by native_decide

-- A partner holding the Date but not the String copies the one and clears the other.
example : (computed sparse).map (·.mergeSort) = some [
    "Staffing/Supply/OutD1 cleared", "Staffing/Supply/OutS1 cleared", "Staffing/Supply/OutS2 cleared",
    "Staffing/Supply[2]/OutD1 value 2026-01-01", "Staffing/Supply[2]/OutS1 cleared",
    "Staffing/Supply[2]/OutS2 cleared"] := by native_decide

example : fired matched = some [
    "Ct01 Staffing/Supply/OutS1 A12Kernel.Polarity.value",
    "Ct02 Staffing/Supply/OutS2 A12Kernel.Polarity.value",
    "Ct03 Staffing/Supply/OutD1 A12Kernel.Polarity.value",
    "Ct03 Staffing/Supply[2]/OutD1 A12Kernel.Polarity.value"] ∧
  fired sparse = some ["Ct03 Staffing/Supply[2]/OutD1 A12Kernel.Polarity.value"] := by native_decide

end A12Kernel.Dm.ParallelJoinedRowLocks
