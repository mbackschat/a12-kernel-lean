import Lean.Data.Json
import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Document
import A12Kernel.Reference.Dm.GeneratedComputationRule
import A12Kernel.Reference.Dm.ParallelValidation
import A12Kernel.Reference.Dm.EntryFrameFixture

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

The last section copies an Enumeration and a Date into targets nested below an unjoined repeatable
group, a reduction of `evidence/kernel-30.8.1/captures/runtime-open-cells-2026-10-28/` (`join-*` rows).
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
  (readModel (checkedEntryFrame <| Json.mkObj [("content", Json.mkObj [("modelRoot", Json.mkObj [("rootGroups", Json.arr #[
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
private def computed (document : Json) (model? : Option DmModel := dm?) : Option (List String) := do
  let dm ← model?
  let input ← (readDocument dm document).toOption
  if !input.refusals.isEmpty then none
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler dm.flat).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  let lowered ← dm.computations.mapM fun source => (lowerComputation dm.flat .english source).toOption
  let outcomes ← (runComputations world prepared checked (lowered.map (·.2))).toOption
  pure (outcomes.map fun outcome => s!"{outcome.pointer} {outcome.outcome}")

/-- Each generated rule's firings, as `code pointer type`. -/
private def fired (document : Json) (model? : Option DmModel := dm?) : Option (List String) := do
  let dm ← model?
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

/-! ### An Enumeration target nested below an unjoined repeatable group

`Join/Lines/Slots/TKind` copies the `Kind` of the root-level `Refs` row its key matches, and
`KindCopy` copies `TKind` within its own row. `Lines` repeats but joins nothing, so the instance view
keeps the target repeatable. Each target is seeded `B`, which no partner holds. -/

private def joinField (path name : String) (fieldType : Json) : Json :=
  element "Field" s!"{path}/{name}" name [("fieldType", fieldType)]

private def kind : Json := Json.mkObj [("type", "EnumerationType"), ("EnumerationType",
  Json.mkObj [("values", Json.arr #[Json.mkObj [("value", "A")], Json.mkObj [("value", "B")]])])]

private def slotComputation (name target operation : String) : Json :=
  element "Computation" s!"/Join/Lines/Slots/{name}" name [("computedFieldRelPath", .str s!"../{target}"),
    ("computationAlternatives", Json.arr #[Json.mkObj [("operation", .str operation)]]),
    ("errorMessage", Json.arr #[Json.mkObj [("locale", "en_US"), ("text", "m")]])]

/-- `Join` with `Refs` holding `refFields` beside its key and `Lines/Slots` holding `slotElements`. -/
private def joinDm? (refFields slotElements : List Json) : Option DmModel :=
  let slots := element "Group" "/Join/Lines/Slots" "Slots" [("repeatability", toJson 3),
    ("indexFieldName", "Key"), ("elements", Json.arr (joinField "/Join/Lines/Slots" "Key" text :: slotElements).toArray)]
  (readModel (checkedEntryFrame <| Json.mkObj [("content", Json.mkObj [("modelRoot", Json.mkObj [("rootGroups", Json.arr #[
    element "Group" "/Join" "Join" [("repeatability", toJson 1), ("elements", Json.arr #[
      element "Group" "/Join/Refs" "Refs" [("repeatability", toJson 3), ("indexFieldName", "Key"),
        ("elements", Json.arr (joinField "/Join/Refs" "Key" text :: refFields).toArray)],
      element "Group" "/Join/Lines" "Lines" [("repeatability", toJson 2),
        ("elements", Json.arr #[joinField "/Join/Lines" "LNote" text, slots])]])]])])])])).toOption

private def nestedDm? : Option DmModel :=
  joinDm? [joinField "/Join/Refs" "Kind" kind] [
    joinField "/Join/Lines/Slots" "TKind" kind, joinField "/Join/Lines/Slots" "KindCopy" kind,
    slotComputation "CTKind" "TKind" "[../../Refs/Kind]",
    slotComputation "CKindCopy" "KindCopy" "[TKind]"]

private def joinDocument (refs : List String) (lines : List (List String))
    (refEntries : List (String × String) := [("Kind", "A")])
    (slotEntries : List (String × String) := [("TKind", "B"), ("KindCopy", "B")]) : Json :=
  Json.mkObj [("Join", Json.mkObj [
    ("Refs", Json.arr (refs.map fun key => row (("Key", key) :: refEntries)).toArray),
    ("Lines", Json.arr (lines.map fun keys => Json.mkObj [("LNote", "l"), ("Slots", Json.arr (keys.map fun key =>
      row (("Key", key) :: slotEntries)).toArray)]).toArray)])]

-- Distinct keys copy the partner's token, and the row copy follows it (`join-distinct`).
example : (computed (joinDocument ["a", "b"] [["a", "b"]]) nestedDm?).map (·.mergeSort) = some [
    "Join/Lines/Slots/KindCopy value A", "Join/Lines/Slots/TKind value A",
    "Join/Lines/Slots[2]/KindCopy value A", "Join/Lines/Slots[2]/TKind value A"] := by native_decide

-- A key repeated within one line clears both of its rows and poisons their row copies, while the
-- other line still copies (`join-own-duplicate`); an unmatched key clears its row
-- (`join-own-unmatched`).
example : (computed (joinDocument ["a", "b"] [["a", "a"], ["b"]]) nestedDm?).map (·.mergeSort) = some [
    "Join/Lines/Slots/KindCopy cleared", "Join/Lines/Slots/TKind cleared",
    "Join/Lines/Slots[2]/KindCopy cleared", "Join/Lines/Slots[2]/TKind cleared",
    "Join/Lines[2]/Slots/KindCopy value A", "Join/Lines[2]/Slots/TKind value A"] ∧
  (computed (joinDocument ["a", "b"] [["a", "z"]]) nestedDm?).map (·.mergeSort) = some [
    "Join/Lines/Slots/KindCopy value A", "Join/Lines/Slots/TKind value A",
    "Join/Lines/Slots[2]/KindCopy cleared", "Join/Lines/Slots[2]/TKind cleared"] := by native_decide

-- The generated rule fires VALUE at each seeded row its copy changes.
example : (fired (joinDocument ["a", "b"] [["a", "b"]]) nestedDm?).map (·.filter (·.startsWith "CTKind")) = some [
    "CTKind Join/Lines/Slots/TKind A12Kernel.Polarity.value",
    "CTKind Join/Lines/Slots[2]/TKind A12Kernel.Polarity.value"] := by native_decide

/- The Date twin, `CTOn` of the same capture: its generated rule compares two Dates, which has no
pair form, over a target the instance view keeps repeatable below `Lines`. -/
private def datedDm? : Option DmModel :=
  joinDm? [joinField "/Join/Refs" "On" date] [
    joinField "/Join/Lines/Slots" "TOn" date, slotComputation "CTOn" "TOn" "[../../Refs/On]"]

private def datedDocument (lines : List (List String) := [["a", "b"]]) : Json :=
  joinDocument ["a", "b"] lines (refEntries := [("On", "2024-01-01")]) (slotEntries := [("TOn", "2000-01-01")])

-- The copy changes each seeded row, and the generated rule fires VALUE at both (`join-distinct`).
example : (computed datedDocument datedDm?).map (·.mergeSort) = some [
    "Join/Lines/Slots/TOn value 2024-01-01", "Join/Lines/Slots[2]/TOn value 2024-01-01"] ∧
  fired datedDocument datedDm? = some [
    "CTOn Join/Lines/Slots/TOn A12Kernel.Polarity.value",
    "CTOn Join/Lines/Slots[2]/TOn A12Kernel.Polarity.value"] := by native_decide

-- An unmatched row reads its partner's Date empty, and a key repeated within one line clears both
-- rows, so neither fires (`join-own-unmatched`, `join-own-duplicate`).
example : fired (datedDocument [["a", "z"]]) datedDm? = some ["CTOn Join/Lines/Slots/TOn A12Kernel.Polarity.value"] ∧
    fired (datedDocument [["a", "a"], ["b"]]) datedDm? =
      some ["CTOn Join/Lines[2]/Slots/TOn A12Kernel.Polarity.value"] := by native_decide

end A12Kernel.Dm.ParallelJoinedRowLocks
