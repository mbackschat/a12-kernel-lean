import Lean.Data.Json
import A12Kernel.Reference.Dm.Document
import A12Kernel.Reference.Dm.Validate
import A12Kernel.Elaboration.ValidationCondition.Omission

/-! # Keyed reads below a selected repeatable group

Reader-to-evaluator locks for a key over a repeatable index read from a rule that iterates a
repeatable level below it. The selection replaces only the indexed group's coordinate: each level
below it the rule binds keeps the firing row, in the read and in `referenced`, a star below it
reopens its level, and a row the selected group lacks reads empty. The documents are those of the
retained Kernel 30.8.1 capture `evidence/kernel-30.8.1/captures/below-key-selection-2026-10-28/`,
and the model keeps its rules `S1`–`S4`; each expectation is the capture's codes, error fields and
references for those rules, without message types or fill-to-fix lists. -/

namespace A12Kernel.Dm.BelowKeySelectionLocks

open Lean A12Kernel

private def element (kind id name : String) (body : List (String × Json)) : Json :=
  Json.mkObj [("type", .str kind), ("id", .str id), ("name", .str name), (kind, Json.mkObj body)]

private def text : Json := Json.mkObj [("type", "StringType")]
private def number : Json :=
  Json.mkObj [("type", "NumberType"), ("NumberType", Json.mkObj [("maxFractionalDigits", toJson 0)])]

private def field (path name : String) (fieldType : Json) : Json :=
  element "Field" s!"{path}/{name}" name [("fieldType", fieldType)]

private def group (path name : String) (repeatability : Nat) (index : Option String)
    (elements : List Json) : Json :=
  element "Group" s!"{path}/{name}" name ([("repeatability", toJson repeatability),
    ("elements", Json.arr elements.toArray)] ++ (index.map fun key => [("indexFieldName", Json.str key)]).getD [])

private def message : Json := Json.arr #[Json.mkObj [("locale", "en_US"), ("text", "m")]]

private def rule (path name entity condition : String) : Json :=
  element "Rule" s!"{path}/{name}" name [("errorEntityRelPath", .str entity), ("errorCode", .str name),
    ("errorCondition", .str condition), ("severity", "ERROR"), ("errorMessage", message)]

private def dm? : Option DmModel :=
  let cells := group "/Depot/Bins/Slots" "Cells" 3 none [field "/Depot/Bins/Slots/Cells" "Q" number,
    field "/Depot/Bins/Slots/Cells" "CNote" text,
    rule "/Depot/Bins/Slots/Cells" "S4" "../CNote" "FieldFilled(CNote) And [Q For \"b\"] > 0"]
  let slots := group "/Depot/Bins" "Slots" 3 none [field "/Depot/Bins/Slots" "Qty" number,
    field "/Depot/Bins/Slots" "Note" text, cells,
    rule "/Depot/Bins/Slots" "S1" "../Note" "FieldFilled(Note) And [Qty For \"b\"] > 0",
    rule "/Depot/Bins/Slots" "S2" "../Note" "FieldFilled(Note) And FieldNotFilled(Qty For \"b\")",
    rule "/Depot/Bins/Slots" "S3" "../Note" "FieldFilled(Note) And Sum(Cells*/Q For \"b\") > 0"]
  let bins := group "/Depot" "Bins" 4 (some "BinCode") [field "/Depot/Bins" "BinCode" text,
    field "/Depot/Bins" "BinNote" text, slots]
  (readModel (Json.mkObj [("content", Json.mkObj [("modelRoot", Json.mkObj [("rootGroups", Json.arr #[
    group "" "Depot" 1 none [field "/Depot" "Ref" text, bins]])])])])).toOption

private def world : World := { now := { epochMillis := 0 } }

private def cell (q : Nat) (note : Option String := none) : Json :=
  Json.mkObj ([("Q", Json.str (toString q))] ++ (note.map fun note => [("CNote", Json.str note)]).getD [])

/-- The capture's noted slots of bin `a`: slot `i` holds `Qty` `i + 1` and two noted cells. -/
private def notedSlots (count : Nat) : List Json :=
  (List.range count).map fun i => Json.mkObj [("Qty", Json.str (toString (i + 1))),
    ("Note", Json.str s!"n{i + 1}"), ("Cells", Json.arr #[cell (10 + i) "c1", cell (20 + i) "c2"])]

/-- The capture's unnoted slots of a selected bin: slot `i` holds `Qty` `3 + i` and three cells. -/
private def plainSlots (count : Nat) : List Json :=
  (List.range count).map fun i => Json.mkObj [("Qty", Json.str (toString (3 + i))),
    ("Cells", Json.arr #[cell (5 + i), cell (6 + i), cell (7 + i)])]

private def bin (code : String) (slots : List Json) (note : Bool := false) : Json :=
  Json.mkObj ([("BinCode", Json.str code)] ++ (if note then [("BinNote", Json.str "x")] else []) ++
    [("Slots", Json.arr slots.toArray)])

private def depot (bins : List Json) : Json :=
  Json.mkObj [("Depot", Json.mkObj [("Ref", Json.str "b"), ("Bins", Json.arr bins.toArray)])]

/-- Every rule's firings with their sorted references, as `code pointer referenced`. -/
private def fired (document : Json) : Option (List String) := do
  let dm ← dm?
  let input ← (readDocument dm document).toOption
  if !input.refusals.isEmpty then none
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler dm.flat).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  let base ← (checked.applyFullIndexPreliminary.toOption.bind (·.messageReferenceInputs.toOption))
  let messages ← dm.rules.mapM fun source => do
    let rule ← (checkRule dm .english source).toOption
    let (_, results) ← (rule.fullRowsAndRepetitionResults checked).toOption
    let inputs := { base with repetitionAt := some fun environment => results.find? (·.row == environment) }
    let fired ← (runRuleAt world checked rule).toOption
    fired.mapM fun (environment, message) => do
      let found ← (rule.condition.core.messageReferences message environment (some inputs)).toOption
      let sorted := (found.referenced.map (renderFieldPointer dm.flat)).eraseDups.mergeSort (compare · · != .gt)
      pure s!"{source.errorCode} {renderPointer dm.flat message.errorAddress} {sorted}"
  pure (messages.flatten.mergeSort (compare · · != .gt))

/- `bk-other`: each noted slot of bin `a` reads bin `b` at its own slot row, and a cell at its own
   cell row, while the star keeps the wildcard on the level it reopens. -/
example : fired (depot [bin "a" (notedSlots 2) true, bin "b" (plainSlots 3)]) = some [
    "S1 Depot/Bins/Slots/Note [Depot/Bins/Slots/Note, Depot/Bins[2]/BinCode, Depot/Bins[2]/Slots/Qty]",
    "S1 Depot/Bins/Slots[2]/Note [Depot/Bins/Slots[2]/Note, Depot/Bins[2]/BinCode, Depot/Bins[2]/Slots[2]/Qty]",
    "S3 Depot/Bins/Slots/Note [/Depot[1]/Bins[2]/Slots[1]/Cells[0]/Q, Depot/Bins/Slots/Note, Depot/Bins[2]/BinCode]",
    "S3 Depot/Bins/Slots[2]/Note [/Depot[1]/Bins[2]/Slots[2]/Cells[0]/Q, Depot/Bins/Slots[2]/Note, Depot/Bins[2]/BinCode]",
    "S4 Depot/Bins/Slots/Cells/CNote [Depot/Bins/Slots/Cells/CNote, Depot/Bins[2]/BinCode, Depot/Bins[2]/Slots/Cells/Q]",
    "S4 Depot/Bins/Slots/Cells[2]/CNote [Depot/Bins/Slots/Cells[2]/CNote, Depot/Bins[2]/BinCode, Depot/Bins[2]/Slots/Cells[2]/Q]",
    "S4 Depot/Bins/Slots[2]/Cells/CNote [Depot/Bins/Slots[2]/Cells/CNote, Depot/Bins[2]/BinCode, Depot/Bins[2]/Slots[2]/Cells/Q]",
    "S4 Depot/Bins/Slots[2]/Cells[2]/CNote [Depot/Bins/Slots[2]/Cells[2]/CNote, Depot/Bins[2]/BinCode, Depot/Bins[2]/Slots[2]/Cells[2]/Q]"]
  := by native_decide

/- `bk-short`: the selected bin holds one slot, so slots 2 and 3 of bin `a` read empty there and
   reference a row the selected bin lacks. -/
example : fired (depot [bin "a" (notedSlots 3) true,
    bin "b" [Json.mkObj [("Qty", Json.str "3"), ("Cells", Json.arr #[cell 5])]]]) = some [
    "S1 Depot/Bins/Slots/Note [Depot/Bins/Slots/Note, Depot/Bins[2]/BinCode, Depot/Bins[2]/Slots/Qty]",
    "S2 Depot/Bins/Slots[2]/Note [Depot/Bins/Slots[2]/Note, Depot/Bins[2]/BinCode, Depot/Bins[2]/Slots[2]/Qty]",
    "S2 Depot/Bins/Slots[3]/Note [Depot/Bins/Slots[3]/Note, Depot/Bins[2]/BinCode, Depot/Bins[2]/Slots[3]/Qty]",
    "S3 Depot/Bins/Slots/Note [/Depot[1]/Bins[2]/Slots[1]/Cells[0]/Q, Depot/Bins/Slots/Note, Depot/Bins[2]/BinCode]",
    "S4 Depot/Bins/Slots/Cells/CNote [Depot/Bins/Slots/Cells/CNote, Depot/Bins[2]/BinCode, Depot/Bins[2]/Slots/Cells/Q]"]
  := by native_decide

/- `bk-missing`: no row carries the key, so the selected coordinate is unknown while the firing
   slot's row survives below it. -/
example : fired (depot [bin "a" (notedSlots 2) true, bin "c" (plainSlots 2)]) = some [
    "S2 Depot/Bins/Slots/Note [/Depot[1]/Bins[-5]/BinCode, /Depot[1]/Bins[-5]/Slots[1]/Qty, Depot/Bins/Slots/Note]",
    "S2 Depot/Bins/Slots[2]/Note [/Depot[1]/Bins[-5]/BinCode, /Depot[1]/Bins[-5]/Slots[2]/Qty, Depot/Bins/Slots[2]/Note]"]
  := by native_decide

/- `bk-duplicate`: two rows carry the key, so every keyed read is unknown and no rule fires. -/
example : fired (depot [bin "a" (notedSlots 1) true, bin "b" (plainSlots 1), bin "b" (plainSlots 1)]) = some []
  := by native_decide

end A12Kernel.Dm.BelowKeySelectionLocks
