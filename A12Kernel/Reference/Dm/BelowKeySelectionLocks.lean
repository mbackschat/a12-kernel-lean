import Lean.Data.Json
import A12Kernel.Reference.Dm.Document
import A12Kernel.Reference.Dm.Validate
import A12Kernel.Reference.Dm.Replay
import A12Kernel.Reference.Dm.Compute
import A12Kernel.Elaboration.ValidationCondition.Omission
import A12Kernel.Reference.Dm.EntryFrameFixture

/-! # Keyed reads below a selected repeatable group

Reader-to-evaluator locks for a key over a repeatable index read from a rule that iterates a
repeatable level below it. The selection replaces only the indexed group's coordinate: each level
below it the rule binds keeps the firing row, in the read and in `referenced`, a star below it
reopens its level, and a row the selected group lacks reads empty. The documents are those of the
retained Kernel 30.8.1 capture `evidence/kernel-30.8.1/captures/below-key-selection-2026-10-28/`,
and the model keeps its rules `S1`–`S4`; each expectation is the capture's codes, error fields and
references for those rules, without message types or fill-to-fix lists.

The routes section keeps a row the selected bin lacks below the key, which yields the values and
verdicts of a clean no-match: each rule's firings as `code@pointer:type`, alike in full and partial
validation, and the computed outcomes. References are left to the replay of the retained capture
`evidence/kernel-30.8.1/captures/below-key-routes-2026-10-28/`, whose documents these are.
-/

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

/-- The capture's model with its rules `S1`–`S4`, or with the given slot and cell rules instead. -/
private def dmWith? (slotRules? cellRules? : Option (List Json) := none) : Option DmModel :=
  let cells := group "/Depot/Bins/Slots" "Cells" 3 none ([field "/Depot/Bins/Slots/Cells" "Q" number,
    field "/Depot/Bins/Slots/Cells" "CNote" text] ++ cellRules?.getD
    [rule "/Depot/Bins/Slots/Cells" "S4" "../CNote" "FieldFilled(CNote) And [Q For \"b\"] > 0"])
  let slots := group "/Depot/Bins" "Slots" 3 none ([field "/Depot/Bins/Slots" "Qty" number,
    field "/Depot/Bins/Slots" "Note" text, cells] ++ slotRules?.getD [
    rule "/Depot/Bins/Slots" "S1" "../Note" "FieldFilled(Note) And [Qty For \"b\"] > 0",
    rule "/Depot/Bins/Slots" "S2" "../Note" "FieldFilled(Note) And FieldNotFilled(Qty For \"b\")",
    rule "/Depot/Bins/Slots" "S3" "../Note" "FieldFilled(Note) And Sum(Cells*/Q For \"b\") > 0"])
  let bins := group "/Depot" "Bins" 4 (some "BinCode") [field "/Depot/Bins" "BinCode" text,
    field "/Depot/Bins" "BinNote" text, slots]
  (readModel (checkedEntryFrame <| Json.mkObj [("content", Json.mkObj [("modelRoot", Json.mkObj [("rootGroups", Json.arr #[
    group "" "Depot" 1 none [field "/Depot" "Ref" text, bins]])])])])).toOption

private def dm? : Option DmModel := dmWith?

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

/-! ## Every reading route reads a missing lower row as empty

The model is the routes capture's `BK4_DM` reduced to the rules and computation these locks read. -/

private def date : Json :=
  Json.mkObj [("type", "DateType"), ("DateType", Json.mkObj [("format", "yyyy-MM-dd")])]

private def computationWith (path name target : String) (alternatives : List (Option String × String)) : Json :=
  element "Computation" s!"{path}/{name}" name [("computedFieldRelPath", .str target),
    ("computationAlternatives", Json.arr (alternatives.map fun (precondition, operation) => Json.mkObj
      ((precondition.map fun condition => [("precondition", Json.str condition)]).getD [] ++
        [("operation", .str operation)])).toArray), ("errorMessage", message)]

private def computation (path name target operation : String) : Json :=
  computationWith path name target [(none, operation)]

private def routesDm? (slotExtra cellExtra : List Json := []) : Option DmModel :=
  let path := "/Depot/Bins/Slots"
  let guarded (name condition : String) := rule path name "../Note" s!"FieldFilled(Note) And {condition}"
  let slots := group "/Depot/Bins" "Slots" 3 none ([field path "Qty" number, field path "Note" text,
    field path "When" date, field path "OutD" number,
    group path "Cells" 2 none (field s!"{path}/Cells" "Q" number :: cellExtra),
    guarded "F1" "FirstFilledValue(Qty For \"b\", Qty) > 0",
    guarded "D4" "DayFromDate(When For \"b\") == 0",
    guarded "G1" "GroupFilled(/Depot/Bins/Slots For \"b\")",
    guarded "G2" "GroupNotFilled(/Depot/Bins/Slots For \"b\")",
    computation path "C5" "../OutD" "DayFromDate(When For \"b\")"] ++ slotExtra)
  let bins := group "/Depot" "Bins" 4 (some "BinCode") [field "/Depot/Bins" "BinCode" text,
    field "/Depot/Bins" "BinNote" text, slots]
  (readModel (checkedEntryFrame <| Json.mkObj [
    ("header", Json.mkObj [("locales", Json.arr #[Json.mkObj [("code", "en_US")]])]),
    ("content", Json.mkObj [("modelConfig", Json.mkObj [("timeZone", "Europe/Berlin"),
        ("conditionLanguage", Json.mkObj [("code", "en_US")])]),
      ("modelRoot", Json.mkObj [("rootGroups", Json.arr #[group "" "Depot" 1 none [bins]])])])])).toOption

private def zonedWorld : World := { now := { epochMillis := 0 }, modelZoneRules := ModelZone.concreteRules }

/-- The extents capture adds keyed group presence and fill below the key and a Date
`FirstFilledValue` to the routes model. -/
private def extentsDm? : Option DmModel :=
  let path := "/Depot/Bins/Slots"
  let cells := s!"{path}/Cells"
  let both (operator negated group : String) := [(some s!"{operator}({group} For \"b\")", "1"),
    (some s!"{negated}({group} For \"b\")", "2")]
  routesDm?
    [field path "OutG2" number, field path "OutW2" date, group path "Info" 1 none [field s!"{path}/Info" "Tag" text],
      computationWith path "K1" "../OutG2" (both "GroupFilled" "GroupNotFilled" s!"{path}/Info"),
      computation path "K3" "../OutW2" "FirstFilledValue(When For \"b\", When)",
      rule path "N1" "../Note" s!"FieldFilled(Note) And NumberOfFilledFields({path} For \"b\") > 0"]
    [field cells "OutC" number, group cells "Data" 1 none [field s!"{cells}/Data" "Q2" number],
      computationWith cells "K2" "../OutC" (both "AllFieldsFilled" "NotAllFieldsFilled" s!"{cells}/Data")]

/-- The capture's slot `i`: `Qty` `i`, a note, the date `2026-01-0i` and one cell; the extents
documents also fill `Info/Tag` and the cell's `Data/Q2`. -/
private def routeSlot (extents : Bool) (i : Nat) : Json :=
  let cell := [("Q", Json.str (toString (10 + i)))] ++
    if extents then [("Data", Json.mkObj [("Q2", Json.str (toString (20 + i)))])] else []
  Json.mkObj ([("Qty", Json.str (toString i)), ("Cells", Json.arr #[Json.mkObj cell]),
    ("Note", Json.str s!"n{i}"), ("When", Json.str s!"2026-01-0{i}")] ++
    if extents then [("Info", Json.mkObj [("Tag", Json.str s!"t{i}")])] else [])

/-- `p3-short`: bin `a` holds three noted slots and the selected bin `b` only the first. -/
private def shortDocument (extents := false) : Json :=
  Json.mkObj [("Depot", Json.mkObj [("Bins", Json.arr #[
    Json.mkObj [("BinCode", "a"), ("BinNote", "x"), ("Slots", Json.arr ((List.range 3).map (routeSlot extents ·.succ)).toArray)],
    Json.mkObj [("BinCode", "b"), ("Slots", Json.arr #[routeSlot extents 1])]])])]

private def routeRelevant : List RelevantEntityPattern :=
  [["Depot", "Bins", "BinCode"], ["Depot", "Bins", "Slots", "Note"], ["Depot", "Bins", "Slots", "Qty"],
    ["Depot", "Bins", "Slots", "When"], ["Depot", "Bins", "Slots"]].map RelevantEntityPattern.allInstances

/-- Every rule's firings as `code@pointer:type`, sorted: full validation without `relevant`,
otherwise one partial call over it. -/
private def routeFirings (relevant : Option (List RelevantEntityPattern) := none)
    (dm? := routesDm?) (document := shortDocument) : Option (List String) := do
  let dm ← dm?
  let input ← (readDocument dm document).toOption
  if !input.refusals.isEmpty then none
  let prepared ← (prepareFlatStringContext zonedWorld builtinStringPatternCompiler dm.flat).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  let validated ← checked.fullValidationDocument.toOption
  let fired ← (validationRules dm .english).mapM fun dmRule => do
    let checkedRule ← (checkValidationRule dm .english dmRule zonedWorld).toOption
    let messages ← (match relevant with
      | none => runValidationRule zonedWorld validated checkedRule
      | some relevant => runRulePartial zonedWorld checked relevant checkedRule).toOption
    pure (messages.map fun message => let observed := observe dm.flat message
      s!"{observed.code}@{observed.pointer}:{observed.messageType}")
  pure (fired.flatten.mergeSort (· ≤ ·))

private def routeOutcomes (dm? := routesDm?) (document := shortDocument) : Option (List String) := do
  let dm ← dm?
  let input ← (readDocument dm document).toOption
  let prepared ← (prepareFlatStringContext zonedWorld builtinStringPatternCompiler dm.flat).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  let lowered ← dm.computations.mapM fun definition => (lowerComputation dm.flat .english definition).toOption
  let reported ← (runComputations zonedWorld prepared checked (lowered.map (·.2))).toOption
  pure ((reported.map toString).mergeSort (· ≤ ·))

/- Slots 2 and 3 of bin `a` meet a selected bin without them: `DayFromDate` reads its empty
date, `FirstFilledValue` falls through to the slot's own `Qty`, and the keyed group is not filled,
each as an omission, alike in full and partial validation. -/
example : routeFirings = some ["D4@Depot/Bins/Slots[2]/Note:OMISSION_ERROR", "D4@Depot/Bins/Slots[3]/Note:OMISSION_ERROR",
    "F1@Depot/Bins/Slots/Note:VALUE_ERROR", "F1@Depot/Bins/Slots[2]/Note:OMISSION_ERROR",
    "F1@Depot/Bins/Slots[3]/Note:OMISSION_ERROR", "F1@Depot/Bins[2]/Slots/Note:VALUE_ERROR",
    "G1@Depot/Bins/Slots/Note:VALUE_ERROR", "G1@Depot/Bins[2]/Slots/Note:VALUE_ERROR",
    "G2@Depot/Bins/Slots[2]/Note:OMISSION_ERROR", "G2@Depot/Bins/Slots[3]/Note:OMISSION_ERROR"] ∧
    routeFirings (some routeRelevant) = routeFirings := by native_decide

/- The computation reads the same missing row as `0`, not as a poisoned operand. -/
example : routeOutcomes = some ["Depot/Bins/Slots/OutD=value 1", "Depot/Bins/Slots[2]/OutD=value 0",
    "Depot/Bins/Slots[3]/OutD=value 0", "Depot/Bins[2]/Slots/OutD=value 1"] := by native_decide

/- Below the key, a keyed group the selected bin lacks is not filled, its fields are not all
filled, and a Date `FirstFilledValue` falls through to the slot's own date: `2` and the own date
at slots 2 and 3 of bin `a`, as the Kernel computes them. -/
example : (routeOutcomes extentsDm? (shortDocument true)).map (·.filter fun outcome =>
      ["OutC=", "OutG2=", "OutW2="].any fun field => (outcome.splitOn field).length > 1) = some [
    "Depot/Bins/Slots/Cells/OutC=value 1", "Depot/Bins/Slots/OutG2=value 1", "Depot/Bins/Slots/OutW2=value 2026-01-01",
    "Depot/Bins/Slots[2]/Cells/OutC=value 2", "Depot/Bins/Slots[2]/OutG2=value 2", "Depot/Bins/Slots[2]/OutW2=value 2026-01-02",
    "Depot/Bins/Slots[3]/Cells/OutC=value 2", "Depot/Bins/Slots[3]/OutG2=value 2", "Depot/Bins/Slots[3]/OutW2=value 2026-01-03",
    "Depot/Bins[2]/Slots/Cells/OutC=value 1", "Depot/Bins[2]/Slots/OutG2=value 1", "Depot/Bins[2]/Slots/OutW2=value 2026-01-01"] := by
  native_decide

/- The fill count below the key counts nothing at the slots the selected bin lacks, so `N1`
fires only at the two present first slots, alike in full and partial validation. -/
example : (routeFirings none extentsDm? (shortDocument true)).map (·.filter (·.startsWith "N1@")) =
      some ["N1@Depot/Bins/Slots/Note:VALUE_ERROR", "N1@Depot/Bins[2]/Slots/Note:VALUE_ERROR"] ∧
    (routeFirings (some routeRelevant) extentsDm? (shortDocument true)).map (·.filter (·.startsWith "N1@")) =
      some ["N1@Depot/Bins/Slots/Note:VALUE_ERROR", "N1@Depot/Bins[2]/Slots/Note:VALUE_ERROR"] := by native_decide

/-! ## A level the key fixes is not iterated

A rule that reads the error field only through the key iterates inside the selected bin: `N2` and
`N2T` fire at `Bins[2]` alone, at each of its slots, and `E2` and `E2T` at each of its slot and cell
rows, each reading its own row. A plain read of the field beside the key, as in `E5` and `E5T`,
iterates every bin again. A key no bin carries, or two bins carry, fires none of them. The documents,
rules and relevant set are those of the retained capture
`evidence/kernel-30.8.1/captures/below-key-error-scope-2026-10-28/`, rows `bk-other`, `bk-missing`
and `bk-duplicate`, and each expectation is the Kernel's firings of these six rules there, alike in
full and partial validation. -/

private def scopeDm? : Option DmModel :=
  let slots := "/Depot/Bins/Slots"
  let cells := s!"{slots}/Cells"
  dmWith? [rule slots "N2" "../Qty" "[Qty For \"b\"] > 0", rule slots "N2T" "../Qty" "[Qty For \"b\"] > 3",
      rule slots "E5" "../Qty" "[Qty For \"b\"] > 0 And [Qty] > 0",
      rule slots "E5T" "../Qty" "[Qty For \"b\"] > 3 And [Qty] > 0"]
    [rule cells "E2" "../Q" "[Q For \"b\"] > 0", rule cells "E2T" "../Q" "[Q For \"b\"] > 6"]

private def scopeRelevant : List RelevantEntityPattern :=
  [["Depot", "Bins", "BinCode"], ["Depot", "Bins", "BinNote"], ["Depot", "Bins", "Slots", "Qty"],
    ["Depot", "Bins", "Slots", "Cells", "Q"], ["Depot", "Bins", "Slots"]].map RelevantEntityPattern.allInstances

/-- Full and partial firings of the six rules, which must agree. -/
private def scopeFirings (document : Json) : Option (List String) := do
  let full ← routeFirings none scopeDm? document
  let partialFired ← routeFirings (some scopeRelevant) scopeDm? document
  if full == partialFired then some full else none

example : scopeFirings (depot [bin "a" (notedSlots 2) true, bin "b" (plainSlots 3)]) = some [
    "E2@Depot/Bins[2]/Slots/Cells/Q:VALUE_ERROR", "E2@Depot/Bins[2]/Slots/Cells[2]/Q:VALUE_ERROR",
    "E2@Depot/Bins[2]/Slots/Cells[3]/Q:VALUE_ERROR", "E2@Depot/Bins[2]/Slots[2]/Cells/Q:VALUE_ERROR",
    "E2@Depot/Bins[2]/Slots[2]/Cells[2]/Q:VALUE_ERROR", "E2@Depot/Bins[2]/Slots[2]/Cells[3]/Q:VALUE_ERROR",
    "E2@Depot/Bins[2]/Slots[3]/Cells/Q:VALUE_ERROR", "E2@Depot/Bins[2]/Slots[3]/Cells[2]/Q:VALUE_ERROR",
    "E2@Depot/Bins[2]/Slots[3]/Cells[3]/Q:VALUE_ERROR", "E2T@Depot/Bins[2]/Slots/Cells[3]/Q:VALUE_ERROR",
    "E2T@Depot/Bins[2]/Slots[2]/Cells[2]/Q:VALUE_ERROR", "E2T@Depot/Bins[2]/Slots[2]/Cells[3]/Q:VALUE_ERROR",
    "E2T@Depot/Bins[2]/Slots[3]/Cells/Q:VALUE_ERROR", "E2T@Depot/Bins[2]/Slots[3]/Cells[2]/Q:VALUE_ERROR",
    "E2T@Depot/Bins[2]/Slots[3]/Cells[3]/Q:VALUE_ERROR", "E5@Depot/Bins/Slots/Qty:VALUE_ERROR",
    "E5@Depot/Bins/Slots[2]/Qty:VALUE_ERROR", "E5@Depot/Bins[2]/Slots/Qty:VALUE_ERROR",
    "E5@Depot/Bins[2]/Slots[2]/Qty:VALUE_ERROR", "E5@Depot/Bins[2]/Slots[3]/Qty:VALUE_ERROR",
    "E5T@Depot/Bins/Slots[2]/Qty:VALUE_ERROR", "E5T@Depot/Bins[2]/Slots[2]/Qty:VALUE_ERROR",
    "E5T@Depot/Bins[2]/Slots[3]/Qty:VALUE_ERROR", "N2@Depot/Bins[2]/Slots/Qty:VALUE_ERROR",
    "N2@Depot/Bins[2]/Slots[2]/Qty:VALUE_ERROR", "N2@Depot/Bins[2]/Slots[3]/Qty:VALUE_ERROR",
    "N2T@Depot/Bins[2]/Slots[2]/Qty:VALUE_ERROR", "N2T@Depot/Bins[2]/Slots[3]/Qty:VALUE_ERROR"] := by
  native_decide

/-- Whether the rule reporting on `Qty` from `Slots` with this condition is admitted. -/
private def qtyRuleAdmitted (condition : String) : Option Bool := do
  let dm ← dmWith? (some []) (some [])
  pure (checkValidationRule dm .english
    { group := ["Depot", "Bins", "Slots"], name := "P", severity := "ERROR", errorCode := "P",
      errorEntityRelPath := "../Qty", condition }).isOk

/- A leaf without a selection that iterates `Bins`, here a current-repetition coordinate that reads
no field, keeps `Bins` iterated, so the keyed read leaves the error field unbound there. This is
Lean's conservative account; the Kernel's answer is unmeasured
([below-key error scope](../../../docs/sources/model-structure-and-declaration-probes.md#src-below-key-error-scope) `limit`). -/
example : qtyRuleAdmitted "[Qty For \"b\"] > 0 And CurrentRepetition(/Depot/Bins) > 1" = some false ∧
    qtyRuleAdmitted "[Qty For \"b\"] > 0" = some true := by native_decide

example : scopeFirings (depot [bin "a" (notedSlots 2) true, bin "c" (plainSlots 2)]) = some [] ∧
    scopeFirings (depot [bin "a" (notedSlots 1) true, bin "b" (plainSlots 1), bin "b" (plainSlots 1)]) = some [] := by
  native_decide

end A12Kernel.Dm.BelowKeySelectionLocks
