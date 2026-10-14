import Lean.Data.Json
import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Document
import A12Kernel.Reference.Dm.ParallelValidation

/-! # Partner-row keys, unmatched sides and pair counts beside a key join

Reader-to-evaluator locks for the leaves a key join binds to one side's row: a key read off the
partner row, in a joined computation guard and in a parallel rule; a key read off an error side
that has no row for the joined key, whose non-key fields read empty; and a distinct count
or a uniqueness test over one field of each side. The model and documents are reductions of the
retained Kernel 30.8.1 capture `evidence/kernel-30.8.1/captures/joined-carrier-limits-2026-10-14/`;
every expectation is the capture's own change or message.

The documents separate a partner key that names a ledger row from one that names none, a partner
that is missing for the target, a Demand row with no Supply row, equal and different pair values,
and a document without any ledger row.
-/

namespace A12Kernel.Dm.ParallelJoinedLimitsLocks

open Lean A12Kernel

private def element (kind id name : String) (body : List (String × Json)) : Json :=
  Json.mkObj [("type", .str kind), ("id", .str id), ("name", .str name), (kind, Json.mkObj body)]

private def field (group name : String) (fieldType : Json) : Json :=
  element "Field" s!"/Staffing/{group}/{name}" name [("fieldType", fieldType)]

private def text : Json := Json.mkObj [("type", "StringType")]
private def number : Json :=
  Json.mkObj [("type", "NumberType"), ("NumberType", Json.mkObj [("maxFractionalDigits", toJson 0)])]

private def keyed (capacity : Nat) (name key : String) (fields : List Json) : Json :=
  element "Group" s!"/Staffing/{name}" name [("repeatability", toJson capacity),
    ("elements", Json.arr (field name key text :: fields).toArray), ("indexFieldName", .str key)]

private def message : Json := Json.arr #[Json.mkObj [("locale", "en_US"), ("text", "m")]]

private def computation (target guard : String) : Json :=
  element "Computation" s!"/Staffing/Supply/C{target}" s!"C{target}" [("computedFieldRelPath", .str s!"../{target}"),
    ("computationAlternatives", Json.arr #[Json.mkObj [("precondition", .str guard),
      ("operation", "[/Staffing/Demand/Base] + [Headcount]")]]), ("errorMessage", message)]

private def rule (name errorField condition : String) : Json :=
  element "Rule" s!"/Staffing/{name}" name [("errorEntityRelPath", .str s!"../Supply/{errorField}"),
    ("errorCode", .str name), ("errorCondition", .str condition), ("severity", "ERROR"),
    ("errorMessage", message)]

private def rules : List Json := [
  rule "p01" "Headcount"
    "FieldFilled(Supply/Headcount) And FieldFilled(Demand/Base) And GroupFilled(/Staffing/Ledger For Demand/Label)",
  rule "d03" "Headcount" "FieldFilled(Supply/Headcount) And NumberOfDifferentValues(Supply/Note, Demand/Label) < 2",
  rule "d04" "Headcount"
    "FieldFilled(Supply/Headcount) And FieldFilled(Demand/Base) And FieldValuesNotUnique(Supply/Note, Demand/Label)",
  rule "u01b" "Note" "FieldFilled(Demand/Base) And GroupNotFilled(/Staffing/Ledger For Supply/Note)",
  rule "u03b" "Note"
    "FieldFilled(Demand/Base) And FieldNotFilled(Supply/Note) And FieldNotFilled(/Staffing/Ledger/Amount For Supply/Note)",
  rule "d01b" "Note" "NumberOfDifferentValues(Supply/Note, Demand/Label) > 1"]

private def dmWith (capacity : Nat) : Option DmModel :=
  (readModel (Json.mkObj [("content", Json.mkObj [("modelRoot", Json.mkObj [("rootGroups", Json.arr #[
    element "Group" "/Staffing" "Staffing" [("repeatability", toJson 1), ("elements", Json.arr (#[
      keyed capacity "Demand" "Department" [field "Demand" "Base" number, field "Demand" "Label" text],
      keyed capacity "Supply" "Department" [field "Supply" "Headcount" number, field "Supply" "Note" text,
        field "Supply" "Out12" number, field "Supply" "Out13" number,
        computation "Out12" "GroupFilled(/Staffing/Ledger For /Staffing/Demand/Label)",
        computation "Out13" "GroupFilled(/Staffing/Ledger For Note)"],
      keyed capacity "Ledger" "Code" [field "Ledger" "Amount" number]] ++ rules.toArray))]])])])])).toOption

private def world : World := { now := { epochMillis := 1791972000000 }, modelZoneRules := ModelZone.concreteRules }

private def row (entries : List (String × String)) : Json :=
  Json.mkObj (entries.map fun (key, value) => (key, Json.str value))

private def staffing (groups : List (String × List (List (String × String)))) : Json :=
  Json.mkObj [("Staffing", Json.mkObj (groups.map fun (name, rows) => (name, Json.arr (rows.map row).toArray)))]

/-- Every reported target change, as `pointer outcome`. -/
private def computed (document : Json) (capacity : Nat := 50) : Option (List String) := do
  let dm ← dmWith capacity
  let input ← (readDocument dm document).toOption
  if !input.refusals.isEmpty then none
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler dm.flat).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  let lowered ← dm.computations.mapM fun source => (lowerComputation dm.flat .english source).toOption
  let outcomes ← (runComputations world prepared checked (lowered.map (·.2))).toOption
  pure (outcomes.map fun outcome => s!"{outcome.pointer} {outcome.outcome}")

/-- Each rule's firings with their sorted references, as `code pointer type referenced`. -/
private def fired (document : Json) (capacity : Nat := 50) : Option (List String) := do
  let dm ← dmWith capacity
  let input ← (readDocument dm document).toOption
  if !input.refusals.isEmpty then none
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler dm.flat).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  let messages ← dm.rules.mapM fun source => do
    let .parallel plan ← (checkValidationRule dm .english source world).toOption | none
    let fired ← (runParallelRuleReferences checked plan (some world)).toOption
    fired.mapM fun (message, references) => do
      let references ← references.toOption
      let sorted := (references.referenced.map (renderPointer dm.flat)).eraseDups.mergeSort (compare · · != .gt)
      pure s!"{source.errorCode} {renderPointer dm.flat message.errorAddress} {reprStr message.messageType} {sorted}"
  pure messages.flatten

private def staff : Json := staffing [
  ("Ledger", [[("Code", "k1"), ("Amount", "4")], [("Code", "x"), ("Amount", "9")], [("Code", "LA"), ("Amount", "5")]]),
  ("Demand", [[("Department", "A"), ("Base", "10"), ("Label", "LA")], [("Department", "B"), ("Base", "20"), ("Label", "zz")],
    [("Department", "C"), ("Base", "5"), ("Label", "k1")], [("Department", "D"), ("Base", "7"), ("Label", "x")]]),
  ("Supply", [[("Department", "A"), ("Out12", "999"), ("Out13", "999"), ("Headcount", "1"), ("Note", "x")],
    [("Department", "B"), ("Out12", "999"), ("Out13", "999"), ("Headcount", "7")],
    [("Department", "C"), ("Out12", "999"), ("Out13", "999"), ("Headcount", "3"), ("Note", "k1")],
    [("Department", "E"), ("Out12", "999"), ("Out13", "999"), ("Headcount", "2"), ("Note", "q")]])]

private def noledger : Json := staffing [
  ("Demand", [[("Department", "A"), ("Base", "1"), ("Label", "LA")], [("Department", "D"), ("Base", "2")]]),
  ("Supply", [[("Department", "A"), ("Out12", "999"), ("Out13", "999"), ("Headcount", "1"), ("Note", "x")]])]

-- The partner row's label keys the ledger: `LA` and `k1` name a row, `zz` none, and row E has no
-- partner, whose empty label names none. The target row's own key agrees on this document.
example : computed staff = some [
    "Staffing/Supply/Out12 value 11", "Staffing/Supply[2]/Out12 cleared", "Staffing/Supply[3]/Out12 value 8",
    "Staffing/Supply[4]/Out12 cleared", "Staffing/Supply/Out13 value 11", "Staffing/Supply[2]/Out13 cleared",
    "Staffing/Supply[3]/Out13 value 8", "Staffing/Supply[4]/Out13 cleared"] := by native_decide

example : computed noledger = some ["Staffing/Supply/Out12 cleared", "Staffing/Supply/Out13 cleared"] := by
  native_decide

-- Demand row D has no Supply row: the error side's non-key fields read empty, so its note is
-- empty, names no ledger row and is reported at the Kernel's key-only address. A distinct count and a
-- uniqueness test take one value from each side; an empty one makes `< 2` an omission and leaves `> 1`
-- unreported, on row B and on row E, which has no partner.
example : fired staff = some [
    "p01 Staffing/Supply/Headcount A12Kernel.Polarity.value [Staffing/Demand/Base, Staffing/Demand/Department, Staffing/Demand/Label, Staffing/Ledger[3]/Amount, Staffing/Ledger[3]/Code, Staffing/Supply/Department, Staffing/Supply/Headcount]",
    "p01 Staffing/Supply[3]/Headcount A12Kernel.Polarity.value [Staffing/Demand[3]/Base, Staffing/Demand[3]/Department, Staffing/Demand[3]/Label, Staffing/Ledger/Amount, Staffing/Ledger/Code, Staffing/Supply[3]/Department, Staffing/Supply[3]/Headcount]",
    "d03 Staffing/Supply[2]/Headcount A12Kernel.Polarity.omission [Staffing/Demand[2]/Department, Staffing/Demand[2]/Label, Staffing/Supply[2]/Department, Staffing/Supply[2]/Headcount, Staffing/Supply[2]/Note]",
    "d03 Staffing/Supply[3]/Headcount A12Kernel.Polarity.value [Staffing/Demand[3]/Department, Staffing/Demand[3]/Label, Staffing/Supply[3]/Department, Staffing/Supply[3]/Headcount, Staffing/Supply[3]/Note]",
    "d03 Staffing/Supply[4]/Headcount A12Kernel.Polarity.omission [/Staffing[1]/Demand[-5]/Department, /Staffing[1]/Demand[-5]/Label, Staffing/Supply[4]/Department, Staffing/Supply[4]/Headcount, Staffing/Supply[4]/Note]",
    "d04 Staffing/Supply[3]/Headcount A12Kernel.Polarity.value [Staffing/Demand[3]/Base, Staffing/Demand[3]/Department, Staffing/Demand[3]/Label, Staffing/Supply[3]/Department, Staffing/Supply[3]/Headcount, Staffing/Supply[3]/Note]",
    "u01b Staffing/Supply[2]/Note A12Kernel.Polarity.omission [/Staffing[1]/Ledger[-5]/Amount, /Staffing[1]/Ledger[-5]/Code, Staffing/Demand[2]/Base, Staffing/Demand[2]/Department, Staffing/Supply[2]/Department, Staffing/Supply[2]/Note]",
    "u01b /Staffing[1]/Supply[-5]/Note A12Kernel.Polarity.omission [/Staffing[1]/Ledger[-5]/Amount, /Staffing[1]/Ledger[-5]/Code, /Staffing[1]/Supply[-5]/Department, /Staffing[1]/Supply[-5]/Note, Staffing/Demand[4]/Base, Staffing/Demand[4]/Department]",
    "u03b Staffing/Supply[2]/Note A12Kernel.Polarity.omission [/Staffing[1]/Ledger[-5]/Amount, /Staffing[1]/Ledger[-5]/Code, Staffing/Demand[2]/Base, Staffing/Demand[2]/Department, Staffing/Supply[2]/Department, Staffing/Supply[2]/Note]",
    "u03b /Staffing[1]/Supply[-5]/Note A12Kernel.Polarity.omission [/Staffing[1]/Ledger[-5]/Amount, /Staffing[1]/Ledger[-5]/Code, /Staffing[1]/Supply[-5]/Department, /Staffing[1]/Supply[-5]/Note, Staffing/Demand[4]/Base, Staffing/Demand[4]/Department]",
    "d01b Staffing/Supply/Note A12Kernel.Polarity.value [Staffing/Demand/Department, Staffing/Demand/Label, Staffing/Supply/Department, Staffing/Supply/Note]"] := by
  native_decide

example : fired noledger = some [
    "u01b Staffing/Supply/Note A12Kernel.Polarity.omission [/Staffing[1]/Ledger[-5]/Amount, /Staffing[1]/Ledger[-5]/Code, Staffing/Demand/Base, Staffing/Demand/Department, Staffing/Supply/Department, Staffing/Supply/Note]",
    "u01b /Staffing[1]/Supply[-5]/Note A12Kernel.Polarity.omission [/Staffing[1]/Ledger[-5]/Amount, /Staffing[1]/Ledger[-5]/Code, /Staffing[1]/Supply[-5]/Department, /Staffing[1]/Supply[-5]/Note, Staffing/Demand[2]/Base, Staffing/Demand[2]/Department]",
    "u03b /Staffing[1]/Supply[-5]/Note A12Kernel.Polarity.omission [/Staffing[1]/Ledger[-5]/Amount, /Staffing[1]/Ledger[-5]/Code, /Staffing[1]/Supply[-5]/Department, /Staffing[1]/Supply[-5]/Note, Staffing/Demand[2]/Base, Staffing/Demand[2]/Department]",
    "d01b Staffing/Supply/Note A12Kernel.Polarity.value [Staffing/Demand/Department, Staffing/Demand/Label, Staffing/Supply/Department, Staffing/Supply/Note]"] := by
  native_decide

-- With every group full, an unmatched side has no free row of its group left; its fields still read
-- empty, so neither the computations nor the rules change. The capture has free
-- rows on every document, so this invariance is the chosen account, not a measurement.
example : computed staff 4 = computed staff ∧ fired staff 4 = fired staff := by native_decide

end A12Kernel.Dm.ParallelJoinedLimitsLocks
