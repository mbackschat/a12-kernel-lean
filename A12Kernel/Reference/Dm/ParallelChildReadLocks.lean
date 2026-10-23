import Lean.Data.Json
import A12Kernel.Reference.Dm.Document
import A12Kernel.Reference.Dm.ParallelValidation

/-! # Reads below a joined group in a parallel rule

Reader-to-evaluator locks for an ordinary leaf of a key-joined parallel rule that reads below one
side's joined group: through starred children, as a count, a sum, a first filled value or a fill
test, and through a fixed subgroup, on the error side and on the partner. Such a read binds the
side's joined row and anchors the join through its unstarred prefix. An unmatched side's key-only
row has no children, so they read empty, even when the side's group is full. A filtered star below
either joined group draws the filtered-entity class, after `RepetitionNotUnique` beside the join; one
in an unjoined group is admitted, and an unstarred child read draws the missing-wildcard class.

The expectations are the Kernel 30.8.1 capture
`evidence/kernel-30.8.1/captures/parallel-child-reads-2026-10-14/`: its diagnostics, and every
message with its references. The fixture merges the capture's models into one, adding `Ledger`,
`Items/Deep` and the rules of each to the others; every rule is checked and run on its own, and
`Deep` is filled only where the second runtime model declared it.
-/

namespace A12Kernel.Dm.ParallelChildReadLocks

open Lean A12Kernel

private def element (kind id name : String) (body : List (String × Json)) : Json :=
  Json.mkObj [("type", .str kind), ("id", .str id), ("name", .str name), (kind, Json.mkObj body)]

private def number : Json :=
  Json.mkObj [("type", "NumberType"), ("NumberType", Json.mkObj [("maxFractionalDigits", toJson 0)])]

private def field (group name : String) (fieldType : Json := number) : Json :=
  element "Field" s!"{group}/{name}" name [("fieldType", fieldType)]

private def group (parent name : String) (elements : List Json) (capacity : Option Nat := none) : Json :=
  element "Group" s!"{parent}/{name}" name ((capacity.map fun capacity => ("repeatability", toJson capacity)).toList ++
    [("elements", Json.arr elements.toArray)])

private def keyed (name : String) (elements : List Json) : Json :=
  element "Group" s!"/Staffing/{name}" name [("repeatability", toJson 4), ("elements",
    Json.arr (field s!"/Staffing/{name}" "Department" (Json.mkObj [("type", "StringType")]) :: elements).toArray),
    ("indexFieldName", "Department")]

private def message : Json := Json.arr #[Json.mkObj [("locale", "en_US"), ("text", "m")]]

private def ruleIn (groupId name errorField condition : String) : Json :=
  element "Rule" s!"{groupId}/{name}" name [("errorEntityRelPath", .str errorField), ("errorCode", .str name),
    ("errorCondition", .str condition), ("severity", "ERROR"), ("errorMessage", message)]

/-- A rule in `Staffing` reporting at `Supply/Note`, behind the capture's prefix: a Demand row with a
base whose Supply note is empty, or, with `onSupply`, a Supply row with a headcount. -/
private def rule (name condition : String) (onSupply : Bool := false) : Json :=
  let prefixText := if onSupply then "FieldFilled(Supply/Headcount) And FieldNotFilled(Supply/Note) And "
    else "FieldFilled(Demand/Base) And FieldNotFilled(Supply/Note) And "
  ruleIn "/Staffing" name "../Supply/Note" (prefixText ++ condition)

/-- A rule in `Staffing` reporting at `Supply/Headcount` beside `RepetitionNotUnique(Supply/Note)`. -/
private def uniquenessRule (name condition : String) : Json :=
  ruleIn "/Staffing" name "../Supply/Headcount"
    ("FieldFilled(Supply/Headcount) And FieldFilled(Demand/Base) And RepetitionNotUnique(Supply/Note)" ++ condition)

private def runtimeRules : List Json := [
  rule "q01" "NumberOfFilledFields(Supply/Items*/Q) == 0", rule "q02" "Sum(Supply/Items*/Q) == 0",
  rule "q03" "FirstFilledValue(Supply/Items*/Q) > 0", rule "q04" "AtLeastOneFieldFilled(Supply/Items*/Q)",
  rule "q06" "FieldFilled(Supply/Sub/X)", rule "q08" "NumberOfFilledFields(Demand/DItems*/P) == 0",
  rule "q09" "FieldNotFilled(Demand/DSub/Y)", rule "q00" "FieldFilled(Supply/Headcount)",
  rule "r01" "NoFieldFilled(Supply/Items*/Q)",
  rule "r02" "NumberOfFilledFields(Demand/DItems*/P) == 0" (onSupply := true),
  rule "r03" "FieldNotFilled(Demand/DSub/Y)" (onSupply := true),
  rule "r04" "NumberOfFilledFields(Supply/Items*/Deep*/R) == 0", rule "r05" "FieldNotFilled(Supply/Sub/X)"]

-- Checked statically only: filters below and beside the join, a rule declared inside the error
-- side's group, and `RepetitionNotUnique` beside the join with and without a filter.
private def staticRules : List Json := [
  rule "q05" "NumberOfFilledFields(Supply/Items*/Q Having [Supply/Items/Q] > 1) > 0",
  rule "q07" "[Supply/Items/Q] > 0",
  rule "q10" "NumberOfFilledFields(Demand/DItems*/P Having [Demand/DItems/P] > 1) > 0",
  rule "q11" "NumberOfFilledFields(/Staffing/Ledger*/L Having [/Staffing/Ledger/L] > 1) > 0",
  rule "q12" "NumberOfFilledFields(/Staffing/Ledger*/L) > 0",
  -- The joined-carrier-limits capture's `d06` condition.
  uniquenessRule "x0" "",
  uniquenessRule "x1" " And NumberOfFilledFields(Demand/DItems*/P Having [Demand/DItems/P] > 1) > 0",
  uniquenessRule "x2" " And NumberOfFilledFields(Supply/Items*/Q Having [Supply/Items/Q] > 1) > 0"]

private def supplyRules : List Json := [
  ruleIn "/Staffing/Supply" "y1" "../Note"
    "FieldFilled(/Staffing/Demand/Base) And FieldNotFilled(Note) And NumberOfFilledFields(Items*/Q Having [Items/Q] > 1) > 0",
  ruleIn "/Staffing/Supply" "y2" "../Note"
    "FieldFilled(/Staffing/Demand/Base) And FieldNotFilled(Note) And NumberOfFilledFields(Items*/Q) > 0"]

private def dmWith (rules : List Json) (inSupply : List Json := []) : Option DmModel :=
  (readModel (Json.mkObj [("content", Json.mkObj [("modelRoot", Json.mkObj [("rootGroups", Json.arr #[
    element "Group" "/Staffing" "Staffing" [("repeatability", toJson 1), ("elements", Json.arr (#[
      keyed "Demand" [field "/Staffing/Demand" "Base",
        group "/Staffing/Demand" "DItems" [field "/Staffing/Demand/DItems" "P"] (some 2),
        group "/Staffing/Demand" "DSub" [field "/Staffing/Demand/DSub" "Y"]],
      keyed "Supply" ([field "/Staffing/Supply" "Headcount",
        field "/Staffing/Supply" "Note" (Json.mkObj [("type", "StringType")]),
        group "/Staffing/Supply" "Items" [field "/Staffing/Supply/Items" "Q",
          group "/Staffing/Supply/Items" "Deep" [field "/Staffing/Supply/Items/Deep" "R"] (some 2)] (some 2),
        group "/Staffing/Supply" "Sub" [field "/Staffing/Supply/Sub" "X"]] ++ inSupply),
      group "/Staffing" "Ledger" [field "/Staffing/Ledger" "L"] (some 3)] ++ rules.toArray))]])])])])).toOption

/-- Each rule's admission, as `code admitted` or `code construct detail`. -/
private def admission : Option (List String) := do
  let dm ← dmWith (runtimeRules ++ staticRules) supplyRules
  pure (dm.rules.map fun source => match checkValidationRule dm .english source with
    | .ok _ => s!"{source.errorCode} admitted"
    | .error refusal => s!"{source.errorCode} {refusal.construct} {refusal.detail}")

private def world : World := { now := { epochMillis := 1791972000000 }, modelZoneRules := ModelZone.concreteRules }

private def sorted (dm : DmModel) (pointers : List MessagePointer) : List String :=
  (pointers.map (renderFieldPointer dm.flat)).eraseDups.mergeSort (compare · · != .gt)

/-- Each rule's firings, as `code pointer type referenced fillToFix`. -/
private def fired (document : Json) : Option (List String) := do
  let dm ← dmWith runtimeRules
  let input ← (readDocument dm document).toOption
  if !input.refusals.isEmpty then none
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler dm.flat).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  let messages ← dm.rules.mapM fun source => do
    let .parallel plan ← (checkValidationRule dm .english source world).toOption | none
    let fired ← (runParallelRuleReferences checked plan (some world)).toOption
    fired.mapM fun (message, references) => do
      let references ← references.toOption
      pure s!"{source.errorCode} {renderPointer dm.flat message.errorAddress} {reprStr message.messageType} {sorted dm references.referenced} {sorted dm references.fillToFix}"
  pure messages.flatten

/-- A starred child group's rows, an empty value standing for a row with its field unfilled. -/
private def items (group field : String) (values : List String) (deep : List (Nat × Json) := []) : String × Json :=
  (group, Json.arr ((values.zipIdx.map fun (value, index) =>
    let fields := (if value.isEmpty then [] else [(field, Json.str value)]) ++
      ((deep.lookup index).map fun rows => ("Deep", rows)).toList
    Json.mkObj fields)).toArray)

/-- A Demand row: key, base, `DItems` values (empty for an unfilled row) and the `DSub` value. -/
private def demand (key : String) (ditems : List String) (y : Option String) : Json :=
  Json.mkObj ([("Department", Json.str key), ("Base", Json.str "1"), items "DItems" "P" ditems] ++
    (y.map fun y => ("DSub", Json.mkObj [("Y", .str y)])).toList)

/-- A Supply row: key, headcount, `Items` values, the `Sub` value, and for row `A` one `Deep` row. -/
private def supply (key : String) (values : List String) (x : Option String) : Json :=
  let deep := if key == "A" then [(1, Json.arr #[Json.mkObj [("R", "7")]])] else []
  Json.mkObj ([("Department", Json.str key), ("Headcount", Json.str "1"), items "Items" "Q" values deep] ++
    (x.map fun x => ("Sub", Json.mkObj [("X", .str x)])).toList)

private def staffing (demands supplies : List Json) : Json :=
  Json.mkObj [("Staffing", Json.mkObj [("Demand", Json.arr demands.toArray), ("Supply", Json.arr supplies.toArray)])]

-- Demand C has no Supply row; Supply E has no Demand row; Supply B has no item.
private def free : Json := staffing
  [demand "A" ["", "3"] (some "1"), demand "B" [] none, demand "C" ["2"] (some "5")]
  [supply "A" ["", "2"] (some "4"), supply "B" [] none, supply "E" ["5"] (some "6")]

-- Supply has all four rows, so Demand C's key-only Supply row lies beyond capacity.
private def full : Json := staffing
  [demand "A" ["", "3"] none, demand "C" ["2"] (some "5")]
  [supply "A" ["", "2"] (some "4"), supply "B" ["1"] (some "1"), supply "D" [] none, supply "E" ["5"] (some "6")]

-- Every verdict is the capture's: the filtered-entity class below either joined group, also for a
-- rule declared inside the error side's group (`y1`), after `RepetitionNotUnique` beside the join
-- (`x1`, `x2`, and `x0`, the joined-carrier-limits capture's `d06`).
example : admission = some [
    "y1 ParallelAdmission MVK_PARALLEL_ITERATION_FOR_FILTERED_ENTITY_NOT_ALLOWED",
    "y2 admitted",
    "q01 admitted",
    "q02 admitted",
    "q03 admitted",
    "q04 admitted",
    "q06 admitted",
    "q08 admitted",
    "q09 admitted",
    "q00 admitted",
    "r01 admitted",
    "r02 admitted",
    "r03 admitted",
    "r04 admitted",
    "r05 admitted",
    "q05 ParallelAdmission MVK_PARALLEL_ITERATION_FOR_FILTERED_ENTITY_NOT_ALLOWED",
    "q07 ParallelAdmission MVK_NO_WILDCARD",
    "q10 ParallelAdmission MVK_PARALLEL_ITERATION_FOR_FILTERED_ENTITY_NOT_ALLOWED",
    "q11 admitted",
    "q12 admitted",
    "x0 ParallelAdmission MVK_PARALLEL_ITERATION_NOT_ALLOWED",
    "x1 ParallelAdmission MVK_PARALLEL_ITERATION_NOT_ALLOWED",
    "x2 ParallelAdmission MVK_PARALLEL_ITERATION_NOT_ALLOWED"] := by
  native_decide

-- Demand C's key-only Supply row reads its children empty, so the count and the sum are zero and
-- `NoFieldFilled` holds, and names them at `-5`, a fixed subgroup at `Sub[1]`; Supply B has no item
-- and reads the same at its own row. Supply E's key-only Demand row does the same on the partner
-- side (`r02`, `r03`), and a read below a side's row brings that side's index field into the
-- fill-to-fix set (`q08`).
example : fired free = some [
    "q01 Staffing/Supply[2]/Note A12Kernel.Polarity.omission [/Staffing[1]/Supply[2]/Items[0]/Q, Staffing/Demand[2]/Base, Staffing/Demand[2]/Department, Staffing/Supply[2]/Department, Staffing/Supply[2]/Note] [/Staffing[1]/Supply[2]/Items[0]/Q, Staffing/Supply[2]/Department, Staffing/Supply[2]/Note]",
    "q01 /Staffing[1]/Supply[-5]/Note A12Kernel.Polarity.omission [/Staffing[1]/Supply[-5]/Department, /Staffing[1]/Supply[-5]/Items[0]/Q, /Staffing[1]/Supply[-5]/Note, Staffing/Demand[3]/Base, Staffing/Demand[3]/Department] [/Staffing[1]/Supply[-5]/Department, /Staffing[1]/Supply[-5]/Items[0]/Q, /Staffing[1]/Supply[-5]/Note]",
    "q02 Staffing/Supply[2]/Note A12Kernel.Polarity.omission [/Staffing[1]/Supply[2]/Items[0]/Q, Staffing/Demand[2]/Base, Staffing/Demand[2]/Department, Staffing/Supply[2]/Department, Staffing/Supply[2]/Note] [/Staffing[1]/Supply[2]/Items[0]/Q, Staffing/Supply[2]/Department, Staffing/Supply[2]/Note]",
    "q02 /Staffing[1]/Supply[-5]/Note A12Kernel.Polarity.omission [/Staffing[1]/Supply[-5]/Department, /Staffing[1]/Supply[-5]/Items[0]/Q, /Staffing[1]/Supply[-5]/Note, Staffing/Demand[3]/Base, Staffing/Demand[3]/Department] [/Staffing[1]/Supply[-5]/Department, /Staffing[1]/Supply[-5]/Items[0]/Q, /Staffing[1]/Supply[-5]/Note]",
    "q03 Staffing/Supply/Note A12Kernel.Polarity.omission [/Staffing[1]/Supply[1]/Items[0]/Q, Staffing/Demand/Base, Staffing/Demand/Department, Staffing/Supply/Department, Staffing/Supply/Note] [/Staffing[1]/Supply[1]/Items[0]/Q, Staffing/Supply/Department, Staffing/Supply/Note]",
    "q04 Staffing/Supply/Note A12Kernel.Polarity.omission [/Staffing[1]/Supply[1]/Items[0]/Q, Staffing/Demand/Base, Staffing/Demand/Department, Staffing/Supply/Department, Staffing/Supply/Note] [Staffing/Supply/Department, Staffing/Supply/Note]",
    "q06 Staffing/Supply/Note A12Kernel.Polarity.omission [Staffing/Demand/Base, Staffing/Demand/Department, Staffing/Supply/Department, Staffing/Supply/Note, Staffing/Supply/Sub/X] [Staffing/Supply/Department, Staffing/Supply/Note]",
    "q08 Staffing/Supply[2]/Note A12Kernel.Polarity.omission [/Staffing[1]/Demand[2]/DItems[0]/P, Staffing/Demand[2]/Base, Staffing/Demand[2]/Department, Staffing/Supply[2]/Department, Staffing/Supply[2]/Note] [/Staffing[1]/Demand[2]/DItems[0]/P, Staffing/Demand[2]/Department, Staffing/Supply[2]/Department, Staffing/Supply[2]/Note]",
    "q09 Staffing/Supply[2]/Note A12Kernel.Polarity.omission [Staffing/Demand[2]/Base, Staffing/Demand[2]/DSub/Y, Staffing/Demand[2]/Department, Staffing/Supply[2]/Department, Staffing/Supply[2]/Note] [Staffing/Demand[2]/DSub/Y, Staffing/Demand[2]/Department, Staffing/Supply[2]/Department, Staffing/Supply[2]/Note]",
    "q00 Staffing/Supply/Note A12Kernel.Polarity.omission [Staffing/Demand/Base, Staffing/Demand/Department, Staffing/Supply/Department, Staffing/Supply/Headcount, Staffing/Supply/Note] [Staffing/Supply/Department, Staffing/Supply/Note]",
    "q00 Staffing/Supply[2]/Note A12Kernel.Polarity.omission [Staffing/Demand[2]/Base, Staffing/Demand[2]/Department, Staffing/Supply[2]/Department, Staffing/Supply[2]/Headcount, Staffing/Supply[2]/Note] [Staffing/Supply[2]/Department, Staffing/Supply[2]/Note]",
    "r01 Staffing/Supply[2]/Note A12Kernel.Polarity.omission [/Staffing[1]/Supply[2]/Items[0]/Q, Staffing/Demand[2]/Base, Staffing/Demand[2]/Department, Staffing/Supply[2]/Department, Staffing/Supply[2]/Note] [/Staffing[1]/Supply[2]/Items[0]/Q, Staffing/Supply[2]/Department, Staffing/Supply[2]/Note]",
    "r01 /Staffing[1]/Supply[-5]/Note A12Kernel.Polarity.omission [/Staffing[1]/Supply[-5]/Department, /Staffing[1]/Supply[-5]/Items[0]/Q, /Staffing[1]/Supply[-5]/Note, Staffing/Demand[3]/Base, Staffing/Demand[3]/Department] [/Staffing[1]/Supply[-5]/Department, /Staffing[1]/Supply[-5]/Items[0]/Q, /Staffing[1]/Supply[-5]/Note]",
    "r02 Staffing/Supply[2]/Note A12Kernel.Polarity.omission [/Staffing[1]/Demand[2]/DItems[0]/P, Staffing/Demand[2]/Department, Staffing/Supply[2]/Department, Staffing/Supply[2]/Headcount, Staffing/Supply[2]/Note] [/Staffing[1]/Demand[2]/DItems[0]/P, Staffing/Demand[2]/Department, Staffing/Supply[2]/Department, Staffing/Supply[2]/Note]",
    "r02 Staffing/Supply[3]/Note A12Kernel.Polarity.omission [/Staffing[1]/Demand[-5]/DItems[0]/P, /Staffing[1]/Demand[-5]/Department, Staffing/Supply[3]/Department, Staffing/Supply[3]/Headcount, Staffing/Supply[3]/Note] [/Staffing[1]/Demand[-5]/DItems[0]/P, /Staffing[1]/Demand[-5]/Department, Staffing/Supply[3]/Department, Staffing/Supply[3]/Note]",
    "r03 Staffing/Supply[2]/Note A12Kernel.Polarity.omission [Staffing/Demand[2]/DSub/Y, Staffing/Demand[2]/Department, Staffing/Supply[2]/Department, Staffing/Supply[2]/Headcount, Staffing/Supply[2]/Note] [Staffing/Demand[2]/DSub/Y, Staffing/Demand[2]/Department, Staffing/Supply[2]/Department, Staffing/Supply[2]/Note]",
    "r03 Staffing/Supply[3]/Note A12Kernel.Polarity.omission [/Staffing[1]/Demand[-5]/DSub[1]/Y, /Staffing[1]/Demand[-5]/Department, Staffing/Supply[3]/Department, Staffing/Supply[3]/Headcount, Staffing/Supply[3]/Note] [/Staffing[1]/Demand[-5]/DSub[1]/Y, /Staffing[1]/Demand[-5]/Department, Staffing/Supply[3]/Department, Staffing/Supply[3]/Note]",
    "r04 Staffing/Supply[2]/Note A12Kernel.Polarity.omission [/Staffing[1]/Supply[2]/Items[0]/Deep[0]/R, Staffing/Demand[2]/Base, Staffing/Demand[2]/Department, Staffing/Supply[2]/Department, Staffing/Supply[2]/Note] [/Staffing[1]/Supply[2]/Items[0]/Deep[0]/R, Staffing/Supply[2]/Department, Staffing/Supply[2]/Note]",
    "r04 /Staffing[1]/Supply[-5]/Note A12Kernel.Polarity.omission [/Staffing[1]/Supply[-5]/Department, /Staffing[1]/Supply[-5]/Items[0]/Deep[0]/R, /Staffing[1]/Supply[-5]/Note, Staffing/Demand[3]/Base, Staffing/Demand[3]/Department] [/Staffing[1]/Supply[-5]/Department, /Staffing[1]/Supply[-5]/Items[0]/Deep[0]/R, /Staffing[1]/Supply[-5]/Note]",
    "r05 Staffing/Supply[2]/Note A12Kernel.Polarity.omission [Staffing/Demand[2]/Base, Staffing/Demand[2]/Department, Staffing/Supply[2]/Department, Staffing/Supply[2]/Note, Staffing/Supply[2]/Sub/X] [Staffing/Supply[2]/Department, Staffing/Supply[2]/Note, Staffing/Supply[2]/Sub/X]",
    "r05 /Staffing[1]/Supply[-5]/Note A12Kernel.Polarity.omission [/Staffing[1]/Supply[-5]/Department, /Staffing[1]/Supply[-5]/Note, /Staffing[1]/Supply[-5]/Sub[1]/X, Staffing/Demand[3]/Base, Staffing/Demand[3]/Department] [/Staffing[1]/Supply[-5]/Department, /Staffing[1]/Supply[-5]/Note, /Staffing[1]/Supply[-5]/Sub[1]/X]"] := by
  native_decide

-- Supply is full, so Demand C's key-only row lies beyond capacity; its child slots still read
-- clean empty and the same leaves fire there.
example : fired full = some [
    "q01 /Staffing[1]/Supply[-5]/Note A12Kernel.Polarity.omission [/Staffing[1]/Supply[-5]/Department, /Staffing[1]/Supply[-5]/Items[0]/Q, /Staffing[1]/Supply[-5]/Note, Staffing/Demand[2]/Base, Staffing/Demand[2]/Department] [/Staffing[1]/Supply[-5]/Department, /Staffing[1]/Supply[-5]/Items[0]/Q, /Staffing[1]/Supply[-5]/Note]",
    "q02 /Staffing[1]/Supply[-5]/Note A12Kernel.Polarity.omission [/Staffing[1]/Supply[-5]/Department, /Staffing[1]/Supply[-5]/Items[0]/Q, /Staffing[1]/Supply[-5]/Note, Staffing/Demand[2]/Base, Staffing/Demand[2]/Department] [/Staffing[1]/Supply[-5]/Department, /Staffing[1]/Supply[-5]/Items[0]/Q, /Staffing[1]/Supply[-5]/Note]",
    "q03 Staffing/Supply/Note A12Kernel.Polarity.omission [/Staffing[1]/Supply[1]/Items[0]/Q, Staffing/Demand/Base, Staffing/Demand/Department, Staffing/Supply/Department, Staffing/Supply/Note] [/Staffing[1]/Supply[1]/Items[0]/Q, Staffing/Supply/Department, Staffing/Supply/Note]",
    "q04 Staffing/Supply/Note A12Kernel.Polarity.omission [/Staffing[1]/Supply[1]/Items[0]/Q, Staffing/Demand/Base, Staffing/Demand/Department, Staffing/Supply/Department, Staffing/Supply/Note] [Staffing/Supply/Department, Staffing/Supply/Note]",
    "q06 Staffing/Supply/Note A12Kernel.Polarity.omission [Staffing/Demand/Base, Staffing/Demand/Department, Staffing/Supply/Department, Staffing/Supply/Note, Staffing/Supply/Sub/X] [Staffing/Supply/Department, Staffing/Supply/Note]",
    "q09 Staffing/Supply/Note A12Kernel.Polarity.omission [Staffing/Demand/Base, Staffing/Demand/DSub/Y, Staffing/Demand/Department, Staffing/Supply/Department, Staffing/Supply/Note] [Staffing/Demand/DSub/Y, Staffing/Demand/Department, Staffing/Supply/Department, Staffing/Supply/Note]",
    "q00 Staffing/Supply/Note A12Kernel.Polarity.omission [Staffing/Demand/Base, Staffing/Demand/Department, Staffing/Supply/Department, Staffing/Supply/Headcount, Staffing/Supply/Note] [Staffing/Supply/Department, Staffing/Supply/Note]",
    "r01 /Staffing[1]/Supply[-5]/Note A12Kernel.Polarity.omission [/Staffing[1]/Supply[-5]/Department, /Staffing[1]/Supply[-5]/Items[0]/Q, /Staffing[1]/Supply[-5]/Note, Staffing/Demand[2]/Base, Staffing/Demand[2]/Department] [/Staffing[1]/Supply[-5]/Department, /Staffing[1]/Supply[-5]/Items[0]/Q, /Staffing[1]/Supply[-5]/Note]",
    "r02 Staffing/Supply[2]/Note A12Kernel.Polarity.omission [/Staffing[1]/Demand[-5]/DItems[0]/P, /Staffing[1]/Demand[-5]/Department, Staffing/Supply[2]/Department, Staffing/Supply[2]/Headcount, Staffing/Supply[2]/Note] [/Staffing[1]/Demand[-5]/DItems[0]/P, /Staffing[1]/Demand[-5]/Department, Staffing/Supply[2]/Department, Staffing/Supply[2]/Note]",
    "r02 Staffing/Supply[3]/Note A12Kernel.Polarity.omission [/Staffing[1]/Demand[-5]/DItems[0]/P, /Staffing[1]/Demand[-5]/Department, Staffing/Supply[3]/Department, Staffing/Supply[3]/Headcount, Staffing/Supply[3]/Note] [/Staffing[1]/Demand[-5]/DItems[0]/P, /Staffing[1]/Demand[-5]/Department, Staffing/Supply[3]/Department, Staffing/Supply[3]/Note]",
    "r02 Staffing/Supply[4]/Note A12Kernel.Polarity.omission [/Staffing[1]/Demand[-5]/DItems[0]/P, /Staffing[1]/Demand[-5]/Department, Staffing/Supply[4]/Department, Staffing/Supply[4]/Headcount, Staffing/Supply[4]/Note] [/Staffing[1]/Demand[-5]/DItems[0]/P, /Staffing[1]/Demand[-5]/Department, Staffing/Supply[4]/Department, Staffing/Supply[4]/Note]",
    "r03 Staffing/Supply/Note A12Kernel.Polarity.omission [Staffing/Demand/DSub/Y, Staffing/Demand/Department, Staffing/Supply/Department, Staffing/Supply/Headcount, Staffing/Supply/Note] [Staffing/Demand/DSub/Y, Staffing/Demand/Department, Staffing/Supply/Department, Staffing/Supply/Note]",
    "r03 Staffing/Supply[2]/Note A12Kernel.Polarity.omission [/Staffing[1]/Demand[-5]/DSub[1]/Y, /Staffing[1]/Demand[-5]/Department, Staffing/Supply[2]/Department, Staffing/Supply[2]/Headcount, Staffing/Supply[2]/Note] [/Staffing[1]/Demand[-5]/DSub[1]/Y, /Staffing[1]/Demand[-5]/Department, Staffing/Supply[2]/Department, Staffing/Supply[2]/Note]",
    "r03 Staffing/Supply[3]/Note A12Kernel.Polarity.omission [/Staffing[1]/Demand[-5]/DSub[1]/Y, /Staffing[1]/Demand[-5]/Department, Staffing/Supply[3]/Department, Staffing/Supply[3]/Headcount, Staffing/Supply[3]/Note] [/Staffing[1]/Demand[-5]/DSub[1]/Y, /Staffing[1]/Demand[-5]/Department, Staffing/Supply[3]/Department, Staffing/Supply[3]/Note]",
    "r03 Staffing/Supply[4]/Note A12Kernel.Polarity.omission [/Staffing[1]/Demand[-5]/DSub[1]/Y, /Staffing[1]/Demand[-5]/Department, Staffing/Supply[4]/Department, Staffing/Supply[4]/Headcount, Staffing/Supply[4]/Note] [/Staffing[1]/Demand[-5]/DSub[1]/Y, /Staffing[1]/Demand[-5]/Department, Staffing/Supply[4]/Department, Staffing/Supply[4]/Note]",
    "r04 /Staffing[1]/Supply[-5]/Note A12Kernel.Polarity.omission [/Staffing[1]/Supply[-5]/Department, /Staffing[1]/Supply[-5]/Items[0]/Deep[0]/R, /Staffing[1]/Supply[-5]/Note, Staffing/Demand[2]/Base, Staffing/Demand[2]/Department] [/Staffing[1]/Supply[-5]/Department, /Staffing[1]/Supply[-5]/Items[0]/Deep[0]/R, /Staffing[1]/Supply[-5]/Note]",
    "r05 /Staffing[1]/Supply[-5]/Note A12Kernel.Polarity.omission [/Staffing[1]/Supply[-5]/Department, /Staffing[1]/Supply[-5]/Note, /Staffing[1]/Supply[-5]/Sub[1]/X, Staffing/Demand[2]/Base, Staffing/Demand[2]/Department] [/Staffing[1]/Supply[-5]/Department, /Staffing[1]/Supply[-5]/Note, /Staffing[1]/Supply[-5]/Sub[1]/X]"] := by
  native_decide

end A12Kernel.Dm.ParallelChildReadLocks
