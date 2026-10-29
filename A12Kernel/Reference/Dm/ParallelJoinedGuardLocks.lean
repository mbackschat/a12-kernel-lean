import Lean.Data.Json
import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Document
import A12Kernel.Reference.Dm.GeneratedComputationRule
import A12Kernel.Reference.Dm.ParallelValidation
import A12Kernel.Reference.Dm.EntryFrameFixture

/-! # Ordinary leaves beside a key join

Reader-to-evaluator locks for leaves of a joined computation guard or a parallel rule that the
instance view cannot check: a clock read, a starred or filtered aggregate, a keyed read of a third or
of the partner group, a key read on the error side's row, and a pattern test. Each keeps its
ordinary meaning at the common row, or at the error side's row where only that row binds its reads,
beside the joined operation `[/Staffing/Demand/Base] + [Headcount]` or the pair guard
`FieldFilled(Supply/Headcount) And FieldFilled(Demand/Base)`, and a starred aggregate inside a joined
operation and its generated rule. The model and documents are reductions
of the retained Kernel 30.8.1 capture
`evidence/kernel-30.8.1/captures/joined-carrier-admission-2026-10-14/`, whose clock this world pins;
every expectation is the capture's own change or message.

The documents separate a matched partner, an unmatched row whose partner reads as empty, a clock
read on each side of the join, a filtered aggregate, keyed read or keyed partner read that selects
nothing, and a key on the error side's row that selects a row, none, or an unfilled one.
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

private def computation (target guard : String)
    (operation : String := "[/Staffing/Demand/Base] + [Headcount]") : Json :=
  element "Computation" s!"/Staffing/Supply/C{target}" s!"C{target}" [("computedFieldRelPath", .str s!"../{target}"),
    ("computationAlternatives", Json.arr #[Json.mkObj [("precondition", .str guard),
      ("operation", .str operation)]]),
    ("errorMessage", Json.arr #[Json.mkObj [("locale", "en_US"), ("text", "m")]])]

private def rule (name condition : String) : Json :=
  element "Rule" s!"/Staffing/{name}" name [("errorEntityRelPath", "../Supply/Headcount"),
    ("errorCode", .str name), ("errorCondition",
      .str s!"FieldFilled(Supply/Headcount) And FieldFilled(Demand/Base) And {condition}"),
    ("severity", "ERROR"), ("errorMessage", Json.arr #[Json.mkObj [("locale", "en_US"), ("text", "m")]])]

private def rules : List (String × String) := [
  ("k01", "FieldFilled(/Staffing/Ledger/Amount For \"k1\")"),
  ("k02", "[/Staffing/Ledger/Amount For \"k1\"] > 0"),
  ("k03b", "GroupFilled(/Staffing/Ledger For Supply/Note)"),
  ("k05", "GroupFilled(/Staffing/Demand For \"A\")"),
  ("k07b", "[Supply/Headcount] > [/Staffing/Ledger/Amount For Supply/Note]"),
  ("k08", "FieldFilled(/Staffing/Ledger/Amount For Supply/Note)"),
  ("k09", "FieldFilled(/Staffing/Demand/Base For \"A\")")]

private def dm? : Option DmModel :=
  (readModel (checkedEntryFrame <| Json.mkObj [("content", Json.mkObj [("modelRoot", Json.mkObj [("rootGroups", Json.arr #[
    element "Group" "/Staffing" "Staffing" [("repeatability", toJson 1), ("elements", Json.arr (#[
      element "Field" "/Staffing/PlanName" "PlanName" [("fieldType", text)],
      keyed "Demand" "Department" [field "Demand" "Headcount" number, field "Demand" "Base" number,
        field "Demand" "Stamp" date],
      keyed "Supply" "Department" ([field "Supply" "Headcount" number, field "Supply" "Note" text,
        field "Supply" "Due" date] ++ guards.map (fun (target, _) => field "Supply" target number) ++
        guards.map (fun (target, guard) => computation target guard) ++ [field "Supply" "Out11" number,
          computation "Out11" "FieldFilled(Headcount)" "[/Staffing/Demand/Base] + Sum(/Staffing/Demand*/Base)"]),
      keyed "Ledger" "Code" [field "Ledger" "Amount" number]] ++
      (rules.map fun (name, condition) => rule name condition).toArray))]])])])])).toOption

-- The capture's clock, 2026-10-14T10:00:00Z.
private def world : World := { now := { epochMillis := 1791972000000 }, modelZoneRules := ModelZone.concreteRules }

private def row (entries : List (String × String)) : Json :=
  Json.mkObj (entries.map fun (key, value) => (key, Json.str value))

private def outs : List (String × String) := guards.map (·.1, "999") ++ [("Out11", "999")]

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

/-- Each parallel rule's firings, then each computation's generated rule's, as `code pointer type`. -/
private def fired (document : Json) : Option (List String) := do
  let dm ← dm?
  let input ← (readDocument dm document).toOption
  if !input.refusals.isEmpty then none
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler dm.flat).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  let generated ← dm.computations.mapM (·.generatedRule? .english)
  let messages ← (dm.rules ++ generated).mapM fun source => do
    let plan ← (checkValidationRule dm .english source world).toOption
    let fired ← (runValidationRule world checked plan).toOption
    pure (fired.map fun message =>
      s!"{source.errorCode} {renderPointer dm.flat message.errorAddress} {reprStr message.messageType}")
  pure messages.flatten

/-- The reference channels of one parallel rule's firings, sorted, as `pointer referenced fillToFix`. -/
private def referenced (name : String) (document : Json) : Option (List (String × List String × List String)) := do
  let dm ← dm?
  let input ← (readDocument dm document).toOption
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler dm.flat).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  let source ← dm.rules.find? (·.name == name)
  let .parallel plan ← (checkValidationRule dm .english source world).toOption | none
  let fired ← (runParallelRuleReferences checked plan (some world)).toOption
  let sorted := fun (pointers : List MessagePointer) =>
    (pointers.map (renderFieldPointer dm.flat)).eraseDups.mergeSort (compare · · != .gt)
  fired.mapM fun (message, references) => do
    let references ← references.toOption
    pure (renderPointer dm.flat message.errorAddress, sorted references.referenced, sorted references.fillToFix)

private def changes (row : String) (outcomes : List String) : List String :=
  (guards.zip outcomes).map fun ((target, _), outcome) => s!"Staffing/Supply{row}/{target} {outcome}"

private def matched : Json := staffing [
  ("Ledger", [[("Code", "k1"), ("Amount", "4")], [("Code", "x"), ("Amount", "9")]]),
  ("Demand", [[("Department", "A"), ("Base", "10"), ("Headcount", "1"), ("Stamp", "2026-10-01")],
    [("Department", "B"), ("Base", "20"), ("Stamp", "2026-11-20")]]),
  ("Supply", [[("Department", "A"), ("Headcount", "1"), ("Note", "x"), ("Due", "2026-09-01")] ++ outs,
    [("Department", "B"), ("Headcount", "7"), ("Note", "AB"), ("Due", "2026-12-01")] ++ outs,
    [("Department", "C"), ("Headcount", "3"), ("Note", "k1"), ("Due", "2026-12-01")] ++ outs])]

private def sparse : Json := staffing [
  ("Demand", [[("Department", "A"), ("Headcount", "0")],
    [("Department", "B"), ("Base", "5"), ("Stamp", "2026-01-01")]]),
  ("Supply", [[("Department", "A")] ++ outs,
    [("Department", "B"), ("Headcount", "2"), ("Due", "2026-02-01"), ("Note", "k1")] ++ outs])]
  [("PlanName", "P")]

-- Row C has no partner: its clock read on the partner side decides nothing, its own `Due` does. A
-- starred sum inside the joined operation spans every Demand row, `30`, beside the joined partner's.
example : (computed matched).map (·.mergeSort) = some (
    changes "" ["cleared", "cleared", "value 11", "value 11", "value 11", "value 11", "value 11",
      "cleared", "value 11"] ++
    changes "[2]" (List.replicate 9 "value 27") ++
    changes "[3]" ["cleared", "value 3", "value 3", "value 3", "value 3", "value 3", "value 3",
      "cleared", "value 3"] ++
    ["Staffing/Supply/Out11 value 40", "Staffing/Supply[2]/Out11 value 50",
      "Staffing/Supply[3]/Out11 value 30"]).mergeSort := by native_decide

-- A filter that keeps no row sums to zero; an absent keyed row and a keyed partner without the read
-- field read as empty. Each guard fails and clears its target.
example : (computed sparse).map (·.mergeSort) = some (
    changes "" ["cleared", "cleared", "value 0", "value 0", "cleared", "cleared", "cleared", "cleared",
      "value 0"] ++
    changes "[2]" ["cleared", "cleared", "value 7", "value 7", "cleared", "cleared", "cleared", "cleared",
      "value 7"] ++
    ["Staffing/Supply/Out11 cleared", "Staffing/Supply[2]/Out11 value 10"]).mergeSort := by native_decide

-- A literal key selects the same row at every joined row, the partner group's own included; a key on
-- the error side's row selects per row, and a key naming no row leaves a Number read empty, an
-- OMISSION. The generated rules carry the same leaves beside the joined operation; the pattern reads
-- the error side's row.
example : fired matched = some [
    "k01 Staffing/Supply/Headcount A12Kernel.Polarity.value",
    "k01 Staffing/Supply[2]/Headcount A12Kernel.Polarity.value",
    "k02 Staffing/Supply/Headcount A12Kernel.Polarity.value",
    "k02 Staffing/Supply[2]/Headcount A12Kernel.Polarity.value",
    "k03b Staffing/Supply/Headcount A12Kernel.Polarity.value",
    "k05 Staffing/Supply/Headcount A12Kernel.Polarity.value",
    "k05 Staffing/Supply[2]/Headcount A12Kernel.Polarity.value",
    "k07b Staffing/Supply[2]/Headcount A12Kernel.Polarity.omission",
    "k08 Staffing/Supply/Headcount A12Kernel.Polarity.value",
    "k09 Staffing/Supply/Headcount A12Kernel.Polarity.value",
    "k09 Staffing/Supply[2]/Headcount A12Kernel.Polarity.value",
    "COut01 Staffing/Supply[2]/Out01 A12Kernel.Polarity.value",
    "COut02 Staffing/Supply[2]/Out02 A12Kernel.Polarity.value",
    "COut02 Staffing/Supply[3]/Out02 A12Kernel.Polarity.omission",
    "COut03 Staffing/Supply/Out03 A12Kernel.Polarity.omission",
    "COut03 Staffing/Supply[2]/Out03 A12Kernel.Polarity.omission",
    "COut03 Staffing/Supply[3]/Out03 A12Kernel.Polarity.omission",
    "COut04 Staffing/Supply/Out04 A12Kernel.Polarity.omission",
    "COut04 Staffing/Supply[2]/Out04 A12Kernel.Polarity.omission",
    "COut04 Staffing/Supply[3]/Out04 A12Kernel.Polarity.omission",
    "COut05 Staffing/Supply/Out05 A12Kernel.Polarity.omission",
    "COut05 Staffing/Supply[2]/Out05 A12Kernel.Polarity.omission",
    "COut05 Staffing/Supply[3]/Out05 A12Kernel.Polarity.omission",
    "COut06 Staffing/Supply/Out06 A12Kernel.Polarity.value",
    "COut06 Staffing/Supply[2]/Out06 A12Kernel.Polarity.value",
    "COut06 Staffing/Supply[3]/Out06 A12Kernel.Polarity.omission",
    "COut07 Staffing/Supply/Out07 A12Kernel.Polarity.value",
    "COut07 Staffing/Supply[2]/Out07 A12Kernel.Polarity.value",
    "COut07 Staffing/Supply[3]/Out07 A12Kernel.Polarity.omission",
    "COut08 Staffing/Supply[2]/Out08 A12Kernel.Polarity.value",
    "COut10 Staffing/Supply/Out10 A12Kernel.Polarity.value",
    "COut10 Staffing/Supply[2]/Out10 A12Kernel.Polarity.value",
    "COut10 Staffing/Supply[3]/Out10 A12Kernel.Polarity.omission",
    "COut11 Staffing/Supply/Out11 A12Kernel.Polarity.omission",
    "COut11 Staffing/Supply[2]/Out11 A12Kernel.Polarity.omission",
    "COut11 Staffing/Supply[3]/Out11 A12Kernel.Polarity.omission"] := by native_decide

example : fired sparse = some [
    "k05 Staffing/Supply[2]/Headcount A12Kernel.Polarity.value",
    "k07b Staffing/Supply[2]/Headcount A12Kernel.Polarity.omission",
    "COut03 Staffing/Supply/Out03 A12Kernel.Polarity.omission",
    "COut03 Staffing/Supply[2]/Out03 A12Kernel.Polarity.omission",
    "COut04 Staffing/Supply/Out04 A12Kernel.Polarity.omission",
    "COut04 Staffing/Supply[2]/Out04 A12Kernel.Polarity.omission",
    "COut10 Staffing/Supply/Out10 A12Kernel.Polarity.omission",
    "COut10 Staffing/Supply[2]/Out10 A12Kernel.Polarity.value",
    "COut11 Staffing/Supply[2]/Out11 A12Kernel.Polarity.omission"] := by native_decide

-- A literal key into the partner group names the selected row beside the joined one; an error-side
-- key that selects nothing names the unknown Ledger row, and its own row's read brings that side's
-- index field into the fill-to-fix set (KF539).
example : referenced "k05" matched = some [
    ("Staffing/Supply/Headcount",
      ["Staffing/Demand/Base", "Staffing/Demand/Department", "Staffing/Demand/Headcount",
        "Staffing/Demand/Stamp", "Staffing/Supply/Department", "Staffing/Supply/Headcount"], []),
    ("Staffing/Supply[2]/Headcount",
      ["Staffing/Demand/Base", "Staffing/Demand/Department", "Staffing/Demand/Headcount",
        "Staffing/Demand/Stamp", "Staffing/Demand[2]/Base", "Staffing/Demand[2]/Department",
        "Staffing/Supply[2]/Department", "Staffing/Supply[2]/Headcount"], [])] := by native_decide

example : referenced "k07b" sparse = some [
    ("Staffing/Supply[2]/Headcount",
      ["/Staffing[1]/Ledger[-5]/Amount", "/Staffing[1]/Ledger[-5]/Code", "Staffing/Demand[2]/Base",
        "Staffing/Demand[2]/Department", "Staffing/Supply[2]/Department", "Staffing/Supply[2]/Headcount",
        "Staffing/Supply[2]/Note"],
      ["/Staffing[1]/Ledger[-5]/Amount", "/Staffing[1]/Ledger[-5]/Code", "Staffing/Supply[2]/Department",
        "Staffing/Supply[2]/Headcount", "Staffing/Supply[2]/Note"])] := by native_decide

end A12Kernel.Dm.ParallelJoinedGuardLocks
