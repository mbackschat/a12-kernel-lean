import Lean.Data.Json
import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Document
import A12Kernel.Reference.Dm.ParallelValidation

/-! # Ordinary leaves over one joined parallel instance

Reader-to-evaluator locks for leaves a key join evaluates through the ordinary elaborators against
its instance view. The model is the staffing topology of the retained Kernel 30.8.1 captures
`evidence/kernel-30.8.1/captures/parallel-instance-leaves-2026-10-14/`: a fixed root, a keyed
`Demand` and a keyed `Supply` group, reduced to the fields these rows read. Every expectation is
the capture's own message or change; each rule keeps one representative of an independent branch.

Validation (error field `Supply/Headcount`): a text equality on the target side, a Date comparison
across the join, membership and its negation on the partner's Enumeration, a String comparison
between the two sides, a partner text inequality, and a `Length` guard. The rows separate a
matched partner, an unmatched one that reads as empty, and a malformed partner Date.

Computation (`[Demand/Base] + [Headcount]` into a Supply target): positive presence of the target's
own group, a field-fill list across the join, presence of the partner group, a cross-join Date
guard, partner membership and presence of the enclosing root. Negative presence of the target's own
group is refused statically, as the Kernel refuses it.
-/

namespace A12Kernel.Dm.ParallelInstanceViewLocks

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
private def kind : Json := Json.mkObj [("type", "EnumerationType"), ("EnumerationType", Json.mkObj [
  ("values", Json.arr #[Json.mkObj [("value", "a")], Json.mkObj [("value", "b")]])])]

private def keyed (name : String) (fields : List Json) : Json :=
  element "Group" s!"/Staffing/{name}" name [("repeatability", toJson 50),
    ("elements", Json.arr (field name "Department" text :: fields).toArray), ("indexFieldName", "Department")]

private def rule (name condition : String) : Json :=
  element "Rule" s!"/Staffing/{name}" name [("errorEntityRelPath", "../Supply/Headcount"),
    ("errorCode", .str name), ("errorCondition", .str s!"FieldFilled(Supply/Headcount) And {condition}"),
    ("severity", "ERROR"), ("errorMessage", Json.arr #[Json.mkObj [("locale", "en_US"), ("text", "m")]])]

private def computation (target guard : String) : Json :=
  element "Computation" s!"/Staffing/Supply/C{target}" s!"C{target}" [("computedFieldRelPath", .str s!"../{target}"),
    ("computationAlternatives", Json.arr #[Json.mkObj [("precondition", .str guard),
      ("operation", "[/Staffing/Demand/Base] + [Headcount]")]]),
    ("errorMessage", Json.arr #[Json.mkObj [("locale", "en_US"), ("text", "m")]])]

private def targets : List String := ["Own", "Cross", "Partner", "Temporal", "Member", "Root"]

private def guards : List (String × String) := [
  ("Own", "GroupFilled(/Staffing/Supply)"),
  ("Cross", "AtLeastOneFieldFilled(/Staffing/Demand/Base, /Staffing/Demand/Stamp)"),
  ("Partner", "GroupFilled(/Staffing/Demand)"),
  ("Temporal", "[/Staffing/Demand/Stamp] > [Due]"),
  ("Member", "FieldValueIncludedInValueList(/Staffing/Demand/Kind, \"a\")"),
  ("Root", "GroupFilled(/Staffing)")]

private def rules : List (String × String) := [
  ("text", "FieldFilled(Demand/Base) And [Supply/Note] == \"x\""),
  ("date", "[Demand/Stamp] > [Supply/Due]"),
  ("member", "FieldValueIncludedInValueList(Demand/Kind, \"a\")"),
  ("nonMember", "FieldValueNotIncludedInValueList(Demand/Kind, \"a\")"),
  ("sides", "[Supply/Note] == [Demand/Label]"),
  ("partnerText", "[Demand/Label] != \"x\""),
  ("length", "FieldFilled(Demand/Base) And Length(Supply/Note) > 1")]

private def dm? (extra : List Json := []) : Option DmModel :=
  (readModel (Json.mkObj [("content", Json.mkObj [("modelRoot", Json.mkObj [("rootGroups", Json.arr #[
    element "Group" "/Staffing" "Staffing" [("repeatability", toJson 1), ("elements", Json.arr (#[
      element "Field" "/Staffing/PlanName" "PlanName" [("fieldType", text)],
      keyed "Demand" [field "Demand" "Base" number, field "Demand" "Stamp" date, field "Demand" "Kind" kind,
        field "Demand" "Label" text],
      keyed "Supply" ([field "Supply" "Headcount" number, field "Supply" "Note" text, field "Supply" "Due" date] ++
        (targets ++ ["Not"]).map (field "Supply" · number) ++
        guards.map (fun (target, guard) => computation target guard) ++ extra)] ++
      (rules.map fun (name, condition) => rule name condition).toArray))]])])])])).toOption

private def world : World := { now := { epochMillis := 0 }, modelZoneRules := ModelZone.concreteRules }

private def checked? (dm : DmModel) (document : Json) :
    Option (PreparedFlatStringContext dm.flat builtinStringPatternCompiler × CheckedDocument dm.flat) := do
  let input ← (readDocument dm document).toOption
  if !input.refusals.isEmpty then none
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler dm.flat).toOption
  pure (prepared, ← (checkDocument prepared "en_US" input.data).toOption)

private def row (entries : List (String × String)) : Json :=
  Json.mkObj (entries.map fun (key, value) => (key, Json.str value))

private def staffing (demand supply : List (List (String × String))) (fixed : List (String × String) := []) : Json :=
  Json.mkObj [("Staffing", Json.mkObj (fixed.map (fun (key, value) => (key, Json.str value)) ++
    [("Demand", Json.arr (demand.map row).toArray), ("Supply", Json.arr (supply.map row).toArray)]))]

/-- Each rule's firings in rule order, as `name pointer polarity`. -/
private def fired (document : Json) : Option (List String) := do
  let dm ← dm?
  let (_, checked) ← checked? dm document
  let messages ← dm.rules.mapM fun source => do
    let plan ← (checkValidationRule dm .english source world).toOption
    let fired ← (runValidationRule world checked plan).toOption
    pure (fired.map fun message => s!"{source.name} {renderPointer dm.flat message.errorAddress} {reprStr message.messageType}")
  pure messages.flatten

/-- Every reported target change, as `pointer outcome`. -/
private def computed (document : Json) : Option (List String) := do
  let dm ← dm?
  let (prepared, checked) ← checked? dm document
  let lowered ← dm.computations.mapM fun source => (lowerComputation dm.flat .english source).toOption
  let outcomes ← (runComputations world prepared checked (lowered.map (·.2))).toOption
  pure (outcomes.map fun outcome => s!"{outcome.pointer} {outcome.outcome}")

private def validationMatched : Json := staffing
  [[("Department", "A"), ("Base", "10"), ("Stamp", "2026-10-01"), ("Kind", "a"), ("Label", "x")], [("Department", "C")]]
  [[("Department", "A"), ("Headcount", "5"), ("Note", "x"), ("Due", "2026-09-01")],
   [("Department", "B"), ("Headcount", "3"), ("Note", "ab"), ("Due", "2026-12-01")]]

private def validationEmpty : Json := staffing
  [[("Department", "A")], [("Department", "B"), ("Base", "3"), ("Stamp", "2026-01-01"), ("Kind", "b"), ("Label", "q")]]
  [[("Department", "A"), ("Headcount", "1"), ("Note", "a"), ("Due", "2026-01-01")],
   [("Department", "B"), ("Headcount", "2")]]

private def validationMalformed : Json := staffing
  [[("Department", "A"), ("Base", "x1"), ("Stamp", "2026-13-40"), ("Kind", "zz"), ("Label", "x")]]
  [[("Department", "A"), ("Headcount", "1"), ("Note", "x"), ("Due", "2026-01-01")]]

example : fired validationMatched = some [
    "text Staffing/Supply/Headcount A12Kernel.Polarity.value",
    "date Staffing/Supply/Headcount A12Kernel.Polarity.value",
    "member Staffing/Supply/Headcount A12Kernel.Polarity.value",
    "sides Staffing/Supply/Headcount A12Kernel.Polarity.value"] := by native_decide

-- The unmatched partner of row A reads as empty: no text or membership leaf fires on it.
example : fired validationEmpty = some [
    "nonMember Staffing/Supply[2]/Headcount A12Kernel.Polarity.value",
    "partnerText Staffing/Supply[2]/Headcount A12Kernel.Polarity.value"] := by native_decide

-- A malformed partner Date and Enumeration decide nothing; the String sides still compare.
example : fired validationMalformed = some [
    "sides Staffing/Supply/Headcount A12Kernel.Polarity.value"] := by native_decide

private def outs : List (String × String) := (targets ++ ["Not"]).map (·, "999")

private def changes (target : String) (outcomes : List String) : List String :=
  outcomes.zipIdx.map fun (outcome, index) =>
    s!"Staffing/Supply{if index == 0 then "" else s!"[{index + 1}]"}/{target} {outcome}"

-- Row C has no partner: its partner reads as empty, so only guards on its own row or the root hold.
example : computed (staffing
    [[("Department", "A"), ("Base", "10"), ("Stamp", "2026-10-01"), ("Kind", "a")],
     [("Department", "B"), ("Base", "20"), ("Kind", "b")]]
    [[("Department", "A"), ("Headcount", "1"), ("Note", "x"), ("Due", "2026-09-01")] ++ outs,
     [("Department", "B"), ("Note", "ab")] ++ outs,
     [("Department", "C"), ("Headcount", "3"), ("Note", "yy"), ("Due", "2026-12-01")] ++ outs]) = some (
    changes "Own" ["value 11", "value 20", "value 3"] ++
    changes "Cross" ["value 11", "value 20", "cleared"] ++
    changes "Partner" ["value 11", "value 20", "cleared"] ++
    changes "Temporal" ["value 11", "cleared", "cleared"] ++
    changes "Member" ["value 11", "cleared", "cleared"] ++
    changes "Root" ["value 11", "value 20", "value 3"]) := by native_decide

-- A partner row holding only its key is present content; an empty partner Date decides no comparison.
example : computed (staffing
    [[("Department", "A")], [("Department", "B"), ("Stamp", "2026-01-01"), ("Kind", "a")]]
    [[("Department", "A")] ++ outs, [("Department", "B"), ("Headcount", "2"), ("Due", "2026-02-01")] ++ outs]
    [("PlanName", "P")]) = some (
    changes "Own" ["value 0", "value 2"] ++ changes "Cross" ["cleared", "value 2"] ++
    changes "Partner" ["value 0", "value 2"] ++ changes "Temporal" ["cleared", "cleared"] ++
    changes "Member" ["cleared", "value 2"] ++ changes "Root" ["value 0", "value 2"]) := by native_decide

example : computed (Json.mkObj [("Staffing", Json.mkObj [("Supply", Json.arr #[
    row ([("Department", "A"), ("Headcount", "5"), ("Note", "x")] ++ outs)])])]) = some (
    changes "Own" ["value 5"] ++ changes "Cross" ["cleared"] ++ changes "Partner" ["cleared"] ++
    changes "Temporal" ["cleared"] ++ changes "Member" ["cleared"] ++ changes "Root" ["value 5"]) := by
  native_decide

-- A negative read of the target's own group is a reference to the computed field.
example : (do
    let dm ← dm? [computation "Not" "GroupNotFilled(/Staffing/Supply)"]
    let source ← dm.computations.getLast?
    pure (match lowerComputation dm.flat .english source with
      | .ok _ => "admitted"
      | .error refusal => refusal.detail)) =
      some KernelStaticDiagnostic.errorReferenceToCalculatedField.kernelCode := by native_decide

end A12Kernel.Dm.ParallelInstanceViewLocks
