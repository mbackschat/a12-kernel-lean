import Lean.Data.Json
import A12Kernel.Reference.Dm.SampleAcceptance
import A12Kernel.Reference.Dm.LoneSurrogate
import A12Kernel.Reference.Dm.ComputeMessages

/-! # A power whose scale leaves the host's range fails its rule and ends its computation, through the reader

A product inside power whose decimal scale leaves the host's signed 32-bit range raises
([spec/04 §3](../../../spec/04-numbers-and-decimals.md#3-arithmetic-domain-failures-are-consumer-sensitive)).
The rule handler reports the raise as one VALUE message with the rule's code, its severity and empty
reference sets, under full and partial validation alike; the validation locks replay each rule against
the Kernel's messages and reference sets through [`replayRules`](Replay.lean), or its partial
counterpart. In a computation the raise ends the expression and leaves the Number target without a
value; the computation locks run the model's computations through `runModelComputationsWithMessages`
and compare the computed outcomes and the formal-error channel by pointer and code, not the
validation messages.

Kernel oracles: the [power-range capture](../../../evidence/kernel-31.3.1/captures/power-scale-range-2026-11-12/MANIFEST.sha256)
(`PowA`, `PowB2` and `PowD` for rules, `PowC` and `PowE` for computations), whose rows are written out
below with their message text left out, and a12-dmkits' KF690 control,
`test-data-generator/evidence/power-scale-2026-11-11/` at `b334b0e73`, whose two models are rebuilt here
field for field. The capture's in-range rows `small-in-range-just-in` (in `PowA` and `PowC`) and `PowB1`
fail later, at the comparison's or the target's rescale, which the theory does not model, so they have
no lock here.
-/

namespace A12Kernel.Dm.PowerScaleRangeLocks
open A12Kernel A12Kernel.Dm Lean

private def world : World := { now := { epochMillis := 0 } }

private def capturedModel : String :=
  include_str "../../../evidence/kernel-31.3.1/captures/power-scale-range-2026-11-12/PowA.json"

private def capturedRequest : String :=
  include_str "../../../evidence/kernel-31.3.1/captures/power-scale-range-2026-11-12/request-PowA.json"

private def capturedTwoPowersModel : String :=
  include_str "../../../evidence/kernel-31.3.1/captures/power-scale-range-2026-11-12/PowB2.json"

private def capturedTwoPowersRequest : String :=
  include_str "../../../evidence/kernel-31.3.1/captures/power-scale-range-2026-11-12/request-PowB2.json"

/-- A row's inline document in a captured request. -/
private def documentOf (requestText name : String) : Option Json := do
  let request ← (Json.parse requestText).toOption
  let rows ← (request.getObjValAs? (Array Json) "rows").toOption
  let row ← rows.find? fun row => (row.getObjValAs? String "name").toOption == some name
  (row.getObjVal? "documentInline").toOption

/-- Whether every rule matches the Kernel under full validation, reference sets included, and, when a
relevant set is given, under partial validation. -/
private def agrees (dm : DmModel) (document : Json) (kernel : List ObservedReferences)
    (relevant : Option (List RelevantEntityPattern)) : Bool := Id.run do
  let some input := (readDocument dm document).toOption | return false
  if !input.refusals.isEmpty then return false
  let some prepared := (prepareFlatStringContext world builtinStringPatternCompiler dm.flat).toOption
    | return false
  let some checked := (checkDocument prepared "en_US" input.data).toOption | return false
  let full := replayRules dm .english world checked (kernel.map (·.message)) kernel
  let fullMatched := full.all fun verdict =>
    verdict.status.tier == "match" && (verdict.references.map (·.tier)).getD "match" == "match"
  match relevant with
  | none => fullMatched
  | some relevant =>
      fullMatched && (replayRulesPartial dm .english world checked relevant (kernel.map (·.message))).all
        (·.status.tier == "match")

private def reported (code field : String) (severity := "ERROR") (referenced : List String := []) :
    ObservedReferences :=
  { message := { code, pointer := field, messageType := "VALUE_ERROR", severity }, referenced, fillToFix := [] }

private def bigFired : ObservedReferences := reported "BigGt" "P/Big" (referenced := ["P/Big", "P/E1", "P/E2", "P/E3"])

private def smallFired : ObservedReferences :=
  reported "SmallGt" "P/Small" (referenced := ["P/F1", "P/F2", "P/F3", "P/Small"])

private def bigRaised : List ObservedReferences :=
  [reported "BigGt" "P/Big", reported "BigLt" "P/Big", reported "BigLtWarn" "P/Big" "WARNING"]

private def smallRaised : List ObservedReferences := [reported "SmallGt" "P/Small", reported "SmallLt" "P/Small"]

/-- The Kernel's messages per `PowA` row; its partial calls report the same messages. -/
private def capturedRows : List (String × String × List ObservedReferences) := [
  ("unit-control", "Big", [bigFired, smallFired]),
  ("big-overflow-144", "Big", bigRaised ++ [smallFired]),
  ("big-negative-odd-overflow", "Big", bigRaised ++ [smallFired]),
  ("small-underflow-just-out", "Small", bigFired :: smallRaised),
  ("small-reciprocal-overflow", "Small", bigFired :: smallRaised),
  ("big-exponent-domain-control", "Big", [smallFired, reported "zahlZuGross" "P/E3" (referenced := ["P/E3"])])]

/-- Overflow through `999999999999999` and through its negation, underflow through `10^-14`, and
overflow through the reciprocal of `10^-14`, fail every rule that reaches the power, the WARNING rule
under its own severity, while the other chain's rules keep their ordinary verdicts; an exponent above the
field's maximum stays a formal finding. -/
example : (do
    let dm ← ((parseModelJson capturedModel).bind (readModel ·)).toOption
    capturedRows.mapM fun (name, field, kernel) => do
      let document ← documentOf capturedRequest name
      pure (agrees dm document kernel (some [.allInstances ["P", field], .allInstances ["P"]]))) =
    some (List.replicate 6 true) := by
  native_decide

/-- Two powers of `999999999999999` reach about fifteen million digits inside the range: ordinary
verdicts with their reference sets. -/
example : (do
    let dm ← ((parseModelJson capturedTwoPowersModel).bind (readModel ·)).toOption
    let document ← documentOf capturedTwoPowersRequest "two-powers-fifteen-million-digits"
    pure (agrees dm document [bigFired, smallFired,
      reported "TwoGt" "P/Big" (referenced := ["P/Big", "P/E1", "P/E2"])] none)) = some true := by
  native_decide

private def capturedSiblingModel : String :=
  include_str "../../../evidence/kernel-31.3.1/captures/power-scale-range-2026-11-12/PowD.json"

private def capturedSiblingRequest : String :=
  include_str "../../../evidence/kernel-31.3.1/captures/power-scale-range-2026-11-12/request-PowD.json"

private def siblingRaised : List ObservedReferences :=
  ["DivThenPow", "MThenPow", "PowThenDiv", "PowThenM"].map (reported · "P/Big")

/-- `PowD`: an overflowing power raises past a malformed, empty, zero-divided or valued sibling, left or
right of it, so all four rules fail; with the power inside the range the malformed sibling leaves them
silent. -/
example : (do
    let dm ← ((parseModelJson capturedSiblingModel).bind (readModel ·)).toOption
    [("malformed-sibling", siblingRaised ++ [reported "zahlHatDezimalTrenner" "P/M" (referenced := ["P/M"])]),
      ("empty-sibling", siblingRaised ++ [reported "mandatoryField" "P/M" (referenced := ["P/M"])]),
      ("zero-divisor-sibling", siblingRaised), ("valued-sibling-control", siblingRaised),
      ("in-range-malformed-control", [reported "zahlHatDezimalTrenner" "P/M" (referenced := ["P/M"])])].mapM
      fun (name, kernel) => do
        let document ← documentOf capturedSiblingRequest name
        pure (agrees dm document kernel none)) = some (List.replicate 5 true) := by
  native_decide

private def number (name : String) (digits : Nat) (minimum maximum : Json) : Json :=
  Json.mkObj [("type", "Field"), ("id", Json.str s!"/Parcel/{name}"), ("name", Json.str name),
    ("Field", Json.mkObj [("fieldType", Json.mkObj [("type", "NumberType"), ("NumberType", Json.mkObj [
      ("maxFractionalDigits", toJson digits), ("minValue", minimum), ("maxValue", maximum)])]),
      ("requirednessConfig", Json.mkObj [("mode", "absoluteOrRelativeToNextRepAncestor")])])]

/-- a12-dmkits' KF690 model with the comparison `comparison` against zero. -/
private def controlModel (comparison : String) : Json :=
  let rule := Json.mkObj [("type", "Rule"), ("id", "/Parcel/PowerSign"), ("name", "PowerSign"),
    ("Rule", Json.mkObj [("errorEntityRelPath", "../Amount"), ("errorCode", "POWER_SIGN"),
      ("errorCondition", Json.str s!"\{ \{ [Amount] ^ [Exponent] } ^ [Exponent] } ^ [Exponent] {comparison} 0"),
      ("severity", "ERROR"), ("errorMessage", Json.arr #[Json.mkObj [("locale", "en_US"), ("text", "PowerSign")]])])]
  Json.mkObj [
    ("header", Json.mkObj [("id", "PowerControl"), ("modelType", "document"), ("modelVersion", "29.8.0"),
      ("locales", Json.arr #[Json.mkObj [("code", "en_US")]]), ("labels", Json.arr #[]),
      ("annotations", Json.arr #[]), ("modelReferences", Json.arr #[])]),
    ("content", Json.mkObj [
      ("modelInfo", Json.mkObj [("name", "PowerControl"), ("variant", "cockpit"), ("revision", "Arbeitsversion"),
        ("immutable", false)]),
      ("modelConfig", Json.mkObj [("decimalSeparator", "."), ("timeZone", "Europe/Berlin"),
        ("conditionLanguage", Json.mkObj [("code", "en_US")]), ("fieldRefByShortNameAllowed", true)]),
      ("modelRoot", Json.mkObj [("rootGroups", Json.arr #[Json.mkObj [("type", "Group"), ("id", "/Parcel"),
        ("name", "Parcel"), ("Group", Json.mkObj [("repeatability", toJson (1 : Nat)), ("elements", Json.arr #[
          number "Amount" 3 (Json.num ⟨1, 3⟩) (toJson (1000 : Nat)),
          number "Exponent" 0 (toJson (1000 : Nat)) (toJson (1001 : Nat)), rule])])]])])])]

private def parcel (amount : JsonNumber) (exponent : Nat) : Json :=
  Json.mkObj [("Parcel", Json.mkObj [("Amount", Json.num amount), ("Exponent", toJson exponent)])]

/-- The KF690 rows: the unit control and the domain control keep their ordinary verdicts under `<` and
`>`, while `1000` and `0.001` through `1000` three times fail the rule under both. -/
example : (do
    let negative ← (readModel (controlModel "<")).toOption
    let positive ← (readModel (controlModel ">")).toOption
    let raised := [reported "POWER_SIGN" "Parcel/Amount"]
    pure [agrees negative (parcel 1 1000) [] none,
      agrees negative (parcel 1000 1000) raised none,
      agrees negative (parcel ⟨1, 3⟩ 1000) raised none,
      agrees negative (parcel 1000 1001) [] none,
      agrees positive (parcel 1 1000)
        [reported "POWER_SIGN" "Parcel/Amount" (referenced := ["Parcel/Amount", "Parcel/Exponent"])] none,
      agrees positive (parcel 1000 1000) raised none,
      agrees positive (parcel ⟨1, 3⟩ 1000) raised none,
      agrees positive (parcel 1000 1001) [] none]) = some (List.replicate 8 true) := by
  native_decide

private def capturedComputedModel : String :=
  include_str "../../../evidence/kernel-31.3.1/captures/power-scale-range-2026-11-12/PowC.json"

private def capturedComputedRequest : String :=
  include_str "../../../evidence/kernel-31.3.1/captures/power-scale-range-2026-11-12/request-PowC.json"

private def capturedOrderModel : String :=
  include_str "../../../evidence/kernel-31.3.1/captures/power-scale-range-2026-11-12/PowE.json"

private def capturedOrderRequest : String :=
  include_str "../../../evidence/kernel-31.3.1/captures/power-scale-range-2026-11-12/request-PowE.json"

/-- A row's computed outcomes beside the call's formal-error channel. -/
private def computed (modelText requestText name : String) :
    Option (List ComputedOutcome × List ComputedMessage) := do
  let dm ← ((parseModelJson modelText).bind (readModel ·)).toOption
  let document ← documentOf requestText name
  let input ← (readDocument dm document).toOption
  if !input.refusals.isEmpty then none
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler dm.flat).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  (runModelComputationsWithMessages dm .english world prepared checked).toOption

/-- Whether a row's computed outcomes and its formal-error channel, each in any order, equal the Kernel's. -/
private def computes (modelText requestText name : String) (outcomes : List (String × String))
    (channel : List (String × String)) : Bool :=
  match computed modelText requestText name with
  | some (observed, messages) =>
      let sorted (entries : List ComputedOutcome) := entries.mergeSort (compare · · != Ordering.gt)
      sorted observed == sorted (outcomes.map fun (pointer, outcome) => { pointer, outcome }) &&
        messages.mergeSort (compare · · != Ordering.gt) ==
          (channel.map fun (pointer, code) => ({ pointer, code } : ComputedMessage)).mergeSort
            (compare · · != Ordering.gt)
  | none => false

private def valueless (target : String) : String × String := (s!"P/{target}", "berechnungsWertFehler")

/-- `PowC`: a power that raises leaves its two-decimal target without a value and reports
`berechnungsWertFehler` there, while the other chain's target computes; an exponent above the field's
maximum stays a formal finding that poisons its target silently. The in-range row `small-in-range-just-in`
raises at the target's rescale, which the theory does not model, so it has no lock here. -/
example : [("unit-control", [("P/TgtBig", "value 1"), ("P/TgtSmall", "value 0")], []),
    ("big-overflow-144", [("P/TgtSmall", "value 0")], [valueless "TgtBig"]),
    ("small-underflow-just-out", [("P/TgtBig", "value 1")], [valueless "TgtSmall"]),
    ("small-reciprocal-overflow", [("P/TgtBig", "value 1")], [valueless "TgtSmall"]),
    ("big-negative-odd-overflow", [("P/TgtSmall", "value 0")], [valueless "TgtBig"]),
    ("big-exponent-domain-control", [("P/TgtSmall", "value 0")], [("P/E3", "zahlZuGross")])].all
      (fun (name, outcomes, channel) =>
        computes capturedComputedModel capturedComputedRequest name outcomes channel) = true := by
  native_decide

/-- `PowE`: the raise ends a computation's evaluation, so a power left of a malformed operand reports
`berechnungsWertFehler` on its target, while a malformed operand left of the power poisons its target
first and silently. An empty or zero-divided sibling, or a valued one, leaves every target reporting. -/
example : [("malformed-sibling",
      [valueless "TPowThenDiv", valueless "TPowThenM", ("P/M", "zahlHatDezimalTrenner")]),
    ("empty-sibling", ["TDivThenPow", "TMThenPow", "TPowThenDiv", "TPowThenM"].map valueless),
    ("zero-divisor-sibling", ["TDivThenPow", "TMThenPow", "TPowThenDiv", "TPowThenM"].map valueless),
    ("valued-sibling-control", ["TDivThenPow", "TMThenPow", "TPowThenDiv", "TPowThenM"].map valueless),
    ("in-range-malformed-control", [("P/M", "zahlHatDezimalTrenner")])].all
      (fun (name, channel) => computes capturedOrderModel capturedOrderRequest name [] channel) = true := by
  native_decide

end A12Kernel.Dm.PowerScaleRangeLocks
