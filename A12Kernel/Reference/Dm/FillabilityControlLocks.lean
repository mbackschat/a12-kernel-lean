import Lean.Data.Json
import A12Kernel.Reference.Dm.ExplainedUnsatControlLocks

/-! # The fillability controls (Q2-P10) against retained Kernel rows

[Q2-P10](../../../docs/PLAN.md#q2-preparation-checklist) asks whether a model accepts a document in which
one field is filled, by asking whether the model plus one goal rule accepts any document. The goal rule
reports ERROR when the field is not filled: `FieldNotFilled` for a field outside repeatable groups and
`NumberOfFilledFields` over the starred path, compared with 0, for a field in a repeatable group, so a
row of the group must fill it. Such a starred-only rule does not iterate
([spec/07 §1.1](../../../spec/07-repetition-and-iteration.md#11-iteration-scope)). When no document is
accepted, the field can never be filled, and a
[Q2-P9](ExplainedUnsatControlLocks.lean) explanation of the goal model, with the goal rule fixed rather than
removable, says why.

The [captures](../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/MANIFEST.sha256) hold
three models, each goal model and each single removal from a goal model, every model over every cell state
of its fields, the repeatable one also over no group, no row, an empty row and a second row. The models
are inhabited, so each answer here is the field's own. Every verdict depends only on those cells: a
Boolean's states are all listed, and in `FRowBound` every filled `X` fires `XLow` unless `maxValue` is
gone, when 10 is accepted, and an `X` above 5 draws a formal finding while `maxValue` stays, so the
answers hold beyond the listed values. Each model's rows agree with the Kernel's on both strategies, each
goal model is its model plus the goal rule, the reduced models are this module's removals, and every
subset is then judged by Lean alone. -/

namespace A12Kernel.Dm.FillabilityControlLocks

open Lean SampleAcceptanceCapture ExplainedUnsatControlLocks

private def parsed (text : String) : Option Json := (parseModelJson text).toOption

private def documents (requestText : String) : List Json := (requestDocuments requestText).getD []

private def full (modelText : String) : Json := (parsed modelText).getD .null

/-- Whether `model` accepts some listed document under the relation: no constraint is removable, so the
only candidate explanation is the empty set, found exactly when nothing is accepted. -/
private def inhabited (model : Json) (docs : List Json) (strict : Bool) : Bool :=
  explanations model [] docs strict == some []

/-- `FForbidden-GoalA.json`, the model `FForbidden.json` plus the goal rule `GoalA`, and each single removal of a
removable constraint agree with the Kernel on every row. -/
example :
    (agreed (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/FForbidden-GoalA.json") (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/request-FForbidden-GoalA.json")
      (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/artifact-FForbidden-GoalA.json")).isSome ∧
    parsed (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/FForbidden.json") ==
      (parsed (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/FForbidden-GoalA.json")).map (remove · (.rule "GoalA")) ∧
    (agreed (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/FForbidden-GoalA-without-rule-AForbidden.json") (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/request-FForbidden-GoalA-without-rule-AForbidden.json")
      (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/artifact-FForbidden-GoalA-without-rule-AForbidden.json")).isSome ∧
    parsed (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/FForbidden-GoalA-without-rule-AForbidden.json") ==
      (parsed (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/FForbidden-GoalA.json")).map (remove · (.rule "AForbidden")) ∧
    (agreed (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/FForbidden-GoalA-without-rule-CTrue.json") (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/request-FForbidden-GoalA-without-rule-CTrue.json")
      (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/artifact-FForbidden-GoalA-without-rule-CTrue.json")).isSome ∧
    parsed (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/FForbidden-GoalA-without-rule-CTrue.json") ==
      (parsed (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/FForbidden-GoalA.json")).map (remove · (.rule "CTrue")) := by native_decide

/-- `FForbidden-GoalC.json`, the model `FForbidden.json` plus the goal rule `GoalC`, and each single removal of a
removable constraint agree with the Kernel on every row. -/
example :
    (agreed (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/FForbidden-GoalC.json") (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/request-FForbidden-GoalC.json")
      (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/artifact-FForbidden-GoalC.json")).isSome ∧
    parsed (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/FForbidden.json") ==
      (parsed (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/FForbidden-GoalC.json")).map (remove · (.rule "GoalC")) ∧
    (agreed (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/FForbidden-GoalC-without-rule-AForbidden.json") (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/request-FForbidden-GoalC-without-rule-AForbidden.json")
      (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/artifact-FForbidden-GoalC-without-rule-AForbidden.json")).isSome ∧
    parsed (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/FForbidden-GoalC-without-rule-AForbidden.json") ==
      (parsed (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/FForbidden-GoalC.json")).map (remove · (.rule "AForbidden")) ∧
    (agreed (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/FForbidden-GoalC-without-rule-CTrue.json") (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/request-FForbidden-GoalC-without-rule-CTrue.json")
      (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/artifact-FForbidden-GoalC-without-rule-CTrue.json")).isSome ∧
    parsed (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/FForbidden-GoalC-without-rule-CTrue.json") ==
      (parsed (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/FForbidden-GoalC.json")).map (remove · (.rule "CTrue")) := by native_decide

/-- `FForbidden.json` itself agrees with the Kernel on every row. -/
example :
    (agreed (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/FForbidden.json") (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/request-FForbidden.json")
      (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/artifact-FForbidden.json")).isSome := by native_decide

/-- `FRequired-GoalA.json`, the model `FRequired.json` plus the goal rule `GoalA`, and each single removal of a
removable constraint agree with the Kernel on every row. -/
example :
    (agreed (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/FRequired-GoalA.json") (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/request-FRequired-GoalA.json")
      (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/artifact-FRequired-GoalA.json")).isSome ∧
    parsed (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/FRequired.json") ==
      (parsed (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/FRequired-GoalA.json")).map (remove · (.rule "GoalA")) ∧
    (agreed (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/FRequired-GoalA-without-required-B.json") (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/request-FRequired-GoalA-without-required-B.json")
      (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/artifact-FRequired-GoalA-without-required-B.json")).isSome ∧
    parsed (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/FRequired-GoalA-without-required-B.json") ==
      (parsed (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/FRequired-GoalA.json")).map (remove · (.required "B")) ∧
    (agreed (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/FRequired-GoalA-without-rule-ABTrue.json") (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/request-FRequired-GoalA-without-rule-ABTrue.json")
      (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/artifact-FRequired-GoalA-without-rule-ABTrue.json")).isSome ∧
    parsed (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/FRequired-GoalA-without-rule-ABTrue.json") ==
      (parsed (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/FRequired-GoalA.json")).map (remove · (.rule "ABTrue")) ∧
    (agreed (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/FRequired-GoalA-without-rule-ABFalse.json") (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/request-FRequired-GoalA-without-rule-ABFalse.json")
      (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/artifact-FRequired-GoalA-without-rule-ABFalse.json")).isSome ∧
    parsed (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/FRequired-GoalA-without-rule-ABFalse.json") ==
      (parsed (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/FRequired-GoalA.json")).map (remove · (.rule "ABFalse")) := by native_decide

/-- `FRequired.json` itself agrees with the Kernel on every row. -/
example :
    (agreed (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/FRequired.json") (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/request-FRequired.json")
      (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/artifact-FRequired.json")).isSome := by native_decide

/-- `FRowBound-GoalX.json`, the model `FRowBound.json` plus the goal rule `GoalX`, and each single removal of a
removable constraint agree with the Kernel on every row. -/
example :
    (agreed (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/FRowBound-GoalX.json") (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/request-FRowBound-GoalX.json")
      (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/artifact-FRowBound-GoalX.json")).isSome ∧
    parsed (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/FRowBound.json") ==
      (parsed (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/FRowBound-GoalX.json")).map (remove · (.rule "GoalX")) ∧
    (agreed (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/FRowBound-GoalX-without-rule-XLow.json") (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/request-FRowBound-GoalX-without-rule-XLow.json")
      (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/artifact-FRowBound-GoalX-without-rule-XLow.json")).isSome ∧
    parsed (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/FRowBound-GoalX-without-rule-XLow.json") ==
      (parsed (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/FRowBound-GoalX.json")).map (remove · (.rule "XLow")) ∧
    (agreed (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/FRowBound-GoalX-without-bound-X-maxValue.json") (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/request-FRowBound-GoalX-without-bound-X-maxValue.json")
      (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/artifact-FRowBound-GoalX-without-bound-X-maxValue.json")).isSome ∧
    parsed (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/FRowBound-GoalX-without-bound-X-maxValue.json") ==
      (parsed (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/FRowBound-GoalX.json")).map (remove · (.bound "X" "maxValue")) ∧
    (agreed (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/FRowBound-GoalX-without-bound-X-minValue.json") (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/request-FRowBound-GoalX-without-bound-X-minValue.json")
      (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/artifact-FRowBound-GoalX-without-bound-X-minValue.json")).isSome ∧
    parsed (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/FRowBound-GoalX-without-bound-X-minValue.json") ==
      (parsed (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/FRowBound-GoalX.json")).map (remove · (.bound "X" "minValue")) := by native_decide

/-- `FRowBound-GoalY.json`, the model `FRowBound.json` plus the goal rule `GoalY`, and each single removal of a
removable constraint agree with the Kernel on every row. -/
example :
    (agreed (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/FRowBound-GoalY.json") (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/request-FRowBound-GoalY.json")
      (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/artifact-FRowBound-GoalY.json")).isSome ∧
    parsed (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/FRowBound.json") ==
      (parsed (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/FRowBound-GoalY.json")).map (remove · (.rule "GoalY")) ∧
    (agreed (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/FRowBound-GoalY-without-rule-XLow.json") (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/request-FRowBound-GoalY-without-rule-XLow.json")
      (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/artifact-FRowBound-GoalY-without-rule-XLow.json")).isSome ∧
    parsed (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/FRowBound-GoalY-without-rule-XLow.json") ==
      (parsed (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/FRowBound-GoalY.json")).map (remove · (.rule "XLow")) ∧
    (agreed (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/FRowBound-GoalY-without-bound-X-maxValue.json") (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/request-FRowBound-GoalY-without-bound-X-maxValue.json")
      (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/artifact-FRowBound-GoalY-without-bound-X-maxValue.json")).isSome ∧
    parsed (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/FRowBound-GoalY-without-bound-X-maxValue.json") ==
      (parsed (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/FRowBound-GoalY.json")).map (remove · (.bound "X" "maxValue")) ∧
    (agreed (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/FRowBound-GoalY-without-bound-X-minValue.json") (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/request-FRowBound-GoalY-without-bound-X-minValue.json")
      (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/artifact-FRowBound-GoalY-without-bound-X-minValue.json")).isSome ∧
    parsed (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/FRowBound-GoalY-without-bound-X-minValue.json") ==
      (parsed (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/FRowBound-GoalY.json")).map (remove · (.bound "X" "minValue")) := by native_decide

/-- `FRowBound.json` itself agrees with the Kernel on every row. -/
example :
    (agreed (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/FRowBound.json") (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/request-FRowBound.json")
      (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/artifact-FRowBound.json")).isSome := by native_decide

/-- A field a rule forbids in an inhabited model: `A` can never be filled and the forbidding rule alone
explains it, while `C`, whose rule only forbids `True`, is filled by `False`. Asking the model without
the goal rule answers neither, since the model is inhabited. -/
example : [true, false].all (fun strict =>
    inhabited (full (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/FForbidden.json"))
      (documents (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/request-FForbidden.json")) strict &&
    explanations (full (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/FForbidden-GoalA.json")) [.rule "AForbidden", .rule "CTrue"]
      (documents (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/request-FForbidden-GoalA.json")) strict == some [[.rule "AForbidden"]] &&
    inhabited (full (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/FForbidden-GoalC.json"))
      (documents (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/request-FForbidden-GoalC.json")) strict) = true := by native_decide

/-- Filling `A` makes both rules on `B` bite, and only `B`'s required role keeps `B` from staying empty. -/
example : [true, false].all (fun strict =>
    inhabited (full (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/FRequired.json"))
      (documents (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/request-FRequired.json")) strict &&
    explanations (full (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/FRequired-GoalA.json")) [.required "B", .rule "ABTrue", .rule "ABFalse"]
      (documents (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/request-FRequired-GoalA.json")) strict ==
    some [[.required "B", .rule "ABTrue", .rule "ABFalse"]]) = true := by native_decide

/-- A row field: every in-range `X` fires `XLow`, so `X` can never be filled and `minValue` is no member,
while its sibling `Y` is filled in a row. A row without `X` is accepted (the fourth listed document, an
empty row), so asking whether a row can exist instead of whether `X` can be filled answers wrongly. -/
example : [true, false].all (fun strict =>
    inhabited (full (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/FRowBound.json"))
      (documents (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/request-FRowBound.json")) strict &&
    explanations (full (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/FRowBound-GoalX.json"))
      [.rule "XLow", .bound "X" "maxValue", .bound "X" "minValue"]
      (documents (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/request-FRowBound-GoalX.json")) strict ==
    some [[.rule "XLow", .bound "X" "maxValue"]] &&
    inhabited (full (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/FRowBound-GoalY.json"))
      (documents (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/request-FRowBound-GoalY.json")) strict) = true := by native_decide

/-- The Kernel accepts the empty row of `FRowBound.json` under both relations. -/
example : ((agreed (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/FRowBound.json") (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/request-FRowBound.json")
    (include_str "../../../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/artifact-FRowBound.json")).bind (·[3]?)) == some (true, true) := by native_decide

end A12Kernel.Dm.FillabilityControlLocks
