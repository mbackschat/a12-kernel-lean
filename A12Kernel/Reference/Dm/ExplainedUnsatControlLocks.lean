import Lean.Data.Json
import A12Kernel.Reference.Dm.SampleAcceptanceCapture

/-! # The explained-UNSAT controls (Q2-P9) against retained Kernel rows

[Q2-P9](../../../docs/PLAN.md#q2-preparation-checklist) explains a model no document is accepted by as an
irreducible set of removable constraints: authored rules, absolute-required roles and declared bounds. The
model keeping only the set's constraints accepts no document, and dropping any one member lets one through.
Removing a constraint writes the model without it: the rule element, the field's `requirednessConfig` or
the bound member left out.

The [captures](../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/MANIFEST.sha256) hold
four controls, each in full and without each of its removable constraints, every model over every cell
state of its fields: two Boolean fields' five states each and a missing root, or a Number's absent, empty
and malformed states, a fraction, its declared range and values outside it. Every verdict depends only on
those cells. A Boolean's states are all listed. For the Number, a subset found UNSAT keeps the rule,
`maxValue` and the required role, under which every value up to 5 fires the rule and every other draws a
formal finding (spec/04 §4.8), while a subset lacking one of them is SAT on a listed document; so the
answers locked here hold beyond the listed values. Each model's rows agree with the Kernel's on both
strategies, the reduced models are this module's own removals of the full one, and every subset of a
control's constraints is then judged from the full model by Lean alone. -/

namespace A12Kernel.Dm.ExplainedUnsatControlLocks

open Lean SampleAcceptanceCapture

/-- A removable constraint of a model, named as the model names it. -/
inductive Constraint where
  | rule (name : String)
  | required (field : String)
  | bound (field member : String)
  deriving DecidableEq, Repr

private def withoutKey (json : Json) (key : String) : Json := match json with
  | .obj members => .obj (members.erase key)
  | other => other

private def modify (json : Json) (key : String) (change : Json → Json) : Json :=
  match json.getObjVal? key with
  | .ok value => json.setObjVal! key (change value)
  | .error _ => json

/-- Rewrite the elements of the model's first root group, where every control declares everything. -/
private def mapElements (change : Array Json → Array Json) (model : Json) : Json :=
  modify model "content" fun content => modify content "modelRoot" fun root => modify root "rootGroups" fun
    | .arr groups => .arr (groups.modify 0 fun group => modify group "Group" fun body => modify body "elements" fun
        | .arr elements => .arr (change elements)
        | other => other)
    | other => other

private def named (element : Json) (kind name : String) : Bool :=
  (element.getObjValAs? String "type").toOption == some kind &&
    (element.getObjValAs? String "name").toOption == some name

/-- Apply `change` to the root group's elements and, recursively, to every nested group's, so a control
may declare a field inside a repeatable group. -/
private partial def deep (change : Array Json → Array Json) (elements : Array Json) : Array Json :=
  (change elements).map fun element =>
    if (element.getObjValAs? String "type").toOption == some "Group" then
      modify element "Group" fun body => modify body "elements" fun
        | .arr inner => .arr (deep change inner)
        | other => other
    else element

/-- The model without one constraint, which every control names uniquely. -/
def remove (model : Json) : Constraint → Json
  | .rule name => mapElements (deep (·.filter fun element => !named element "Rule" name)) model
  | .required field => mapElements (deep (·.map fun element =>
      if named element "Field" field then modify element "Field" (withoutKey · "requirednessConfig") else element)) model
  | .bound field member => mapElements (deep (·.map fun element =>
      if named element "Field" field then
        modify element "Field" fun body => modify body "fieldType" fun type =>
          match type.getObjValAs? String "type" with
          | .ok kind => modify type kind (withoutKey · member)
          | .error _ => type
      else element)) model

/-- The model keeping, of the removable constraints `all`, only `kept`. -/
def keeping (model : Json) (all kept : List Constraint) : Json :=
  (all.filter (!kept.contains ·)).foldl remove model

private def world : World := { now := { epochMillis := 0 } }

/-- Whether some document is accepted, message-free when `strict` and error-free otherwise; `none` when the
model is not read or a document is not decided. -/
private def satisfiable (model : Json) (documents : List Json) (strict : Bool) : Option Bool := do
  let dm ← (readModel model).toOption
  let accepted ← documents.mapM (sampleAcceptance world dm)
  pure (accepted.any fun acceptance => if strict then acceptance.messageFree else acceptance.errorFree)

private def subsets : List α → List (List α)
  | [] => [[]]
  | head :: tail => (subsets tail).map (head :: ·) ++ subsets tail

/-- Every irreducible conflicting subset of `all`: kept alone it accepts no document, and without any one
member it accepts one. -/
def explanations (model : Json) (all : List Constraint) (documents : List Json) (strict : Bool) :
    Option (List (List Constraint)) := do
  let verdicts ← (subsets all).mapM fun kept => do pure (kept, ← satisfiable (keeping model all kept) documents strict)
  let satisfied := fun kept => (verdicts.lookup kept).getD false
  pure (verdicts.filterMap fun (kept, sat) =>
    if !sat && kept.all (fun member => satisfied (kept.erase member)) then some kept else none)

private def parsed (text : String) : Option Json := (parseModelJson text).toOption

private def xUnrelatedAll : List Constraint := [.rule "ANone", .rule "ATrue", .rule "AFalse", .rule "BTrue"]

private def xDisjointAll : List Constraint := [.rule "ANone", .rule "ATrue", .rule "AFalse", .rule "BNone", .rule "BTrue", .rule "BFalse"]

private def xRequiredAll : List Constraint := [.required "A", .rule "ATrue", .rule "AFalse"]

private def xBoundAll : List Constraint := [.rule "NLow", .bound "N" "maxValue", .bound "N" "minValue", .required "N"]

/-- `XUnrelated.json` and each single removal agree with the Kernel on every row, and each retained
reduced model is this module's removal from the full one. -/
example :
    (agreed (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/XUnrelated.json") (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/request-XUnrelated.json")
      (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/artifact-XUnrelated.json")).isSome ∧
    (agreed (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/XUnrelated-without-rule-ANone.json") (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/request-XUnrelated-without-rule-ANone.json")
      (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/artifact-XUnrelated-without-rule-ANone.json")).isSome ∧
    parsed (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/XUnrelated-without-rule-ANone.json") == (parsed (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/XUnrelated.json")).map (remove · (.rule "ANone")) ∧
    (agreed (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/XUnrelated-without-rule-ATrue.json") (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/request-XUnrelated-without-rule-ATrue.json")
      (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/artifact-XUnrelated-without-rule-ATrue.json")).isSome ∧
    parsed (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/XUnrelated-without-rule-ATrue.json") == (parsed (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/XUnrelated.json")).map (remove · (.rule "ATrue")) ∧
    (agreed (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/XUnrelated-without-rule-AFalse.json") (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/request-XUnrelated-without-rule-AFalse.json")
      (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/artifact-XUnrelated-without-rule-AFalse.json")).isSome ∧
    parsed (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/XUnrelated-without-rule-AFalse.json") == (parsed (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/XUnrelated.json")).map (remove · (.rule "AFalse")) ∧
    (agreed (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/XUnrelated-without-rule-BTrue.json") (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/request-XUnrelated-without-rule-BTrue.json")
      (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/artifact-XUnrelated-without-rule-BTrue.json")).isSome ∧
    parsed (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/XUnrelated-without-rule-BTrue.json") == (parsed (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/XUnrelated.json")).map (remove · (.rule "BTrue")) := by native_decide

/-- `XDisjoint.json` and each single removal agree with the Kernel on every row, and each retained
reduced model is this module's removal from the full one. -/
example :
    (agreed (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/XDisjoint.json") (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/request-XDisjoint.json")
      (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/artifact-XDisjoint.json")).isSome ∧
    (agreed (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/XDisjoint-without-rule-ANone.json") (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/request-XDisjoint-without-rule-ANone.json")
      (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/artifact-XDisjoint-without-rule-ANone.json")).isSome ∧
    parsed (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/XDisjoint-without-rule-ANone.json") == (parsed (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/XDisjoint.json")).map (remove · (.rule "ANone")) ∧
    (agreed (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/XDisjoint-without-rule-ATrue.json") (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/request-XDisjoint-without-rule-ATrue.json")
      (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/artifact-XDisjoint-without-rule-ATrue.json")).isSome ∧
    parsed (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/XDisjoint-without-rule-ATrue.json") == (parsed (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/XDisjoint.json")).map (remove · (.rule "ATrue")) ∧
    (agreed (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/XDisjoint-without-rule-AFalse.json") (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/request-XDisjoint-without-rule-AFalse.json")
      (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/artifact-XDisjoint-without-rule-AFalse.json")).isSome ∧
    parsed (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/XDisjoint-without-rule-AFalse.json") == (parsed (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/XDisjoint.json")).map (remove · (.rule "AFalse")) ∧
    (agreed (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/XDisjoint-without-rule-BNone.json") (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/request-XDisjoint-without-rule-BNone.json")
      (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/artifact-XDisjoint-without-rule-BNone.json")).isSome ∧
    parsed (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/XDisjoint-without-rule-BNone.json") == (parsed (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/XDisjoint.json")).map (remove · (.rule "BNone")) ∧
    (agreed (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/XDisjoint-without-rule-BTrue.json") (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/request-XDisjoint-without-rule-BTrue.json")
      (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/artifact-XDisjoint-without-rule-BTrue.json")).isSome ∧
    parsed (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/XDisjoint-without-rule-BTrue.json") == (parsed (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/XDisjoint.json")).map (remove · (.rule "BTrue")) ∧
    (agreed (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/XDisjoint-without-rule-BFalse.json") (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/request-XDisjoint-without-rule-BFalse.json")
      (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/artifact-XDisjoint-without-rule-BFalse.json")).isSome ∧
    parsed (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/XDisjoint-without-rule-BFalse.json") == (parsed (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/XDisjoint.json")).map (remove · (.rule "BFalse")) := by native_decide

/-- `XRequired.json` and each single removal agree with the Kernel on every row, and each retained
reduced model is this module's removal from the full one. -/
example :
    (agreed (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/XRequired.json") (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/request-XRequired.json")
      (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/artifact-XRequired.json")).isSome ∧
    (agreed (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/XRequired-without-required-A.json") (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/request-XRequired-without-required-A.json")
      (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/artifact-XRequired-without-required-A.json")).isSome ∧
    parsed (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/XRequired-without-required-A.json") == (parsed (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/XRequired.json")).map (remove · (.required "A")) ∧
    (agreed (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/XRequired-without-rule-ATrue.json") (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/request-XRequired-without-rule-ATrue.json")
      (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/artifact-XRequired-without-rule-ATrue.json")).isSome ∧
    parsed (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/XRequired-without-rule-ATrue.json") == (parsed (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/XRequired.json")).map (remove · (.rule "ATrue")) ∧
    (agreed (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/XRequired-without-rule-AFalse.json") (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/request-XRequired-without-rule-AFalse.json")
      (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/artifact-XRequired-without-rule-AFalse.json")).isSome ∧
    parsed (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/XRequired-without-rule-AFalse.json") == (parsed (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/XRequired.json")).map (remove · (.rule "AFalse")) := by native_decide

/-- `XBound.json` and each single removal agree with the Kernel on every row, and each retained
reduced model is this module's removal from the full one. -/
example :
    (agreed (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/XBound.json") (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/request-XBound.json")
      (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/artifact-XBound.json")).isSome ∧
    (agreed (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/XBound-without-rule-NLow.json") (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/request-XBound-without-rule-NLow.json")
      (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/artifact-XBound-without-rule-NLow.json")).isSome ∧
    parsed (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/XBound-without-rule-NLow.json") == (parsed (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/XBound.json")).map (remove · (.rule "NLow")) ∧
    (agreed (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/XBound-without-bound-N-maxValue.json") (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/request-XBound-without-bound-N-maxValue.json")
      (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/artifact-XBound-without-bound-N-maxValue.json")).isSome ∧
    parsed (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/XBound-without-bound-N-maxValue.json") == (parsed (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/XBound.json")).map (remove · (.bound "N" "maxValue")) ∧
    (agreed (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/XBound-without-bound-N-minValue.json") (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/request-XBound-without-bound-N-minValue.json")
      (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/artifact-XBound-without-bound-N-minValue.json")).isSome ∧
    parsed (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/XBound-without-bound-N-minValue.json") == (parsed (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/XBound.json")).map (remove · (.bound "N" "minValue")) ∧
    (agreed (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/XBound-without-required-N.json") (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/request-XBound-without-required-N.json")
      (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/artifact-XBound-without-required-N.json")).isSome ∧
    parsed (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/XBound-without-required-N.json") == (parsed (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/XBound.json")).map (remove · (.required "N")) := by native_decide

private def documents (requestText : String) : List Json := (requestDocuments requestText).getD []

private def full (modelText : String) : Json := (parsed modelText).getD .null

/-- A conflict beside an unrelated rule: the three `A` rules are the only explanation, so the set adding
`BTrue` is no explanation, since the model keeping only the `A` rules still accepts nothing. -/
example : [true, false].all (fun strict =>
    explanations (full (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/XUnrelated.json")) xUnrelatedAll
      (documents (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/request-XUnrelated.json")) strict ==
    some [[.rule "ANone", .rule "ATrue", .rule "AFalse"]]) = true := by native_decide

/-- Two disjoint conflicts: each trio is an explanation and no other set is, so neither is the conflict. -/
example : [true, false].all (fun strict =>
    explanations (full (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/XDisjoint.json")) xDisjointAll
      (documents (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/request-XDisjoint.json")) strict ==
    some [[.rule "ANone", .rule "ATrue", .rule "AFalse"], [.rule "BNone", .rule "BTrue", .rule "BFalse"]]) = true := by
  native_decide

/-- A conflict that needs a required field: the two rules alone accept an empty `A`. -/
example : [true, false].all (fun strict =>
    explanations (full (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/XRequired.json")) xRequiredAll
      (documents (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/request-XRequired.json")) strict ==
    some [[.required "A", .rule "ATrue", .rule "AFalse"]]) = true := by native_decide

/-- A conflict that needs a bound: without `maxValue` the value 10 is accepted, without the required role an
empty `N`, and `minValue` belongs to no explanation. -/
example : [true, false].all (fun strict =>
    explanations (full (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/XBound.json")) xBoundAll
      (documents (include_str "../../../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/request-XBound.json")) strict ==
    some [[.rule "NLow", .bound "N" "maxValue", .required "N"]]) = true := by native_decide

end A12Kernel.Dm.ExplainedUnsatControlLocks
