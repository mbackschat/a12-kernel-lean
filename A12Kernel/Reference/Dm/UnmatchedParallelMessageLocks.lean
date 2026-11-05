import A12Kernel.Reference.Dm.ParallelValidation
import A12Kernel.Reference.Dm.Document
import A12Kernel.Elaboration.ValidationMessageRendering
import A12Kernel.Reference.Dm.Replay

/-! # Reader-to-render locks for a message read of an unmatched parallel side

The [unmatched-side capture](../../../evidence/kernel-31.1.1/captures/unmatched-parallel-message-2026-11-05/)
joins `Demand` and `Supply` on their index field `Dept`: `Eng` has no `Supply` row and `Ops` no `Demand` row.
Each rule below is read by the DM reader from declarations hand-built as the capture's, run on its document and
its template rendered at every firing's environment; the texts are the capture's own, identical under both
Kernel strategies ([checkpoint](../../../docs/sources/message-parameter-rendering-probes.md#src-unmatched-parallel-side)).

Display text is caller-supplied, so `inputs` reads each cell's stored text, with the format's default for an
absent one: `0` for the scale-0 `Head`, `0.00` for `Rate`, the empty text otherwise. What the locks separate
is the absent row: a wrong account reading the unmatched level's first row renders the other side's first
row, `d=[3] s=[5]` where the capture renders `d=[3] s=[0]`.
-/

namespace A12Kernel.Dm.UnmatchedParallelMessageLocks

open Lean A12Kernel

private def field (group name : String) (fieldType : Json) : Json :=
  Json.mkObj [("type", "Field"), ("id", .str s!"/Form/{group}{name}"), ("name", .str name),
    ("Field", Json.mkObj [("fieldType", fieldType)])]

private def number (digits : Nat) : Json :=
  Json.mkObj [("type", "NumberType"), ("NumberType", Json.mkObj
    [("maxFractionalDigits", toJson digits), ("minFractionalDigits", toJson digits)])]

private def string : Json := Json.mkObj [("type", "StringType"), ("StringType", Json.mkObj [])]

private def kind : Json :=
  Json.mkObj [("type", "EnumerationType"), ("EnumerationType", Json.mkObj [
    ("values", Json.arr #[Json.mkObj [("value", "A")], Json.mkObj [("value", "B")]]),
    ("categories", Json.arr #[Json.mkObj [("name", "Band"), ("values", Json.arr #["Hi", "Lo"])]])])]

/-- A joined side, `extra` appended to its elements. -/
private def side (name : String) (extra : List Json := []) : Json :=
  Json.mkObj [("type", "Group"), ("id", .str s!"/Form/{name}"), ("name", .str name), ("Group", Json.mkObj [
    ("repeatability", toJson 3), ("indexFieldName", "Dept"), ("elements", Json.arr (#[
      field s!"{name}/" "Dept" string, field s!"{name}/" "Head" (number 0),
      field s!"{name}/" "Rate" (number 2), field s!"{name}/" "Note" string, field s!"{name}/" "Kind" kind] ++
      extra.toArray))])]

/-- `FieldsNotCollectivelyFilled` over one field of each side, or the condition given, reported on the
`Demand` field. -/
private def rule (code fieldName text : String) (condition : Option String := none) : Json :=
  Json.mkObj [("type", "Rule"), ("id", .str s!"/Form/{code}"), ("name", .str code), ("Rule", Json.mkObj [
    ("errorEntityRelPath", .str s!"../Demand/{fieldName}"), ("errorCode", .str code), ("severity", "ERROR"),
    ("errorCondition", .str (condition.getD s!"FieldsNotCollectivelyFilled(Demand/{fieldName}, Supply/{fieldName})")),
    ("errorMessage", Json.arr #[Json.mkObj [("locale", "en_US"), ("text", .str text)]])])]

/-- The capture's model with `rules`, its `Demand` holding `demandExtra` too. -/
private def modelJson (rules : List Json) (demandExtra : List Json := []) : Json :=
  Json.mkObj [
    ("header", Json.mkObj [("id", "P31_DM"), ("modelType", "document"), ("modelVersion", "29.4.0"),
      ("locales", Json.arr #[Json.mkObj [("code", "en_US")]])]),
    ("content", Json.mkObj [("modelInfo", Json.mkObj [("name", "P31_DM")]),
      ("modelConfig", Json.mkObj [("timeZone", "UTC"), ("conditionLanguage", Json.mkObj [("code", "en_US")])]),
      ("modelRoot", Json.mkObj [("rootGroups", Json.arr #[Json.mkObj [
        ("type", "Group"), ("id", "/Form"), ("name", "Form"), ("Group", Json.mkObj [
          ("repeatability", toJson 1),
          ("elements", Json.arr (#[field "" "Plan" string, side "Demand" demandExtra, side "Supply"] ++ rules.toArray))])]])])])]

private def row (dept head rate note kind : String) : Json :=
  Json.mkObj [("Dept", .str dept), ("Head", .str head), ("Rate", .str rate), ("Note", .str note), ("Kind", .str kind)]

/-- The capture's `unmatched-both` document, or with `Eng` written twice in `Supply` in place of `Ops`. -/
private def documentJson (duplicate : Bool := false) : Json :=
  Json.mkObj [("Form", Json.mkObj [("Plan", "Q3"),
    ("Demand", Json.arr #[row "Sales" "5" "1.50" "dn1" "A", row "Eng" "3" "2.25" "dn2" "B"]),
    ("Supply", Json.arr (if duplicate then
      #[row "Sales" "5" "1.50" "sn1" "B", row "Eng" "7" "1.00" "sn2" "A", row "Eng" "8" "1.00" "sn3" "A"]
      else #[row "Sales" "5" "1.50" "sn1" "B", row "Ops" "2" "4.00" "sn2" "A"]))])]

private def world : World := { now := { epochMillis := 0 } }

/-- Every firing's rendered text of the model's one rule, in evaluation order, or `none` when the reader,
the checker or the template refuses it. -/
private def rendered (definition : Json) (duplicate : Bool := false) : Option (List String) := do
  let dm ← (readModel (modelJson [definition])).toOption
  let model := dm.flat
  let [rule] := dm.rules | none
  let input ← (readDocument dm (documentJson duplicate)).toOption
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  let preliminary ← checked.applyFullIndexPreliminary.toOption
  let references ← preliminary.messageReferenceInputs.toOption
  let document := input.data.toDocument
  let defaultOf (cell : CellAddr) : String :=
    match (model.fields.find? (·.id == cell.field)).map (·.name) with
    | some "Head" => "0"
    | some "Rate" => "0.00"
    | _ => ""
  let inputs : ValidationMessageInputs := {
    fieldName := fun id => {
      providerResult := none, modelLabel := none
      debugDisplay := ((model.fields.find? (·.id == id)).map (·.name)).getD "" }
    fieldValue := fun cell => { displayValue := document.rawCells cell, defaultDisplay := defaultOf cell }
    fieldStoredToken := document.rawCells
    formPointer := fun _ => "" }
  let .parallel parallelRule ← (checkValidationRule dm .english rule).toOption | none
  let template ← (elaborateValidationMessageTemplate model .english
    (.parallel parallelRule rule.group) (rule.messages.headD ("", "")).2).toOption
  let rows ← (parallelRule.evalDocument preliminary preliminary.messageCacheContext.toOption).toOption
  (rows.filter (·.outcome.message?.isSome)).mapM fun fired =>
    let context := fired.row.messageContext document prepared "en_US" (some references)
    (template.toRenderPlanAt context inputs).toOption.map (·.render.text)

/-- A value read of the unmatched side renders its format's default, as a missing value does, beside the
matched side's own value. -/
example :
    rendered (rule "pv" "Head" "d=[$/Form/Demand/Head.value$] s=[$/Form/Supply/Head.value$]") =
      some ["d=[3] s=[0]", "d=[0] s=[2]"] ∧
    rendered (rule "pr" "Rate" "d=[$/Form/Demand/Rate.value$] s=[$/Form/Supply/Rate.value$]") =
      some ["d=[2.25] s=[0.00]", "d=[0.00] s=[4.00]"] ∧
    rendered (rule "pn" "Note" "d=[$/Form/Demand/Note.value$] s=[$/Form/Supply/Note.value$]") =
      some ["d=[dn2] s=[]", "d=[] s=[sn2]"] := by native_decide

/-- The index field the join reads is a member although the condition text never names it, and its
unmatched value renders empty; a name needs no row. An Enumeration's value and category of the unmatched
side render empty. -/
example :
    rendered (rule "pg" "Head"
        "ns=[$/Form/Supply/Head$] nd=[$/Form/Demand/Head$] kd=[$/Form/Demand/Dept.value$] ks=[$/Form/Supply/Dept.value$]") =
      some ["ns=[Head] nd=[Head] kd=[Eng] ks=[]", "ns=[Head] nd=[Head] kd=[] ks=[Ops]"] ∧
    rendered (rule "pk" "Kind"
        "vd=[$/Form/Demand/Kind.value$] vs=[$/Form/Supply/Kind.value$] cd=[$/Form/Demand/Kind->Band$] cs=[$/Form/Supply/Kind->Band$]") =
      some ["vd=[B] vs=[] cd=[Lo] cs=[]", "vd=[] vs=[A] cd=[] cs=[Hi]"] := by native_decide

/-- A side whose key two rows carry is not absent: its reads keep the unbound level's first row, a choice of
this account that no row measures, separated here from the unmatched side's absent cell. -/
example :
    rendered (rule "pd" "Head" "d=[$/Form/Demand/Head.value$] s=[$/Form/Supply/Head.value$]"
        (some "FieldFilled(Demand/Head) Or FieldFilled(Supply/Head)")) (duplicate := true) =
      some ["d=[3] s=[5]", "d=[5] s=[5]"] := by native_decide

/-- The template refusal of the model's one parallel rule, `none` when its template is admitted. -/
private def templateRefusal (definition : Json) : Option ValidationMessageTemplateError := do
  let dm ← (readModel (modelJson [definition])).toOption
  let [rule] := dm.rules | none
  let .parallel parallelRule ← (checkValidationRule dm .english rule).toOption | none
  match elaborateValidationMessageTemplate dm.flat .english (.parallel parallelRule rule.group)
      (rule.messages.headD ("", "")).2 with
  | .ok _ => none
  | .error error => some error

/-- A field of either side the condition does not read is refused as no member, as the capture's twin of `pg`
is on both sides; the index field beside it is admitted. -/
example :
    (templateRefusal (rule "pg" "Head" "vd=[$/Form/Demand/Kind.value$]")).map
        (·.namedRuleDiagnostic?) = some (some .messageFieldNotReferenced) ∧
    (templateRefusal (rule "pg" "Head" "vs=[$/Form/Supply/Kind.value$]")).map
        (·.namedRuleDiagnostic?) = some (some .messageFieldNotReferenced) ∧
    templateRefusal (rule "pg" "Head" "kd=[$/Form/Demand/Dept.value$] ks=[$/Form/Supply/Dept.value$]") = none := by
  native_decide

/-- Either joined group's row token is refused beside `FieldsNotCollectivelyFilled`, as the capture's twin of
`pg` is on both sides, so no unmatched firing renders a token its level has no row for. The admitted twin beside
a positive presence on each side is the peer's row on its own carrier
([KF675 lock](ParallelJoinMessageLocks.lean)), restated here on the capture's model. -/
example :
    ["$#/Form/Demand$", "$#/Form/Supply$"].all (fun token =>
      (templateRefusal (rule "pg" "Head" token)).map (·.namedRuleDiagnostic?) ==
          some (some .invalidUseOfIterationParam) &&
        (templateRefusal (rule "pg" "Head" token (some "FieldFilled(Demand/Head) And FieldFilled(Supply/Head)"))).isNone) :=
  by native_decide


/-! ## The joined-row proof's residual rows -/

/-- A nonrepeatable group `Demand/{name}` holding one String `member`. -/
private def subGroup (name member : String) : Json :=
  Json.mkObj [("type", "Group"), ("id", .str s!"/Form/Demand/{name}"), ("name", .str name), ("Group", Json.mkObj [
    ("elements", Json.arr #[field s!"Demand/{name}/" member string])])]

/-- The measured carrier: the capture's model with a nonrepeatable `Demand/Detail` holding a String `Memo`,
and for the peer's group-list row a second one, `Demand/Pack` holding `Label`. -/
private def demandSubGroups : List Json := [subGroup "Detail" "Memo", subGroup "Pack" "Label"]

/-- The class of a rule reporting on `Demand/Head` under `condition` with the message `Check {token}.`, declared
in `/Form`, or in `/Form/Demand` when `inDemand`; `none` when admitted. -/
private def tokenClass (condition token : String) (inDemand : Bool) : Option String :=
  let parent := if inDemand then "/Form/Demand" else "/Form"
  let definition := Json.mkObj [("type", "Rule"), ("id", .str s!"{parent}/R"), ("name", "R"), ("Rule", Json.mkObj [
    ("errorEntityRelPath", .str (if inDemand then "../Head" else "../Demand/Head")), ("errorCode", "R"),
    ("severity", "ERROR"), ("errorCondition", .str condition),
    ("errorMessage", Json.arr #[Json.mkObj [("locale", "en_US"), ("text", .str s!"Check {token}.")]])])]
  let demandExtra := if inDemand then demandSubGroups ++ [definition] else demandSubGroups
  match readModel (modelJson (if inDemand then [] else [definition]) demandExtra) with
  | .error _ => some "no model"
  | .ok dm => match dm.rules with
    | [rule] => match checkValidationRule dm .english rule with
      | .error _ => some "rule refused"
      | .ok checked =>
          let condition : ValidationMessageCondition dm.flat := match checked with
            | .ordinary checked => .rule checked
            | .parallel checked => .parallel checked rule.group
          match elaborateValidationMessageTemplate dm.flat .english condition (rule.messages.headD ("", "")).2 with
          | .ok _ => none
          | .error error => some ((error.namedRuleDiagnostic?.map (·.kernelCode)).getD "unclassed")
    | _ => some "not one rule"

private def r12 := "FieldNotFilled(Demand/Head) And AtLeastOneGroupFilled(Demand/Detail, Demand/Pack) And FieldFilled(Supply/Head)"

/-- Each row of the [residual capture](../../../evidence/kernel-31.1.1/captures/joined-row-proof-2026-11-05/):
its id, condition, token, whether the rule sits in `Demand`, and the Kernel's class, `none` when admitted. -/
private def residualRows : List (String × String × String × Bool × Option String) := [
  ("c01td", "MoreThanOneFieldFilled(Demand/Head, Supply/Head)", "$#/Form/Demand$", false, some "INVALID_USE_OF_ITERATION_PARAM"),
  ("c01ts", "MoreThanOneFieldFilled(Demand/Head, Supply/Head)", "$#/Form/Supply$", false, some "INVALID_USE_OF_ITERATION_PARAM"),
  ("c02td", "AllFieldsFilled(Demand/Head, Demand/Note, Supply/Head)", "$#/Form/Demand$", false, none),
  ("c02ts", "AllFieldsFilled(Demand/Head, Demand/Note, Supply/Head)", "$#/Form/Supply$", false, none),
  ("c03td", "AtLeastOneFieldFilled(Demand/Head, Demand/Note, Demand/Rate) And FieldFilled(Supply/Head)", "$#/Form/Demand$", false, none),
  ("c03ts", "AtLeastOneFieldFilled(Demand/Head, Demand/Note, Demand/Rate) And FieldFilled(Supply/Head)", "$#/Form/Supply$", false, none),
  ("c04td", "MoreThanOneFieldFilled(Demand/Head, Demand/Note, Supply/Head)", "$#/Form/Demand$", false, some "INVALID_USE_OF_ITERATION_PARAM"),
  ("c04ts", "MoreThanOneFieldFilled(Demand/Head, Demand/Note, Supply/Head)", "$#/Form/Supply$", false, some "INVALID_USE_OF_ITERATION_PARAM"),
  ("c05td", "[Demand/Head] > 0 And [Supply/Head] > 0", "$#/Form/Demand$", false, some "INVALID_USE_OF_ITERATION_PARAM"),
  ("c05ts", "[Demand/Head] > 0 And [Supply/Head] > 0", "$#/Form/Supply$", false, some "INVALID_USE_OF_ITERATION_PARAM"),
  ("c06td", "GroupNotFilled(Demand) And FieldFilled(Supply/Head)", "$#/Form/Demand$", false, some "INVALID_USE_OF_ITERATION_PARAM"),
  ("c06ts", "GroupNotFilled(Demand) And FieldFilled(Supply/Head)", "$#/Form/Supply$", false, none),
  ("c07td", "(FieldFilled(Demand/Head) And FieldFilled(Supply/Head)) Or AllFieldsFilled(Demand/Head, Supply/Head)", "$#/Form/Demand$", false, none),
  ("c07ts", "(FieldFilled(Demand/Head) And FieldFilled(Supply/Head)) Or AllFieldsFilled(Demand/Head, Supply/Head)", "$#/Form/Supply$", false, none),
  ("c08td", "FieldNotFilled(Demand/Head) And FieldFilled(Demand/Detail/Memo) And FieldFilled(Supply/Head)", "$#/Form/Demand$", false, none),
  ("c08ts", "FieldNotFilled(Demand/Head) And FieldFilled(Demand/Detail/Memo) And FieldFilled(Supply/Head)", "$#/Form/Supply$", false, none),
  ("c09td", "FieldNotFilled(Demand/Head) And AtLeastOneFieldFilled(Demand*/Note) And FieldFilled(Supply/Head)", "$#/Form/Demand$", false, some "INVALID_USE_OF_ITERATION_PARAM"),
  ("c09ts", "FieldNotFilled(Demand/Head) And AtLeastOneFieldFilled(Demand*/Note) And FieldFilled(Supply/Head)", "$#/Form/Supply$", false, none),
  ("c10td", "AtLeastOneGroupFilled(Demand, Supply)", "$#/Form/Demand$", false, some "INVALID_USE_OF_ITERATION_PARAM"),
  ("c10ts", "AtLeastOneGroupFilled(Demand, Supply)", "$#/Form/Supply$", false, some "INVALID_USE_OF_ITERATION_PARAM"),
  ("c11td", "FieldsNotCollectivelyFilled(Demand/Head, Supply/Head)", "$#/Form/Demand$", false, some "INVALID_USE_OF_ITERATION_PARAM"),
  ("c11ts", "FieldsNotCollectivelyFilled(Demand/Head, Supply/Head)", "$#/Form/Supply$", false, some "INVALID_USE_OF_ITERATION_PARAM"),
  ("c12td", "FieldFilled(Demand/Head) And FieldFilled(Supply/Head)", "$#/Form/Demand$", false, none),
  ("c12ts", "FieldFilled(Demand/Head) And FieldFilled(Supply/Head)", "$#/Form/Supply$", false, none),
  ("c13td", "AllGroupsFilled(Demand, Supply)", "$#/Form/Demand$", false, none),
  ("c13ts", "AllGroupsFilled(Demand, Supply)", "$#/Form/Supply$", false, none),
  ("c11rd", "FieldsNotCollectivelyFilled(Demand/Head, Supply/Head)", "$#Demand$", false, some "INVALID_USE_OF_ITERATION_PARAM"),
  ("c11rs", "FieldsNotCollectivelyFilled(Demand/Head, Supply/Head)", "$#Supply$", false, some "INVALID_USE_OF_ITERATION_PARAM"),
  ("c12rd", "FieldFilled(Demand/Head) And FieldFilled(Supply/Head)", "$#Demand$", false, none),
  ("c12rs", "FieldFilled(Demand/Head) And FieldFilled(Supply/Head)", "$#Supply$", false, none),
  ("g11rg", "FieldsNotCollectivelyFilled(Head, ../Supply/Head)", "$#RuleGroup$", true, some "INVALID_USE_OF_ITERATION_PARAM"),
  ("g11td", "FieldsNotCollectivelyFilled(Head, ../Supply/Head)", "$#/Form/Demand$", true, some "INVALID_USE_OF_ITERATION_PARAM"),
  ("g11ts", "FieldsNotCollectivelyFilled(Head, ../Supply/Head)", "$#/Form/Supply$", true, some "INVALID_USE_OF_ITERATION_PARAM"),
  ("g12rg", "FieldFilled(Head) And FieldFilled(../Supply/Head)", "$#RuleGroup$", true, none),
  ("g12td", "FieldFilled(Head) And FieldFilled(../Supply/Head)", "$#/Form/Demand$", true, none),
  ("g12ts", "FieldFilled(Head) And FieldFilled(../Supply/Head)", "$#/Form/Supply$", true, none),
  ("k1ka", "AtLeastOneFieldFilled(Demand/Head For \"a\", Demand/Note For \"a\")", "$#Demand For \"a\"$", false, none),
  ("k2ka", "MoreThanOneFieldFilled(Demand/Head For \"a\", Demand/Note For \"a\")", "$#Demand For \"a\"$", false, none),
  ("k3ka", "AllFieldsFilled(Demand/Head For \"a\", Demand/Note For \"a\")", "$#Demand For \"a\"$", false, none),
  ("k4ka", "FieldNotFilled(Demand/Head For \"a\")", "$#Demand For \"a\"$", false, some "INVALID_USE_OF_SEMANTIC_INDEX"),
  -- Peer row R12, measured on its shop carrier ([Letter I](../../../docs/sources/inbound-handbacks.md#src-inbound-2026-11-05d)).
  ("r12td", r12, "$#/Form/Demand$", false, none),
  ("r12ts", r12, "$#/Form/Supply$", false, none),
  -- Two peer rows of the KF546 correction (Letter I §4), re-expressed on this carrier: the keyed
  -- `FieldNotFilled`, which guards nothing (`k4ka`), stands in for the peer's unkeyed conjunct so that no conjunct
  -- iterates `Demand`, and the outside operand is the root field `Plan`, outside `Demand` as the peer's is outside
  -- `Bins`. That stand-in is an assumption; the peer's outside-operand group-list row has no counterpart here.
  ("k5ka", "FieldNotFilled(Demand/Head For \"a\") And AtLeastOneGroupFilled(Demand/Detail For \"a\", Demand/Pack For \"a\")", "$#Demand For \"a\"$", false, none),
  ("k7ka", "FieldNotFilled(Demand/Head For \"a\") And AtLeastOneFieldFilled(Demand/Head For \"a\", Plan)", "$#Demand For \"a\"$", false, some "INVALID_USE_OF_SEMANTIC_INDEX")]

/-- The rule check's class for `condition` on the measured carrier, `none` when admitted. -/
private def ruleClass (condition : String) : Option String :=
  match readModel (modelJson [rule "R" "Head" "x" (some condition)] demandSubGroups) with
  | .error _ => some "no model"
  | .ok dm => match dm.rules with
    | [rule] => match checkValidationRule dm .english rule with
      | .ok _ => none
      | .error refusal => some (refusal.kernelClass?.getD "unclassed")
    | _ => some "not one rule"

/-- Every residual row agrees with the Kernel: three-operand calls across both sides or inside one prove as
two-operand ones do, a deeper presence proves, a literal comparison, a mixed `MoreThanOneFieldFilled`,
`GroupNotFilled` and a starred operand do not, an `Or` whose every arm proves admits, the relative and
`$#RuleGroup$` spellings are gated alike, `AllGroupsFilled` and `AtLeastOneGroupFilled` over the joined groups
are admitted as the conjunction and disjunction of their presences, as are the peer's `AtLeastOneGroupFilled` over
two groups inside one joined group (`r12`), and a keyed token beside `AtLeastOneFieldFilled`,
`MoreThanOneFieldFilled`, `AllFieldsFilled` or `AtLeastOneGroupFilled` over operands under its own key is
admitted, a field outside the keyed group refusing it (`k1`-`k3`, `k5`, `k7`). A negative three-operand
quantifier across the join guards no iteration, as the rule check measured on row `n3x`. -/
example :
    (residualRows.filter fun (_, condition, token, inDemand, kernel) =>
      tokenClass condition token inDemand != kernel).map (·.1) = [] ∧
    ruleClass "NoFieldFilled(Demand/Head, Demand/Note, Supply/Head)" = some "MVK_PARALLEL_ITERATION_INVALID" := by
  native_decide

end A12Kernel.Dm.UnmatchedParallelMessageLocks
