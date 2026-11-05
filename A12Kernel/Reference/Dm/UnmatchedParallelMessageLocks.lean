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

private def side (name : String) : Json :=
  Json.mkObj [("type", "Group"), ("id", .str s!"/Form/{name}"), ("name", .str name), ("Group", Json.mkObj [
    ("repeatability", toJson 3), ("indexFieldName", "Dept"), ("elements", Json.arr #[
      field s!"{name}/" "Dept" string, field s!"{name}/" "Head" (number 0),
      field s!"{name}/" "Rate" (number 2), field s!"{name}/" "Note" string, field s!"{name}/" "Kind" kind])])]

/-- `FieldsNotCollectivelyFilled` over one field of each side, or the condition given, reported on the
`Demand` field. -/
private def rule (code fieldName text : String) (condition : Option String := none) : Json :=
  Json.mkObj [("type", "Rule"), ("id", .str s!"/Form/{code}"), ("name", .str code), ("Rule", Json.mkObj [
    ("errorEntityRelPath", .str s!"../Demand/{fieldName}"), ("errorCode", .str code), ("severity", "ERROR"),
    ("errorCondition", .str (condition.getD s!"FieldsNotCollectivelyFilled(Demand/{fieldName}, Supply/{fieldName})")),
    ("errorMessage", Json.arr #[Json.mkObj [("locale", "en_US"), ("text", .str text)]])])]

private def modelJson (rules : List Json) : Json :=
  Json.mkObj [
    ("header", Json.mkObj [("id", "P31_DM"), ("modelType", "document"), ("modelVersion", "29.4.0"),
      ("locales", Json.arr #[Json.mkObj [("code", "en_US")]])]),
    ("content", Json.mkObj [("modelInfo", Json.mkObj [("name", "P31_DM")]),
      ("modelConfig", Json.mkObj [("timeZone", "UTC"), ("conditionLanguage", Json.mkObj [("code", "en_US")])]),
      ("modelRoot", Json.mkObj [("rootGroups", Json.arr #[Json.mkObj [
        ("type", "Group"), ("id", "/Form"), ("name", "Form"), ("Group", Json.mkObj [
          ("repeatability", toJson 1),
          ("elements", Json.arr (#[field "" "Plan" string, side "Demand", side "Supply"] ++ rules.toArray))])]])])])]

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

end A12Kernel.Dm.UnmatchedParallelMessageLocks
