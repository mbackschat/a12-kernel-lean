import A12Kernel.Reference.Dm.ParallelValidation
import A12Kernel.Reference.Dm.GeneratedComputationRule
import A12Kernel.Elaboration.ValidationMessageDiagnostic

/-! # A message beside a parallel join: the index fields are members, and a row token needs a proved row

The first two sections hold Kernel 31.1.1 rows on a shop whose `Ordered` and `Received` lines are both keyed by their String `Sku`, every
rule reporting on `Ordered/Qty` and reading a `Received` field unstarred to join the two (a12-dmkits
`CheckerParallelJoinMessageAgreementTest` at `c7afca597`, KF675;
[inbound record](../../../docs/sources/inbound-handbacks.md#src-inbound-2026-11-05c)). Each row is one model with
one message parameter, read by the DM reader from declarations hand-built as the peer's.

What the rows separate: a join's index fields are members although the condition names neither, for a
computation's generated rule as for a rule, while a starred read joins nothing; and a joined level's row token
`$#…$` is admitted only where the condition proves that level's row, one AND arm or every OR arm carrying the
proof, `AllGroupsFilled` over the two joined groups admitting both tokens.

The last section holds rows on an order whose `Lines` and `Picks` are both keyed by `LineNo`, a rule reporting
on `Lines/Sku`: a key expression's read joins its level without proving its row (a12-dmkits
`CheckerKeyReadMarkingAgreementTest` at `74e77a325`;
[inbound record](../../../docs/sources/inbound-handbacks.md#src-inbound-2026-11-05e)).
-/

namespace A12Kernel.Dm.ParallelJoinMessageLocks

open Lean A12Kernel

private def field (group name : String) (fieldType : Json) (root := "Shop") : Json :=
  Json.mkObj [("type", "Field"), ("id", .str s!"/{root}/{group}/{name}"), ("name", .str name),
    ("Field", Json.mkObj [("fieldType", fieldType)])]

private def number : Json :=
  Json.mkObj [("type", "NumberType"), ("NumberType", Json.mkObj [("maxFractionalDigits", toJson 0)])]

private def string : Json := Json.mkObj [("type", "StringType")]

private def message (parameter : String) : Json :=
  Json.arr #[Json.mkObj [("locale", "en_US"), ("text", .str s!"Check {parameter}.")]]

/-- The rule `JoinMessage` reporting on `Ordered/Qty` under `condition`, declared in `/Shop` or `/Shop/Ordered`. -/
private def rule (condition parameter : String) (inOrdered : Bool) : Json :=
  let parent := if inOrdered then "/Shop/Ordered" else "/Shop"
  Json.mkObj [("type", "Rule"), ("id", .str s!"{parent}/JoinMessage"), ("name", "JoinMessage"), ("Rule", Json.mkObj [
    ("errorEntityRelPath", .str (if inOrdered then "../Qty" else "../Ordered/Qty")), ("errorCode", "JOIN"),
    ("severity", "ERROR"), ("errorCondition", .str condition), ("errorMessage", message parameter)])]

/-- The computation `GapComputation` of `Ordered/Gap` by `operation`, declared in `/Shop`. -/
private def computation (operation parameter : String) : Json :=
  Json.mkObj [("type", "Computation"), ("id", "/Shop/GapComputation"), ("name", "GapComputation"),
    ("Computation", Json.mkObj [("computedFieldRelPath", "../Ordered/Gap"),
      ("computationAlternatives", Json.arr #[Json.mkObj [("operation", .str operation)]]),
      ("errorMessage", message parameter)])]

private def side (name : String) (extra : List Json) : Json :=
  Json.mkObj [("type", "Group"), ("id", .str s!"/Shop/{name}"), ("name", .str name), ("Group", Json.mkObj [
    ("repeatability", toJson 3), ("indexFieldName", "Sku"), ("elements", Json.arr (#[
      field name "Sku" string, field name "Qty" number] ++ extra.toArray ++ #[field name "Note" string]))])]

/-- The shop with `Ordered` and `Received` both keyed by their String `Sku`, `ordered` and `shop` holding the
elements declared in `Ordered` and in `Shop`. -/
private def shop (ordered shop : List Json) : Json :=
  Json.mkObj [
    ("header", Json.mkObj [("id", "Shop_DM"), ("modelType", "document"), ("modelVersion", "29.4.0"),
      ("locales", Json.arr #[Json.mkObj [("code", "en_US")]])]),
    ("content", Json.mkObj [("modelInfo", Json.mkObj [("name", "Shop")]),
      ("modelConfig", Json.mkObj [("timeZone", "UTC"), ("conditionLanguage", Json.mkObj [("code", "en_US")])]),
      ("modelRoot", Json.mkObj [("rootGroups", Json.arr #[Json.mkObj [("type", "Group"), ("id", "/Shop"),
        ("name", "Shop"), ("Group", Json.mkObj [("elements", Json.arr (#[
          side "Ordered" ([field "Ordered" "Gap" number] ++ ordered), side "Received" []] ++ shop.toArray))])]])])])]

/-- The named class of the message of a checked rule, `none` when admitted. -/
private def messageClass (dm : DmModel) (rule : DmRule) : Option String :=
  match checkValidationRule dm .english rule with
  | .error refusal => some s!"rule: {refusal.kernelClass?.getD "unclassed"}"
  | .ok checked =>
      let condition : ValidationMessageCondition dm.flat := match checked with
        | .ordinary checked => .rule checked
        | .parallel checked => .parallel checked rule.group
      match elaborateValidationMessageTemplate dm.flat .english condition (rule.messages.headD ("", "")).2 with
      | .ok _ => none
      | .error error => some ((error.namedRuleDiagnostic?.map (·.kernelCode)).getD "unclassed")

/-- The message class of the one rule `model` declares. -/
private def classOf (model : Json) : Option String :=
  match readModel model with
  | .error error => some s!"no model: {error}"
  | .ok dm => match dm.rules with
    | [rule] => messageClass dm rule
    | _ => some "not one rule"

/-- The message class of the rule under `condition`, declared in `Shop` unless `inOrdered`. -/
private def ruleClass (condition parameter : String) (inOrdered := false) : Option String :=
  let definition := rule condition parameter inOrdered
  classOf (if inOrdered then shop [definition] [] else shop [] [definition])

/-- The message class of the rule the computation by `operation` generates. -/
private def computationClass (operation parameter : String) : Option String :=
  match readModel (shop [] [computation operation parameter]) with
  | .error error => some s!"no model: {error}"
  | .ok dm => match dm.computations with
    | [computation] => match computation.generatedRule? .english with
      | some rule => messageClass dm { rule with messages := computation.messages }
      | none => some "no generated rule"
    | _ => some "not one computation"

private def orderedRow := "$#/Shop/Ordered$"
private def receivedRow := "$#/Shop/Received$"
private def notCollectively := "FieldsNotCollectivelyFilled(Ordered/Qty, Received/Qty)"

/-- The join's index fields are members although the condition names neither, for a computation's generated
rule too; a rule joining nothing, a starred read and an unread payload field leave the parameter no member. -/
example :
    ruleClass notCollectively "$/Shop/Ordered/Sku.value$" = none ∧
    ruleClass notCollectively "$/Shop/Received/Sku.value$" = none ∧
    ruleClass notCollectively "$/Shop/Ordered/Sku$" = none ∧
    ruleClass "FieldFilled(Ordered/Qty) And FieldFilled(Received/Qty)" "$/Shop/Ordered/Sku.value$" = none ∧
    ruleClass "FieldsNotCollectivelyFilled(Qty, ../Received/Qty)" "$/Shop/Received/Sku.value$"
      (inOrdered := true) = none ∧
    computationClass "[Ordered/Qty] - [Received/Qty]" "$/Shop/Received/Sku.value$" = none ∧
    ruleClass "FieldFilled(Ordered/Qty)" "$/Shop/Ordered/Sku.value$" = some "INVALID_FIELD" ∧
    computationClass "[Ordered/Qty] + 1" "$/Shop/Ordered/Sku.value$" = some "INVALID_FIELD" ∧
    ruleClass "FieldFilled(Ordered/Qty) And AtLeastOneFieldFilled(Received*/Qty)" "$/Shop/Received/Sku.value$" =
      some "INVALID_FIELD" ∧
    ruleClass notCollectively "$/Shop/Received/Note.value$" = some "INVALID_FIELD" := by
  native_decide

private def refused := some "INVALID_USE_OF_ITERATION_PARAM"

/-- Each condition with the two tokens' classes, `$#/Shop/Ordered$` first. -/
private def tokenRows : List (String × Option String × Option String) := [
  (notCollectively, refused, refused),
  ("FieldFilled(Ordered/Qty) And FieldFilled(Received/Qty)", none, none),
  ("FieldFilled(Ordered/Qty) Or FieldFilled(Received/Qty)", refused, refused),
  ("AllFieldsFilled(Ordered/Qty, Received/Qty)", none, none),
  ("AtLeastOneFieldFilled(Ordered/Qty, Received/Qty)", refused, refused),
  ("AtLeastOneFieldFilled(Ordered/Qty, Ordered/Note) And FieldFilled(Received/Qty)", none, none),
  ("MoreThanOneFieldFilled(Ordered/Qty, Ordered/Note) And FieldFilled(Received/Qty)", none, none),
  ("[Ordered/Qty] > [Received/Qty]", refused, refused),
  ("FieldNotFilled(Ordered/Qty) And FieldFilled(Received/Qty)", refused, none),
  ("GroupFilled(Ordered) And FieldFilled(Received/Qty)", none, none),
  ("AllGroupsFilled(Ordered, Received)", none, none)]

/-- A joined level's row token needs the condition to prove its row: a positive presence inside the level, the
all-filled quantifier with one operand there, or the two other counting quantifiers with every operand there,
in one AND arm or in every OR arm. A rule declared in a joined group is gated alike; a rule joining nothing is
not. -/
example :
    tokenRows.all (fun (condition, ordered, received) =>
      ruleClass condition orderedRow == ordered && ruleClass condition receivedRow == received) ∧
    ruleClass "FieldsNotCollectivelyFilled(Qty, ../Received/Qty)" orderedRow (inOrdered := true) = refused ∧
    ruleClass "FieldsNotCollectivelyFilled(Qty, ../Received/Qty)" receivedRow (inOrdered := true) = refused ∧
    ruleClass "FieldFilled(Ordered/Qty)" orderedRow = none := by
  native_decide

/-! ## A key expression's read joins its level -/

private def orderGroup (name index : String) (members : List String) (repeatability : Nat) : Json :=
  Json.mkObj [("type", "Group"), ("id", .str s!"/Order/{name}"), ("name", .str name), ("Group", Json.mkObj [
    ("repeatability", toJson repeatability), ("indexFieldName", .str index),
    ("elements", Json.arr ((index :: members).map (field name · string (root := "Order"))).toArray)])]

private def orderClass (condition parameter : String) (picksIndex := "LineNo") : Option String :=
  let definition := Json.mkObj [("type", "Rule"), ("id", "/Order/KeyRead"), ("name", "KeyRead"), ("Rule", Json.mkObj [
    ("errorEntityRelPath", "../Lines/Sku"), ("errorCode", "KEY"), ("severity", "ERROR"),
    ("errorCondition", .str condition), ("errorMessage", message parameter)])]
  let model := Json.mkObj [
    ("header", Json.mkObj [("id", "Order_DM"), ("modelType", "document"), ("modelVersion", "29.4.0"),
      ("locales", Json.arr #[Json.mkObj [("code", "en_US")]])]),
    ("content", Json.mkObj [("modelInfo", Json.mkObj [("name", "Order")]),
      ("modelConfig", Json.mkObj [("timeZone", "UTC"), ("conditionLanguage", Json.mkObj [("code", "en_US")])]),
      ("modelRoot", Json.mkObj [("rootGroups", Json.arr #[Json.mkObj [("type", "Group"), ("id", "/Order"),
        ("name", "Order"), ("Group", Json.mkObj [("elements", Json.arr #[
          orderGroup "Lines" "LineNo" ["Sku"] 5, orderGroup "Picks" picksIndex ["Ref"] 5,
          orderGroup "Gifts" "GiftNo" ["Note"] 2, definition])])]])])])]
  classOf model

private def keyedJoin (index : String) := s!"FieldFilled(Lines/Sku) And FieldFilled(Gifts/Note For Picks/{index})"
private def unkeyedJoin := "FieldFilled(Lines/Sku) And FieldFilled(Picks/Ref)"

/-- The key `Picks/LineNo` joins `Lines` and `Picks` as the unkeyed control does: `Lines/LineNo` is a member,
which a reading in which the key marks nothing would refuse; `Picks/LineNo` is one already as the key's own
read. The key proves no pick row, its keyed operand selecting `Gifts` outside `Picks`, so the picks' row token
is refused where the control admits it. With `Picks` keyed by a differently named index field the rule check
refuses each condition with the join's index-name class before any parameter is read. The peer locks the six
`LineNo` rows at `74e77a325`; the `Code` rows are its unlocked probe's. The last two rows are Lean's own
controls on this carrier, not measured on it: a field the condition does not read is no member, and without the
join neither is `Lines/LineNo`, as the shop's measured `FieldFilled(Ordered/Qty)` row is. -/
example :
    ["$/Order/Lines/LineNo.value$", "$/Order/Picks/LineNo.value$", "$#/Order/Picks$"].map
        (orderClass (keyedJoin "LineNo")) = [none, none, refused] ∧
    ["$/Order/Lines/LineNo.value$", "$/Order/Picks/LineNo.value$", "$#/Order/Picks$"].map
        (orderClass unkeyedJoin) = [none, none, none] ∧
    ([keyedJoin "Code", unkeyedJoin].all fun condition =>
      ["$/Order/Lines/LineNo.value$", "$/Order/Picks/Code.value$", "$#/Order/Picks$"].all fun parameter =>
        orderClass condition parameter (picksIndex := "Code") == some "rule: MVK_ERROR_FIELD_INVALID_INDEX") ∧
    orderClass (keyedJoin "LineNo") "$/Order/Picks/Ref.value$" = some "INVALID_FIELD" ∧
    orderClass "FieldFilled(Lines/Sku)" "$/Order/Lines/LineNo.value$" = some "INVALID_FIELD" := by
  native_decide

end A12Kernel.Dm.ParallelJoinMessageLocks
