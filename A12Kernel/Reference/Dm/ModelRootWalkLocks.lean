import A12Kernel.Reference.Dm.ParallelValidation
import A12Kernel.Reference.Dm.Document
import A12Kernel.Elaboration.ValidationMessageRendering

/-! # A relative walk turns on the model root

Kernel 31.3.1 lets a relative path's up-run land on the technical model root and continue from it into any
root group, as the absolute path its remaining segments spell; a walk that stops on the model root or climbs
past it draws the parent-depth class, each up-step judged as it is taken, so a star on a step answers
before the path's end (a12-dmkits KF679, `CrossRootGroupReferenceLawsTest`, `PathSegmentWalkLawsTest`,
`CrossRootGroupReferenceDiffTest`, `MessageGroupWalkAgreementTest` and
`MessageGroupParentBoundaryAgreementTest` at `505683610`;
[inbound record](../../../docs/sources/inbound-handbacks.md#src-inbound-2026-11-07)). Kernel 31.1.1 refused
every walk reaching the model root. The rows below are the letter's §2 rows on its carrier: root groups
`Order` (with repeatable `Lines`), `Customer` and repeatable `Voucher`, plus `Library/Loans/Shelf/Bin` for
the group-message grid.
-/

namespace A12Kernel.Dm.ModelRootWalkLocks

open Lean A12Kernel

private def string : Json := Json.mkObj [("type", "StringType")]
private def number : Json := Json.mkObj [("type", "NumberType"), ("NumberType", Json.mkObj [("maxFractionalDigits", toJson 0)])]

private def field (parent name : String) (type : Json := string) : Json :=
  Json.mkObj [("type", "Field"), ("id", .str s!"{parent}/{name}"), ("name", .str name), ("Field", Json.mkObj [("fieldType", type)])]

private def group (parent name : String) (elements : List Json) (repeatability : Option Nat := none) : Json :=
  Json.mkObj [("type", "Group"), ("id", .str s!"{parent}/{name}"), ("name", .str name), ("Group", Json.mkObj (
    (repeatability.map fun count => [("repeatability", toJson count)]).getD [] ++
    [("elements", Json.arr elements.toArray)]))]

private def message : Json := Json.arr #[Json.mkObj [("locale", "en_US"), ("text", "x")]]

/-- A computation in `Order` computing `5` into `target`. -/
private def computation (target : String) : Json :=
  Json.mkObj [("type", "Computation"), ("id", "/Order/Copy"), ("name", "Copy"), ("Computation", Json.mkObj [
    ("computedFieldRelPath", .str target), ("computationAlternatives", Json.arr #[Json.mkObj [("operation", "5")]]),
    ("errorMessage", message)])]

private def walkModel (orderExtra : List Json := []) : Json :=
  Json.mkObj [
    ("header", Json.mkObj [("id", "W_DM"), ("modelType", "document"), ("modelVersion", "29.8.0"),
      ("locales", Json.arr #[Json.mkObj [("code", "en_US")]])]),
    ("content", Json.mkObj [("modelInfo", Json.mkObj [("name", "W")]),
      ("modelConfig", Json.mkObj [("timeZone", "UTC"), ("conditionLanguage", Json.mkObj [("code", "en_US")])]),
      ("modelRoot", Json.mkObj [("rootGroups", Json.arr #[
        group "" "Order" ([field "/Order" "Code", group "/Order" "Lines" [field "/Order/Lines" "Qty" number] (some 5)] ++
          orderExtra),
        group "" "Customer" [field "/Customer" "Name", field "/Customer" "Tier"],
        group "" "Voucher" [field "/Voucher" "Value" number] (some 3),
        group "" "Library" [field "/Library" "Title", group "/Library" "Loans" [field "/Library/Loans" "Due",
          group "/Library/Loans" "Shelf" [field "/Library/Loans/Shelf" "Row",
            group "/Library/Loans/Shelf" "Bin" [field "/Library/Loans/Shelf/Bin" "Slot"]]]]])])])]

private def dm? : Option DmModel := (readModel (walkModel)).toOption

private def rule (group : List String) (errorPath condition : String) : DmRule :=
  { group, name := "R", severity := "ERROR", errorCode := "R", condition, errorEntityRelPath := errorPath }

/-- The rule's admission: `none` when admitted, else its classes. -/
private def ruleClass (group : List String) (errorPath condition : String) : Option String :=
  match dm? with
  | none => some "no model"
  | some dm =>
      match checkValidationRule dm .english (rule group errorPath condition) with
      | .ok _ => none
      | .error refusal => some (" ".intercalate refusal.kernelClasses)

/-- A rule in `Order` reporting on the condition's own field, so only the path answers. -/
private def inOrder (path : String) (predicate := "FieldFilled") : Option String :=
  ruleClass ["Order"] "../Code" s!"{predicate}(Code) And {predicate}({path})"

private def inLines (path : String) : Option String :=
  ruleClass ["Order", "Lines"] "../Qty" s!"FieldFilled(Qty) And FieldFilled({path})"

private def groupInOrder (path : String) : Option String :=
  ruleClass ["Order"] "../Code" s!"FieldFilled(Code) And GroupFilled({path})"

/-- The named class of a message on a rule in `group` reporting on `errorPath` under `condition`. -/
private def messageClass (group : List String) (errorPath condition text : String) : Option String := do
  let dm ← dm?
  let .ordinary checked ← (checkValidationRule dm .english (rule group errorPath condition)).toOption
    | some "rule refused"
  match elaborateValidationMessageTemplate dm.flat .english (.rule checked) text with
  | .ok _ => none
  | .error error => some ((error.namedRuleDiagnostic?.map (·.kernelCode)).getD "unclassed")

private def orderMessage (text : String) : Option String :=
  messageClass ["Order"] "../../Customer/Name" "FieldFilled(../Customer/Name)" text

private def groupMessage (group : List String) (field text : String) : Option String :=
  messageClass group s!"../{field}" s!"FieldFilled({field})" text

/-- Whether the reader keeps a computation targeting `target`, and its refusals. -/
private def targetRead (target : String) : Option (Bool × List String) :=
  (readModel (walkModel [computation target])).toOption.map fun dm =>
    (!dm.computations.isEmpty, dm.refusals.map (·.2))

/-! ## Conditions -/

/-- A sibling root group, the rule's own root re-entered, and a climb from below both admit. -/
example : inOrder "../Customer/Name" = none ∧ inOrder "../Order/Code" = none ∧
    groupInOrder "../Customer" = none ∧ inLines "../../Customer/Name" = none := by native_decide

/-- From the model root the path is judged as its absolute spelling: an undeclared root, a missing entity
and an unstarred or starred repeatable root draw what `/Nope/Name`, `/Customer/Nope`, `/Voucher/Value` and
`/Voucher*/Value` draw. -/
example : inOrder "../Nope/Name" = some "MVK_INVALID_ROOT_GROUP" ∧
    groupInOrder "../Nope" = some "MVK_INVALID_ROOT_GROUP" ∧
    inOrder "../Customer/Nope" = some "MVK_INVALID_ENTITY" ∧
    inOrder "../Voucher/Value" = some "MVK_NO_WILDCARD" ∧
    inOrder "../Voucher*/Value" = some "MVK_NO_WILDCARDS_ALLOWED" := by native_decide

/-- Stopping on the model root, or climbing past it, keeps the parent-depth class. -/
example : groupInOrder ".." = some "MVK_TOO_MANY_PARENT_GROUPS" ∧
    groupInOrder "../.." = some "MVK_TOO_MANY_PARENT_GROUPS" ∧
    inOrder "../../Customer/Name" = some "MVK_TOO_MANY_PARENT_GROUPS" ∧
    inLines "../../../Customer/Name" = some "MVK_TOO_MANY_PARENT_GROUPS" := by native_decide

/-- A star on an up-step answers as the step is taken: onto the model root it is the star's class, and on
a step past it the depth class. -/
example : groupInOrder "../..*" = some "MVK_TOO_MANY_PARENT_GROUPS" ∧
    groupInOrder "..*" = some "MVK_INVALID_WILDCARD_REL" ∧
    inOrder "..*/Customer/Name" = some "MVK_INVALID_WILDCARD_REL" ∧
    groupInOrder "..*/.." = some "MVK_INVALID_WILDCARD_REL" := by native_decide

/-- The re-measured 31.1.1 rows that moved (KF284, KF356): a walk onto the model root whose next segment
names no root draws the root class. -/
example : inLines "../../Code" = some "MVK_INVALID_ROOT_GROUP" ∧
    inOrder "../Code" = some "MVK_INVALID_ROOT_GROUP" := by native_decide

/-! ## Error and computed targets -/

/-- An error target climbing through the model root names the sibling root's field, and one naming nothing
draws the declaration gate's pair. -/
example : ruleClass ["Order"] "../../Customer/Name" "FieldFilled(../Customer/Name)" = none ∧
    ruleClass ["Order"] "../../Nope/Name" "FieldFilled(Code)" =
      some "MVK_ERROR_FIELD_MISSING MVK_MISSING_ERROR_FIELD" := by native_decide

/-- A computed target through the model root is kept; one naming nothing draws the codeless not-found
sentence; one climbing past the model root leaves no model. -/
example : targetRead "../../Customer/Name" = some (true, []) ∧
    targetRead "../../Nope/Name" = some (false, ["codeless:computed-field-not-found"]) ∧
    targetRead "../../../Customer/Name" = none := by native_decide

/-! ## Messages -/

example : orderMessage "x $../Customer/Name$" = none ∧ orderMessage "x $../Customer/Name.value$" = none ∧
    orderMessage "x $../Nope/Name$" = some "INVALID_ROOT_GROUP" ∧
    orderMessage "x $..$" = some "ERROR_TEXT_PARAMETER_TOO_MANY_PARENT_GROUPS" ∧
    orderMessage "x $../..$" = some "ERROR_TEXT_PARAMETER_TOO_MANY_PARENT_GROUPS" ∧
    orderMessage "x $../Code$" = some "INVALID_ROOT_GROUP" := by native_decide

/-- A group argument continuing from the model root keeps the group class for a name that is no root
(KF214 moved); one continuing into a root admits; a run reaching the model root exactly, counting the step
a continuing token adds, lets the token answer, and one step more keeps the depth class. -/
example : groupMessage ["Library"] "Title" "x $#../Loans$" = some "INVALID_GROUP" ∧
    groupMessage ["Library", "Loans"] "Due" "x $#../../Library$" = none ∧
    groupMessage ["Library", "Loans", "Shelf"] "Row" "x $#../../$" = some "MVK_EXPECTED_TOKEN_NOT_FOUND" ∧
    groupMessage ["Library", "Loans", "Shelf"] "Row" "x $#../..//$" = some "MVK_UNEXPECTED_TOKEN" ∧
    groupMessage ["Library", "Loans", "Shelf"] "Row" "x $#../../-x$" = some "MVK_UNEXPECTED_TOKEN" ∧
    groupMessage ["Library", "Loans", "Shelf"] "Row" "x $#../../($" = some "MVK_UNEXPECTED_TOKEN" ∧
    groupMessage ["Library", "Loans", "Shelf", "Bin"] "Slot" "x $#../../../RuleGroup$" =
      some "MVK_UNEXPECTED_TOKEN" ∧
    groupMessage ["Library"] "Title" "x $#../$" = some "MVK_INCOMPLETE_INPUT" ∧
    groupMessage ["Library", "Loans", "Shelf"] "Row" "x $#../../../$" =
      some "ERROR_TEXT_PARAMETER_TOO_MANY_PARENT_GROUPS" := by native_decide

/-! ## Runtime -/

private def world : World := { now := { epochMillis := 0 } }

/-- The pointers a rule in `Order/Lines` firing on a gold customer reports, over two lines. -/
private def goldLines (tier : String) : Option (List String) := do
  let dm ← dm?
  let checked ← (checkRule dm .english (rule ["Order", "Lines"] "../Qty"
    "FieldFilled(Qty) And [../../Customer/Tier] == \"gold\"")).toOption
  let input ← (readDocument dm (Json.mkObj [
    ("Order", Json.mkObj [("Lines", Json.arr #[Json.mkObj [("Qty", "1")], Json.mkObj [("Qty", "2")]])]),
    ("Customer", Json.mkObj [("Tier", .str tier)])])).toOption
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler dm.flat).toOption
  let document ← (checkDocument prepared "en_US" input.data).toOption
  pure ((← (runRule world document checked).toOption).map fun message => (observe dm.flat message).pointer)

/-- A cross-root read fires once per line for a gold customer and stays silent otherwise. -/
example : goldLines "gold" = some ["Order/Lines/Qty", "Order/Lines[2]/Qty"] ∧
    goldLines "silver" = some [] := by native_decide

end A12Kernel.Dm.ModelRootWalkLocks
