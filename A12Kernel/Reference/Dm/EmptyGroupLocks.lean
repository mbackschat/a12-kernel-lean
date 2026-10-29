import Lean.Data.Json
import A12Kernel.Reference.Dm.Validate
import A12Kernel.Elaboration.ValidationMessageDiagnostic
import A12Kernel.Reference.Dm.EntryFrameFixture

/-! # Declared groups without a field

The Kernel admits a nonrepeatable group whose subtree holds no field, and refuses every operand that
names one. These locks read models through the DM reader, which lists such groups apart from the fields
and repeatable declarations that make every other group present, and replay the rows `eg-fixed`,
`eg-rep`, `eg-fixed-root`, `eg-ref` and `eg-rule-only` of the retained Kernel 30.8.1 capture
`evidence/kernel-30.8.1/captures/field-declaration-notifications-2026-10-13/`. The root and message
position rows come from the
[empty-group checkpoint](../../../docs/sources/group-and-iteration-probes.md#src-empty-declared-group);
the twins that populate the group are controls, and a group populated only through a descendant
(`subtree-not-direct`) is admitted.

Not locked, because unmeasured: a star written on the empty group, and the group named where a field
is expected.
-/

namespace A12Kernel.Dm.EmptyGroupLocks

open Lean A12Kernel

private def element (kind id name : String) (body : List (String × Json)) : Json :=
  Json.mkObj [("type", .str kind), ("id", .str id), ("name", .str name), (kind, Json.mkObj body)]

private def stringField (id name : String) : Json :=
  element "Field" id name [("fieldType", Json.mkObj [("type", "StringType")])]

private def group (id name : String) (repeatability : Nat) (children : List Json) : Json :=
  element "Group" id name [("repeatability", toJson repeatability),
    ("elements", Json.arr children.toArray)]

private def ruleElement (id name errorEntityRelPath errorCondition : String) : Json :=
  element "Rule" id name [("errorEntityRelPath", .str errorEntityRelPath), ("errorCode", "C"),
    ("errorCondition", .str errorCondition), ("severity", "ERROR"),
    ("errorMessage", Json.arr #[Json.mkObj [("locale", "en_US"), ("text", "m")]])]

/-- The capture's base model, reduced to the root `Form` and its field `Value`, with the row's
elements appended to it and its further root groups added. -/
private def modelJson (appended : List Json) (roots : List Json := []) : Json :=
  checkedEntryFrame <| Json.mkObj [("content", Json.mkObj [("modelRoot", Json.mkObj [("rootGroups",
    Json.arr (#[group "/Form" "Form" 1 (stringField "/Form/Value" "Value" :: appended)] ++
      roots.toArray))])])]

private def emptyGroup : Json := group "/Form/Empty" "Empty" 1 []

private def read? (appended : List Json) (roots : List Json := []) : Option DmModel :=
  (Dm.readModel (modelJson appended roots)).toOption

/-- What a rule of the model is refused with, or `admitted`. The rule-check route reports an elaborator's
error as its printed form and no class, so a row below names the error and a separate example locks the
class that error projects to. -/
private def outcome (dm : DmModel) (rule : DmRule) : String :=
  match checkRule dm .english rule with
  | .ok _ => "admitted"
  | .error refusal => refusal.detail

private def formRule (condition : String) : DmRule :=
  { group := ["Form"], name := "R1", errorEntityRelPath := "../Value", errorCode := "C"
    condition, severity := "ERROR" }

private def conditionOutcome? (appended : List Json) (condition : String)
    (roots : List Json := []) : Option String := do
  pure (outcome (← read? appended roots) (formRule condition))

/-- Whether the condition is refused by the group-reference error `arm` naming `path`. -/
private def refusedBy? (appended : List Json) (condition arm path : String)
    (roots : List Json := []) : Option Bool := do
  let detail ← conditionOutcome? appended condition roots
  pure ((detail.splitOn s!"FixedGroupReferenceError.{arm} {path}").length == 2)

-- eg-fixed and eg-rep: the model is valid, and only the nonrepeatable group is listed as empty.
example :
    ((read? [emptyGroup]).map fun dm => (dm.flat.validate.isOk, dm.flat.emptyNonrepeatableGroups)) =
      some (true, [["Form", "Empty"]]) ∧
    ((read? [group "/Form/Empty" "Empty" 3 []]).map fun dm =>
      (dm.flat.validate.isOk, dm.flat.emptyNonrepeatableGroups)) = some (true, []) := by
  native_decide

-- eg-fixed-root: an empty root is listed by its own path, and the group is present in no other way.
example :
    ((read? [] [group "/Empty" "Empty" 1 []]).map fun dm =>
      (dm.flat.validate.isOk, dm.flat.emptyNonrepeatableGroups,
        dm.flat.hasGroupPath ["Empty"], dm.flat.declaresEmptyGroup ["Empty"])) =
      some (true, [["Empty"]], false, true) := by
  native_decide

-- The listing follows the subtree: a group populated only through a descendant is not empty, and a
-- group holding an empty subgroup and nothing else is listed with it.
example :
    ((read? [group "/Form/Shell" "Shell" 1 [group "/Form/Shell/Inner" "Inner" 1
        [stringField "/Form/Shell/Inner/Deep" "Deep"]]]).map (·.flat.emptyNonrepeatableGroups)) =
      some [] ∧
    ((read? [group "/Form/Outer" "Outer" 1 [group "/Form/Outer/Hollow" "Hollow" 1 []]]).map
      (·.flat.emptyNonrepeatableGroups)) = some [["Form", "Outer", "Hollow"], ["Form", "Outer"]] := by
  native_decide

-- eg-ref: the presence predicate on the empty group is refused by the empty-group error; the populated
-- twin and the group populated only through a descendant are admitted.
example :
    refusedBy? [emptyGroup] "GroupFilled(Empty) and FieldNotFilled(Value)" "groupHasNoFields"
        "[\"Form\", \"Empty\"]" = some true ∧
    conditionOutcome? [group "/Form/Full" "Full" 1 [stringField "/Form/Full/Item" "Item"]]
      "GroupFilled(Full) and FieldNotFilled(Value)" = some "admitted" ∧
    conditionOutcome? [group "/Form/Shell" "Shell" 1 [group "/Form/Shell/Inner" "Inner" 1
        [stringField "/Form/Shell/Inner/Deep" "Deep"]]]
      "GroupFilled(Shell) and FieldNotFilled(Value)" = some "admitted" := by
  native_decide

-- A field-list quantifier reads the same group the same way, by relative and absolute spelling.
example :
    refusedBy? [emptyGroup] "FieldsNotCollectivelyFilled(Empty) and FieldNotFilled(Value)"
        "groupHasNoFields" "[\"Form\", \"Empty\"]" = some true ∧
    refusedBy? [emptyGroup] "FieldsNotCollectivelyFilled(/Form/Empty) and FieldNotFilled(Value)"
        "groupHasNoFields" "[\"Form\", \"Empty\"]" = some true := by
  native_decide

-- An empty root is refused by the same error, and an undeclared group keeps the unknown-group error.
example :
    refusedBy? [] "GroupFilled(/Hollow) and FieldNotFilled(Value)" "groupHasNoFields" "[\"Hollow\"]"
        [group "/Hollow" "Hollow" 1 []] = some true ∧
    refusedBy? [emptyGroup] "GroupFilled(Nope) and FieldNotFilled(Value)" "unknownGroup"
        "[\"Form\", \"Nope\"]" = some true := by
  native_decide

-- The error projects to the empty-group class, and to the root class for a root.
example :
    (FixedGroupReferenceError.groupHasNoFields ["Form", "Empty"]).diagnostic? = some .groupIsEmpty ∧
    (FixedGroupReferenceError.groupHasNoFields ["Hollow"]).diagnostic? = some .rootGroupIsEmpty := by
  native_decide

-- eg-rule-only: a rule declared inside the empty group, reading outside it, is admitted.
example :
    ((read? [group "/Form/Empty" "Empty" 1 [ruleElement "/Form/Empty/R1" "R1" "../../Value"
        "FieldNotFilled(../Value)"]]).map fun dm => dm.rules.map (outcome dm)) = some ["admitted"] := by
  native_decide

private def profile : ValidationMessageKeywordProfile := .english

/-- The class a message's group position draws on a rule in `Form` that reads only `Value`. -/
private def messageClass? (dm : DmModel) (parameter : String) : Option (Option String) := do
  let checked ← (checkRule dm .english (formRule "FieldFilled(Value)")).toOption
  match elaborateValidationMessageTemplate dm.flat profile (.rule checked) ("$" ++ parameter ++ "$") with
  | .ok _ => pure none
  | .error error => pure (error.namedRuleDiagnostic?.map KernelStaticDiagnostic.kernelCode)

-- The message group position treats an empty root as a declared root: its refusal is the ordinary
-- group class, where an undeclared root draws the root class. A declared group the rule does not
-- read draws the ordinary class too.
example :
    (do messageClass? (← read? [emptyGroup] [group "/Hollow" "Hollow" 1 []]) "#/Hollow") =
      some (some "INVALID_GROUP") ∧
    (do messageClass? (← read? [emptyGroup] [group "/Hollow" "Hollow" 1 []]) "#/Nope") =
      some (some "INVALID_ROOT_GROUP") ∧
    (do messageClass? (← read? [emptyGroup]) "#/Form/Empty") = some (some "INVALID_GROUP") := by
  native_decide

end A12Kernel.Dm.EmptyGroupLocks
