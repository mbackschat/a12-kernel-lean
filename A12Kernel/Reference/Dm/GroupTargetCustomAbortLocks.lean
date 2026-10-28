import A12Kernel.Reference.Dm.Validate
import A12Kernel.Reference.Dm.Document

/-! # A reached custom condition on a group target, through the reader

A rule reporting on a group fails at a reached custom condition without invoking a callback, and the
whole-rule handler reports one VALUE message at the group's first address, whatever the name answers
or whether it is registered. A field target is called as usual. Kernel oracle: the
[group-target abort capture](../../../docs/sources/key-join-and-parallel-probes.md#src-k22-group-target-custom-abort)
(`c1`, `c3`–`c5`, `c7`, `c9`), which the population replay compares on every row.
-/

namespace A12Kernel.Dm.GroupTargetCustomAbortLocks
open A12Kernel A12Kernel.Dm Lean

private def text (name : String) : Json :=
  Json.mkObj [("type", "Field"), ("name", Json.str name),
    ("Field", Json.mkObj [("fieldType", Json.mkObj [("type", "StringType")])])]

private def group (name : String) (repeatability : Nat) (elements : List Json) : Json :=
  Json.mkObj [("type", "Group"), ("name", Json.str name), ("Group", Json.mkObj [
    ("repeatability", toJson repeatability), ("elements", Json.arr elements.toArray)])]

private def modelJson : Json :=
  let items := group "Items" 3 [text "ItemNo"]
  let claims := group "Claims" 4 [text "ClaimNo", text "Status", items]
  Json.mkObj [("header", Json.mkObj [("locales", Json.arr #[Json.mkObj [("code", "en_US")]])]),
    ("content", Json.mkObj [("modelConfig", Json.mkObj [("conditionLanguage", Json.mkObj [("code", "en_US")])]),
      ("modelRoot", Json.mkObj [("rootGroups", Json.arr #[
        group "Policy" 1 [text "Holder", group "Contact" 1 [text "Phone"], claims]])])])]

private def world : World := { now := { epochMillis := 0 } }

private def registry (flat : FlatModel) : CustomValidationRegistry flat :=
  { configured := some fun name =>
      if name == "Approved" then some fun _ => true
      else if name == "Nope" then some fun _ => false
      else none }

/-- Each message as its pointer, its type and whether the whole-rule handler raised it. -/
private def run (declaring : GroupPath) (target condition : String) (policy : Json) :
    Option (List (String × String × Bool)) := do
  let dm ← (readModel modelJson).toOption
  let rule : DmRule := {
    group := declaring, name := "R", errorCode := "R", severity := "ERROR", errorEntityRelPath := target
    condition }
  let checked ← (checkRule dm .english rule).toOption
  let input ← (readDocument dm (Json.mkObj [("Policy", policy)])).toOption
  if !input.refusals.isEmpty then none
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler dm.flat).toOption
  let document ← (checkDocument prepared "en_US" input.data).toOption
  pure ((← (runRule world document checked (registry dm.flat)).toOption).map fun message =>
    let observed := observe dm.flat message
    (observed.pointer, observed.messageType, message.origin == .runtimeFailure))

private def filled : Json := Json.mkObj [("Holder", "h"), ("Contact", Json.mkObj [("Phone", "p")])]
private def holderOnly : Json := Json.mkObj [("Holder", "h")]
private def raised : Option (List (String × String × Bool)) := some [("Policy/Contact", "VALUE_ERROR", true)]

/-- The name's answer and its registration do not matter, and an unreached leaf raises nothing. -/
example : ["Approved", "Nope", "Ghost"].all (fun name =>
      run ["Policy"] "../Contact" s!"GroupFilled(Contact) And CustomCondition {name}" filled == raised) ∧
    run ["Policy"] "../Contact" "GroupFilled(Contact) And CustomCondition Approved" holderOnly = some [] := by
  native_decide

/-- A leaf reached first raises on a document whose group is empty; the field twin is called and fires
as an ordinary message. -/
example : run ["Policy"] "../Contact" "CustomCondition Approved And GroupFilled(Contact)" holderOnly = raised ∧
    run ["Policy"] "../Holder" "FieldFilled(Holder) And CustomCondition Approved" holderOnly =
      some [("Policy/Holder", "VALUE_ERROR", false)] := by
  native_decide

/-- On a repeatable rule the report lands at the iterator's first address, though only the second claim
reaches the leaf. -/
example : run ["Policy", "Claims"] "../Items"
      "GroupFilled(Items) And FieldFilled(Status) And CustomCondition Approved"
      (Json.mkObj [("Claims", Json.arr #[
        Json.mkObj [("ClaimNo", "1"), ("Items", Json.arr #[Json.mkObj [("ItemNo", "i")]])],
        Json.mkObj [("ClaimNo", "2"), ("Status", "s"), ("Items", Json.arr #[Json.mkObj [("ItemNo", "j")]])]])]) =
    some [("Policy/Claims/Items", "VALUE_ERROR", true)] := by
  native_decide

end A12Kernel.Dm.GroupTargetCustomAbortLocks
