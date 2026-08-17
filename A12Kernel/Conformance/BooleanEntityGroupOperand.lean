import A12Kernel.Elaboration.ValidationCondition.Reference

/-! # Checked Boolean/Confirm group-scope entity-list carrier

The Boolean value-count carrier certifies one authored group slot against its constant-specific
kind gate. Translate and Analyze retain the slot plus every descendant declaration, and Explain
publishes the descendant fields. Execute remains explicit insufficient information because group
tail fillability is unmeasured for this count.
-/

namespace A12Kernel.Conformance.BooleanEntityGroupOperand

open A12Kernel

private def booleanField (id : FieldId) (groups : GroupPath) (name : String)
    (scope : List RepeatableLevel := []) : FlatFieldDecl :=
  { id, groupPath := groups, name, policy := { kind := .boolean },
    repeatableScope := scope }

private def confirmField (id : FieldId) (groups : GroupPath) (name : String) :
    FlatFieldDecl :=
  { id, groupPath := groups, name, policy := { kind := .confirm } }

private def model : FlatModel :=
  { fields := [
      booleanField 1 ["Form", "Flags"] "Direct",
      booleanField 2 ["Form", "Flags", "Rows"] "Left" [20],
      booleanField 3 ["Form", "Flags", "Rows"] "Right" [20],
      booleanField 4 ["Form", "Choices"] "Flag",
      confirmField 5 ["Form", "Choices"] "Confirmed"]
    repeatableGroups := [
      { level := 20, path := ["Form", "Flags", "Rows"] }] }

private def source? (expected : Bool) (groups : GroupPath) :
    Option (CheckedBooleanValueCountSource model) :=
  (elaborateBooleanValueCountSource model ["Form"] expected {
    first := .group (.path { base := .absolute, groups })
    rest := [] }).toOption

/- Measured with four structured `rule check` rows at clean a12-dmkits `57ddd442`, dmtool 0.13.0,
   against kernel 30.8.1: `True` and `False` over the Boolean group, `True` over the
   Boolean/Confirm group, and the explicit Boolean-field control. -/
example : (source? true ["Form", "Choices"]).isSome = true := by
  native_decide

example : (source? true ["Form", "Flags"]).isSome = true := by
  native_decide

example : (source? false ["Form", "Flags"]).isSome = true := by
  native_decide

/- The local total account applies the `False` kind gate to every descendant. The corresponding
   mixed Boolean/Confirm Kernel row is unmeasured, so this is an internal representation lock. -/
example : (source? false ["Form", "Choices"]).isNone = true := by
  native_decide

private def retainedGroup? : Option (GroupPath × Bool × List FieldId) := do
  let source ← source? true ["Form", "Flags"]
  let slot ← source.first.groupSlot?
  pure (slot.groupPath, slot.isStarred, slot.fields.map (·.id))

example :
    retainedGroup? = some (["Form", "Flags"], false, [1, 2, 3]) := by
  native_decide

private def prepared :
    PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def emptyCheckedDocument : CheckedDocument model :=
  (checkDocument prepared "en_US" { instantiatedRows := [], cells := [] })
    |>.toOption.get (by native_decide)

private def runtimeError? : Option CheckedAddressingError := do
  let source ← source? true ["Form", "Flags"]
  match source.evaluateCheckedDocumentValidation emptyCheckedDocument [] with
  | .error error => some error
  | .ok _ => none

example :
    runtimeError? =
      some (.addressing (.unsupportedGroupOperand ["Form", "Flags"])) := by
  native_decide

private def referenceFields? : Option (List FieldId) := do
  let source ← source? true ["Form", "Choices"]
  (source.referencePointers []).toOption.map fun pointers => pointers.map (·.field)

example : referenceFields? = some [4, 5] := by native_decide

end A12Kernel.Conformance.BooleanEntityGroupOperand
