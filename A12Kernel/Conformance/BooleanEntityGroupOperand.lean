import A12Kernel.Elaboration.ValidationCondition.Reference

/-! # Checked Boolean/Confirm group-scope entity-list carrier

The Boolean value-count carrier certifies one authored group slot against its constant-specific
kind gate. Translate and Analyze retain the slot plus every descendant declaration, Explain
publishes the descendant fields, and checked-document Execute reads the recursive `(row × field)`
extent while preserving declared-but-uninstantiated repeatable capacity.
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
      { level := 20, path := ["Form", "Flags", "Rows"],
        repeatability := some 3 }] }

private def directOperand : SurfaceFieldEntityOperand :=
  .field {
    base := .absolute, groups := ["Form", "Flags"], field := "Direct" }

private def starOperand (field : String) : SurfaceFieldEntityOperand :=
  .star {
    base := .absolute
    groups := [
      { name := "Form" },
      { name := "Flags" },
      { name := "Rows", starred := true }]
    field }

private def source? (expected : Bool) (groups : GroupPath) :
    Option (CheckedBooleanValueCountSource model) :=
  (elaborateBooleanValueCountSource model ["Form"] expected {
    first := .group (.path { base := .absolute, groups })
    rest := [] }).toOption

private def explicitSource? (expected : Bool) :
    Option (CheckedBooleanValueCountSource model) :=
  (elaborateBooleanValueCountSource model ["Form"] expected {
    first := directOperand
    rest := [starOperand "Left", starOperand "Right"] }).toOption

/- Measured with four structured `rule check` rows at clean a12-dmkits `57ddd442`, dmtool 0.13.0,
   against kernel 30.8.1: `True` and `False` over the Boolean group, `True` over the
   Boolean/Confirm group, and the explicit Boolean-field control. -/
example : (source? true ["Form", "Choices"]).isSome = true := by
  native_decide

example : (source? true ["Form", "Flags"]).isSome = true := by
  native_decide

example : (source? false ["Form", "Flags"]).isSome = true := by
  native_decide

/- Measured with `rule check` at clean a12-dmkits `3a4025bb`, dmtool 0.13.0, against kernel
   30.8.1: the `False` mixed Boolean/Confirm group is rejected with `MVK_NO_TYPEYESNO`. -/
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

private def rows (count : Nat) : List RowAddr :=
  (List.range count).map fun index =>
    { group := 20, path := [index + 1] }

private def cell (field : FieldId) (path : List Nat)
    (value : Bool) : ClassifiedCellInput :=
  { address := { field, path }
    stored := booleanValueCountToken value
    raw := .parsed (.bool value) }

private def runtimeCounts? (rowCount : Nat)
    (cells : List ClassifiedCellInput) : Option (NumericOperand × NumericOperand) := do
  let groupSource ← source? true ["Form", "Flags"]
  let explicitSource ← explicitSource? true
  let document ← (checkDocument prepared "en_US" {
    instantiatedRows := rows rowCount
    cells }).toOption
  let groupCount ←
    (groupSource.evaluateCheckedDocumentValidation document []).toOption
  let explicitCount ←
    (explicitSource.evaluateCheckedDocumentValidation document []).toOption
  pure (groupCount, explicitCount)

private def twoRowCells : List ClassifiedCellInput :=
  [cell 1 [] false,
    cell 2 [1] false,
    cell 2 [2] true,
    cell 3 [1] false,
    cell 3 [2] false]

private def threeRowCells : List ClassifiedCellInput :=
  twoRowCells ++ [cell 2 [3] false, cell 3 [3] false]

/- The group and explicit expansion both reach the second row. Remaining declared capacity makes
   equality growable even though every reached cell is filled. -/
example :
    runtimeCounts? 2 twoRowCells =
      some (.value 1 .growOnly, .value 1 .growOnly) := by
  native_decide

/- Instantiating the final declared row removes only the omitted-tail possibility, so the same
   count becomes fixed for both representations. -/
example :
    runtimeCounts? 3 threeRowCells =
      some (.value 1 .fixed, .value 1 .fixed) := by
  native_decide

/- A fully instantiated all-false group stays a fixed zero instead of manufacturing a match or an
   open tail. -/
example :
    runtimeCounts? 3 [
      cell 1 [] false,
      cell 2 [1] false,
      cell 2 [2] false,
      cell 2 [3] false,
      cell 3 [1] false,
      cell 3 [2] false,
      cell 3 [3] false] =
        some (.value 0 .fixed, .value 0 .fixed) := by
  native_decide

private def referenceFields? : Option (List FieldId) := do
  let source ← source? true ["Form", "Choices"]
  (source.referencePointers []).toOption.map fun pointers => pointers.map (·.field)

example : referenceFields? = some [4, 5] := by native_decide

end A12Kernel.Conformance.BooleanEntityGroupOperand
