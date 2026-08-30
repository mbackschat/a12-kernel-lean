import A12Kernel.Elaboration.CheckedGroupPresence

/-! # A nonrepeatable group whose only content is a repeatable descendant

The validation arm derives a group's content from two constituents, either sufficient: an admitted
descendant cell anywhere in its subtree, or an instantiated row in a repeatable descendant. For an
ordinary group only the first can fire, so the second is untested until a group's *only* content is
a repeatable descendant.

That shape is measured at the [repeatable-descendant
checkpoint](../../docs/SOURCES.md#src-repeatable-descendant-group-count): one instantiated row
carrying no filled cell still makes the group count. These cases lock that this arm agrees, on the
same discriminator. This module's own fixture exercises the row constituent, because inside a
repeatable descendant a cell cannot exist without a row; the Kernel-side shape that separates both
constituents against one operand is measured at that checkpoint instead. The compute arm deliberately
refuses the shape instead, because its cell-list projection cannot express row instantiation at
all; `ResolvedGroupReference.computationDescendants?` owns that boundary.
-/

namespace A12Kernel.Conformance.GroupPresenceRepeatableDescendant

open A12Kernel

private def numberPolicy : FieldPolicy := { kind := .number { scale := 0, signed := false } }

/-- `RowShell` owns no field of its own; its only content is the repeatable `Rows` below it. -/
private def rowValue : FlatFieldDecl :=
  { id := 1
    groupPath := ["Probe", "RowShell", "Rows"]
    name := "RowValue"
    policy := numberPolicy
    repeatableScope := [10] }

private def flatValue : FlatFieldDecl :=
  { id := 2
    groupPath := ["Probe", "Flat"]
    name := "FlatValue"
    policy := numberPolicy }

private def rows : RepeatableGroupDecl :=
  { level := 10, path := ["Probe", "RowShell", "Rows"], repeatability := some 5 }

private def model : FlatModel :=
  { fields := [rowValue, flatValue], repeatableGroups := [rows] }

private def world : World where
  now := { epochMillis := 0 }

private def checkedFor (data : DocumentData) : Option (CheckedDocument model) := do
  let prepared ←
    (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  (checkDocument prepared "en_US" data).toOption

private def contentOf (data : DocumentData) (group : GroupPath) : Option Bool := do
  let checked ← checkedFor data
  let input ← (checked.groupPresenceInput group [] .fullyRelevant false).toOption
  pure input.derive.content

private def errorOf (data : DocumentData) (group : GroupPath) :
    Option CheckedGroupPresenceError := do
  let checked ← checkedFor data
  match checked.groupPresenceInput group [] .fullyRelevant false with
  | .ok _ => none
  | .error error => some error

private def rowAt (path : List Nat) : RowAddr := { group := 10, path }

private def cell (field : FieldId) (path : List Nat) (stored : String) (raw : RawCell) :
    ClassifiedCellInput :=
  { address := { field, path }, stored, raw }

private def flatCell : ClassifiedCellInput := cell flatValue.id [] "1" (.parsed (.num 1))

/-- One instantiated row and no cell in it at all. -/
private def emptyRow : DocumentData :=
  { instantiatedRows := [rowAt [1]], cells := [flatCell] }

private def noRows : DocumentData :=
  { instantiatedRows := [], cells := [flatCell] }

private def filledRow : DocumentData :=
  { instantiatedRows := [rowAt [1]]
    cells := [flatCell, cell rowValue.id [1] "2" (.parsed (.num 2))] }

/- The discriminator, mirroring the Kernel row. `RowShell` owns no cell anywhere, so a
   descendant-cell account answers `false` here; the instantiated row alone decides it. -/
example : contentOf emptyRow ["Probe", "RowShell"] = some true := by
  native_decide

/- The control. With no row instantiated the same group has no content, so the case above is not
   a group that counts unconditionally. -/
example : contentOf noRows ["Probe", "RowShell"] = some false := by
  native_decide

/- A filled row agrees, so the two sources of content do not disagree where both could fire. -/
example : contentOf filledRow ["Probe", "RowShell"] = some true := by
  native_decide

/- The row reaches upward through the whole subtree, so the root above the shell sees it too.
   Asking for the repeatable group's **own** presence is a different question and fails closed
   without a bound row, which is why the enclosing shell rather than the group itself is the
   operand shape the Kernel row measured. -/
example :
    contentOf emptyRow ["Probe"] = some true ∧
      errorOf emptyRow ["Probe", "RowShell", "Rows"] = some (.missingBinding 10) := by
  native_decide

/- The separator against reading every group structurally: a sibling group with no repeatable
   descendant still decides by its cells alone, filled here and absent below. -/
example :
    contentOf emptyRow ["Probe", "Flat"] = some true ∧
      contentOf { instantiatedRows := [rowAt [1]], cells := [] } ["Probe", "Flat"] =
        some false := by
  native_decide

end A12Kernel.Conformance.GroupPresenceRepeatableDescendant
