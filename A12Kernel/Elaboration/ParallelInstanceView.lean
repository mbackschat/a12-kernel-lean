import A12Kernel.Elaboration.Flat.Model
import A12Kernel.Elaboration.CheckedDocument

/-! # The model one joined parallel instance reads

A parallel iteration evaluates each joined instance with one row of every pair group bound: the
target row and the partner row its key matches. Read statically, each pair group is then a
non-repeatable group, so the ordinary leaf elaborators accept its fields exactly as they accept any
fixed read. The view keeps every field identity, which lets a leaf elaborated against it evaluate
over the instance's joined reads (spec/07 §2; parallel-flat-leaves capture, 2026-10-14). A side
without a matching row is read at a row of its group the document does not instantiate, whose
fields read empty.
-/

namespace A12Kernel

/-- `model` with the repeatable groups at `groups` made non-repeatable and their levels removed
from every field scope. Other repeatable groups, including common outer frames, are untouched.
Joining nothing is `model` itself by definition, so an ordinary checked guard is already a guard
over that view. -/
def FlatModel.parallelInstanceView (model : FlatModel) : List GroupPath → FlatModel
  | [] => model
  | groups =>
      let joined := (model.repeatableGroups.filter (groups.contains ·.path)).map (·.level)
      { model with
        repeatableGroups := model.repeatableGroups.filter (!groups.contains ·.path)
        fields := model.fields.map fun field =>
          { field with repeatableScope := field.repeatableScope.filter (!joined.contains ·) } }

/-- The first row of `group` beside `outer` that the document does not instantiate, beyond the
group's capacity when every row within it is taken. Every slot of a row that does not exist reads
clean empty, which is the account chosen for an unmatched side: its non-key fields read empty, as the
Kernel's values show where a free row exists (joined-carrier-limits capture, rows `u01b`–`u03b`,
2026-10-14). The index slot reads empty too, as a presence test of a side's own key
field measures ([spec/07 §2.4](../../spec/07-repetition-and-iteration.md#24-reading-the-joined-row)). A full group gets the same reading, measured for an unmatched error side's keyed read and
own-key presence test (spec/07 §2.4). None only when a frame level
lies between `outer` and `group`. Bindings of `outer` outside the group's frames are dropped, so a
target row's environment serves. -/
def CheckedDocument.keyOnlyEnvironment? (document : CheckedDocument model) (outer : Env)
    (group : RepeatableGroupDecl) : Option Env := do
  let scope := model.repeatableScopeForGroupPath group.path
  let ancestors ← (outer.pathForScope scope.dropLast).toOption
  let taken := document.source.instantiatedRows
  -- `taken.length + 1` candidates cannot all be instantiated, so a free row always exists.
  let free ← ((List.range (taken.length + 1)).map (· + 1)).find? fun index =>
    !taken.contains { group := group.level, path := ancestors ++ [index] }
  pure (outer.filter (scope.dropLast.contains ·.1) ++ [(group.level, free)])

end A12Kernel
