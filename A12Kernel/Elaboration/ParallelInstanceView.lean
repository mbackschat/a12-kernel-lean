import A12Kernel.Elaboration.Flat.Model
import A12Kernel.Elaboration.CheckedDocument

/-! # The model one joined parallel instance reads

A parallel iteration evaluates each joined instance with one row of every pair group bound: the
target row and the partner row its key matches. Read statically, each pair group is then a
non-repeatable group, so the ordinary leaf elaborators accept its fields exactly as they accept any
fixed read. The view keeps every field identity, which lets a leaf elaborated against it evaluate
over the instance's joined reads (spec/07 §2; parallel-flat-leaves capture, 2026-10-14). A side
without a matching row is read at a free row of its group instead, as a row holding only its key.
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

/-- A row of `group` beside `outer` that the document does not instantiate and its capacity admits.
A declared slot there reads as empty, which is how the Kernel reads an unmatched side: as a row
holding only its key (joined-carrier-limits capture, rows `u01b`–`u03b`, 2026-10-14). The index slot
reads empty too, so a leaf reading the unmatched side's own index field is not this account. None
when every in-capacity row is instantiated or a frame level lies between `outer` and `group`.
Bindings of `outer` outside the group's frames are dropped, so a target row's environment serves. -/
def CheckedDocument.keyOnlyEnvironment? (document : CheckedDocument model) (outer : Env)
    (group : RepeatableGroupDecl) : Option Env := do
  let scope := model.repeatableScopeForGroupPath group.path
  let ancestors ← (outer.pathForScope scope.dropLast).toOption
  let capacity ← group.repeatability
  let free ← ((List.range capacity).map (· + 1)).find? fun index =>
    !document.source.instantiatedRows.contains { group := group.level, path := ancestors ++ [index] }
  pure (outer.filter (scope.dropLast.contains ·.1) ++ [(group.level, free)])

end A12Kernel
