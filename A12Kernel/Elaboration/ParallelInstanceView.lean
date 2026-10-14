import A12Kernel.Elaboration.Flat.Model

/-! # The model one joined parallel instance reads

A parallel iteration evaluates each joined instance with one row of every pair group bound: the
target row and the partner row its key matches. Read statically, each pair group is then a
non-repeatable group, so the ordinary leaf elaborators accept its fields exactly as they accept any
fixed read. The view keeps every field identity, which lets a leaf elaborated against it evaluate
over the instance's joined reads (spec/07 §2; parallel-flat-leaves capture, 2026-10-14).
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

end A12Kernel
