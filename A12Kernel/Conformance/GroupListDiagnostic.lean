import A12Kernel.Elaboration.ValidationCondition

/-! # A12Kernel.Conformance.GroupListDiagnostic — group-list admission diagnostic identity

The separating axis is that the shared account's *rule* list and the Kernel's *class* partition do
not line up. Three measured facts do the separating: there is no root-group class at all, the two
duplicate classes are distinct, and one star draws different classes through different carriers.

The fixture mirrors the measured kernel model rather than reusing a shared one, because the
distinctions need shapes a general iteration model does not carry: a **nonrepeatable** nested pair
(the only way to reach the ancestor class without the star gate firing first), a disjoint
nonrepeatable pair, and a repeatable group.
-/

namespace A12Kernel.Conformance.GroupListDiagnostic

open A12Kernel

private def unsigned : NumField := { scale := 0, signed := false }

private def probeModel : FlatModel :=
  { fields := [
      { id := 1, groupPath := ["Probe", "A"], name := "AVal",
        policy := { kind := .number unsigned } },
      { id := 2, groupPath := ["Probe", "A", "Deep"], name := "DeepVal",
        policy := { kind := .number unsigned } },
      { id := 3, groupPath := ["Probe", "B"], name := "BVal",
        policy := { kind := .number unsigned } },
      { id := 4, groupPath := ["Probe", "Rows"], name := "RowVal",
        policy := { kind := .number unsigned }, repeatableScope := [10] }]
    repeatableGroups := [{ level := 10, path := ["Probe", "Rows"] }] }

private def group (groups : GroupPath) : SurfaceGroupListOperand :=
  .group (.path { base := .absolute, groups })

private def rowsStar : SurfaceGroupListOperand :=
  .starredGroup {
    base := .absolute
    groups := [{ name := "Probe" }, { name := "Rows", starred := true }] }

private def diagnostic? (operator : GroupFillQuantifier)
    (operands : List SurfaceGroupListOperand) : Option KernelStaticDiagnostic :=
  match CheckedValidationCondition.fromGroupList probeModel ["Probe"] operator
      operands with
  | .ok _ => none
  | .error error => error.groupListDiagnostic?

/- The exact same operand twice and an ancestor/descendant pair are **two** Kernel classes, and one
   local error carries both — the split is read off the paths it retains, not from a second
   constructor. Both operands are nonrepeatable here, so the star gate cannot pre-empt either. -/
example :
    diagnostic? .allGroupsFilled [group ["Probe", "A"], group ["Probe", "A"]] =
      some .duplicateParam1 := by
  native_decide

example :
    diagnostic? .allGroupsFilled
        [group ["Probe", "A"], group ["Probe", "A", "Deep"]] =
      some .duplicateParam2 := by
  native_decide

/- A root operand beside another takes that same ancestor class. It has none of its own, because a
   root is an ancestor of every group, and inventing one would send an author looking for a rule the
   Kernel does not have. -/
example :
    diagnostic? .allGroupsFilled [group ["Probe"], group ["Probe", "B"]] =
      some .duplicateParam2 := by
  native_decide

/- A singleton under a quantifier that requires two operands, beside the singleton-admitting
   quantifier that never reaches the class. -/
example :
    diagnostic? .allGroupsFilled [group ["Probe", "A"]] =
      some .paramSizeInvalid2 := by
  native_decide

example : diagnostic? .atLeastOneGroupFilled [group ["Probe", "A"]] = none := by
  native_decide

/- One star, two carriers, two classes: forbidden under a multi-operand quantifier, and *required*
   when a repeatable group is named without it. -/
example :
    diagnostic? .allGroupsFilled [group ["Probe", "A"], rowsStar] =
      some .noWildcardsGAllowed := by
  native_decide

example :
    diagnostic? .allGroupsFilled [group ["Probe", "A"], group ["Probe", "Rows"]] =
      some .noWildcard := by
  native_decide

/- An unknown path is separable from every overlap class, which is why the class is retained. -/
example :
    diagnostic? .allGroupsFilled [group ["Probe", "A"], group ["Probe", "Nope"]] =
      some .invalidEntity := by
  native_decide

end A12Kernel.Conformance.GroupListDiagnostic
