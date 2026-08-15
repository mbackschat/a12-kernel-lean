import A12Kernel.Elaboration.NumberValuesNotUnique

/-! # A12Kernel.Conformance.FieldEntityGroupOperand — the shared entity list's group slot

A group-scope operand is admitted by the shared entity-list checker, and the three gates it passes
through read **three different things**: arity reads the authored slots, the wildcard gate reads the
authored path, and the kind/category scans read the group's expansion. The cases below separate all
three, because reasoning from any one of them predicts the wrong verdict for the other two.

The headline separator is the last pair: a group operand and its own written-out expansion are two
different models. The group form is admitted where the expansion is rejected for the nested
repeatable level's missing star, so a consumer that normalizes one into the other emits a model the
Kernel refuses.

Carrier certification of an admitted group operand is not yet represented, so it reports `none`
rather than a class. That is the honest unrepresented state and not a measured admission.
-/

namespace A12Kernel.Conformance.FieldEntityGroupOperand

open A12Kernel

private def unsigned : NumField := { scale := 0, signed := false }

/-- Two nonrepeatable subtrees and one stacked repeatable pair. `Probe/A` carries a String only
    below a **nested** subgroup, so a direct-child expansion and the recursive one disagree on it;
    `Probe/B` is the pure-Number control that isolates every other gate from the kind scan. -/
private def probeModel : FlatModel :=
  { fields := [
      { id := 1, groupPath := ["Probe", "A"], name := "AVal",
        policy := { kind := .number unsigned } },
      { id := 2, groupPath := ["Probe", "A", "Deep"], name := "DeepVal",
        policy := { kind := .number unsigned } },
      { id := 3, groupPath := ["Probe", "A", "Deep"], name := "DeepText",
        policy := { kind := .string } },
      { id := 4, groupPath := ["Probe", "B"], name := "BVal",
        policy := { kind := .number unsigned } },
      { id := 5, groupPath := ["Probe", "B", "Sub"], name := "SubVal",
        policy := { kind := .number unsigned } },
      { id := 6, groupPath := ["Probe", "Rows"], name := "RowVal",
        policy := { kind := .number unsigned }, repeatableScope := [10] },
      { id := 7, groupPath := ["Probe", "Rows", "Fees"], name := "FeeVal",
        policy := { kind := .number unsigned }, repeatableScope := [10, 11] }]
    repeatableGroups := [
      { level := 10, path := ["Probe", "Rows"] },
      { level := 11, path := ["Probe", "Rows", "Fees"] }] }

private def group (groups : GroupPath) : SurfaceFieldEntityOperand :=
  .group (.path { base := .absolute, groups })

private def starredGroup (segments : List SurfaceStarGroupSegment) :
    SurfaceFieldEntityOperand :=
  .starredGroup { base := .absolute, groups := segments }

private def field (groups : List String) (name : String) :
    SurfaceFieldEntityOperand :=
  .field { base := .absolute, groups, field := name }

private def starField (segments : List SurfaceStarGroupSegment) (name : String) :
    SurfaceFieldEntityOperand :=
  .star { base := .absolute, groups := segments, field := name }

/-- Every case reads one carrier that routes through the shared checker, so a class reported here
    is the shared gate's and not this operator's own. -/
private def diagnostic? (operands : List SurfaceFieldEntityOperand) :
    Option KernelStaticDiagnostic :=
  match operands with
  | [] => none
  | first :: rest =>
      match elaborateNumberValuesNotUniqueSource probeModel ["Probe"]
          { first, rest } with
      | .ok _ => none
      | .error error => error.diagnostic?

/-! ## Arity reads the authored slots

A group slot is already-many by itself, so the single-operand class it escapes is exactly the one
its own single expanded field would draw. -/

example : diagnostic? [group ["Probe", "B"]] = none := by native_decide

example : diagnostic? [field ["Probe", "B"] "BVal"] = some .paramSizeInvalidN := by
  native_decide

/-! ## The wildcard gate reads the authored path

Both arms, on operands character-identical apart from the `*`. A repeatable group must carry it and
a nonrepeatable group must not, and the two refusals are distinct classes rather than one. -/

example : diagnostic? [group ["Probe", "Rows"]] = some .noWildcard := by
  native_decide

example :
    diagnostic? [starredGroup [{ name := "Probe" }, { name := "Rows", starred := true }]] =
      none := by
  native_decide

example :
    diagnostic? [starredGroup [{ name := "Probe" }, { name := "B", starred := true }]] =
      some .invalidWildcard := by
  native_decide

/- Nested stars both survive: the operand reopens two stacked repeatable levels. -/
example :
    diagnostic? [starredGroup [{ name := "Probe" }, { name := "Rows", starred := true },
      { name := "Fees", starred := true }]] = none := by
  native_decide

/-! ## A group operand and its written-out expansion are two different models

This is the pair a normalizing consumer gets wrong. The group form is admitted; the same extent
authored as explicit field operands is refused for the nested repeatable level's missing star, and
starring that level admits it again. Neither neighbouring gate predicts this — the expansion is what
the kind gate reads, and arity has no view of the explicit form at all.

The refusal is read as admitted-or-not rather than as a class: the Kernel reports `MVK_NO_WILDCARD`
for this shape on a field-fill quantifier, and no row places that class on this carrier, so the
shared projection deliberately names none for it. -/

private def shapeAdmitted (operands : List SurfaceFieldEntityOperand) : Bool :=
  match operands with
  | [] => false
  | first :: rest =>
      (elaborateFieldEntityShape probeModel ["Probe"] { first, rest }).toOption.isSome

example :
    shapeAdmitted [starredGroup [{ name := "Probe" },
      { name := "Rows", starred := true }]] = true := by
  native_decide

example :
    shapeAdmitted [starField [{ name := "Probe" }, { name := "Rows", starred := true }] "RowVal",
      starField [{ name := "Probe" }, { name := "Rows", starred := true },
        { name := "Fees" }] "FeeVal"] = false := by
  native_decide

example :
    shapeAdmitted [starField [{ name := "Probe" }, { name := "Rows", starred := true }] "RowVal",
      starField [{ name := "Probe" }, { name := "Rows", starred := true },
        { name := "Fees", starred := true }] "FeeVal"] = true := by
  native_decide

/-! ## The indirect arm fires between operands, the direct arm does not see them

Ancestor/descendant overlap is rejected across a group and a field below it and between two starred
groups, while the same starred group twice stays two independent authored occurrences. Both overlap
fixtures are pure Number, so a missing overlap gate would report `none` rather than a kind class. -/

example :
    diagnostic? [group ["Probe", "B"], field ["Probe", "B", "Sub"] "SubVal"] =
      some .duplicateParam2 := by
  native_decide

example :
    diagnostic? [starredGroup [{ name := "Probe" }, { name := "Rows", starred := true }],
      starredGroup [{ name := "Probe" }, { name := "Rows", starred := true },
        { name := "Fees", starred := true }]] = some .duplicateParam2 := by
  native_decide

example :
    diagnostic? [starredGroup [{ name := "Probe" }, { name := "Rows", starred := true }],
      starredGroup [{ name := "Probe" }, { name := "Rows", starred := true }]] = none := by
  native_decide

/- Two disjoint subtrees are not an overlap even across repetition shapes, which is what keeps the
   arm above from being a groupness refusal in disguise. -/
example :
    diagnostic? [group ["Probe", "B"],
      starredGroup [{ name := "Probe" }, { name := "Rows", starred := true }]] = none := by
  native_decide

/-! ## The kind and category scans read the expansion, recursively

`Probe/A` is Number in its direct children and String only inside a nested subgroup. Under the
Number carrier it therefore draws the mixing class, which a direct-child expansion would miss
entirely, while the pure-Number `Probe/B` passes both scans. A group declares no kind of its own, so
neither verdict can be read off the operand's own declaration. -/

example : diagnostic? [group ["Probe", "A"]] = some .varyingTypesNotAllowed := by
  native_decide

example : diagnostic? [group ["Probe", "A", "Deep"]] = some .varyingTypesNotAllowed := by
  native_decide

end A12Kernel.Conformance.FieldEntityGroupOperand
