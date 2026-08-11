import A12Kernel.Elaboration.ValidationRule

/-! # A12Kernel.Conformance.RepetitionNotUniqueDiagnostic — RNU key-admission diagnostic identity

`RepetitionNotUnique` reuses two classes the group-list families already own and adds one of its own,
and the separating fact is the **collapse**: the two structurally different ways a key can sit outside
the iterated repeatable group — a second key in a different group, and a sole key whose group is not
repeatable — draw one Kernel class, so the local error type is finer than the observable.

The whole-rule error-field reference gate is measured here too, because it is the gate that decides
whether an RNU rule is authorable at all and it is not an operand gate.
-/

namespace A12Kernel.Conformance.RepetitionNotUniqueDiagnostic

open A12Kernel

private def probeModel : FlatModel :=
  { fields := [
      { id := 1, groupPath := ["Probe", "A"], name := "AVal",
        policy := { kind := .string } },
      { id := 2, groupPath := ["Probe", "Rows"], name := "RowVal",
        policy := { kind := .string }, repeatableScope := [10] },
      { id := 3, groupPath := ["Probe", "Rows"], name := "RowKey2",
        policy := { kind := .string }, repeatableScope := [10] },
      { id := 4, groupPath := ["Probe", "Rows"], name := "RowNum",
        policy := { kind := .number { scale := 0, signed := false } },
        repeatableScope := [10] }]
    repeatableGroups := [{ level := 10, path := ["Probe", "Rows"] }] }

private def key (groups : List String) (field : String) : SurfaceFieldPath :=
  { base := .absolute, groups, field }

private def diagnostic? (first : SurfaceFieldPath)
    (rest : List SurfaceFieldPath := []) : Option KernelStaticDiagnostic :=
  match CheckedValidationCondition.fromRepetitionNotUnique probeModel ["Probe"]
      { firstKey := first, restKeys := rest } with
  | .ok _ => none
  | .error (.repetitionNotUnique error) => error.diagnostic?
  | .error _ => none

/- One key repeated draws the exact-duplicate class, the same one a repeated group-list operand
   draws — the operand relation is shared across families rather than restated per operator. -/
example :
    diagnostic? (key ["Probe", "Rows"] "RowVal") [key ["Probe", "Rows"] "RowVal"] =
      some .duplicateParam1 := by
  native_decide

/- The collapse: a second key in a different group and a sole key in a nonrepeatable group are two
   distinct local errors and **one** Kernel class. Projecting them apart would invent a distinction
   the engine does not report. -/
example :
    diagnostic? (key ["Probe", "Rows"] "RowVal") [key ["Probe", "A"] "AVal"] =
      some .repeatableGroupMissing := by
  native_decide

example :
    diagnostic? (key ["Probe", "A"] "AVal") = some .repeatableGroupMissing := by
  native_decide

/- An unresolvable key path takes the shared unknown-entity class rather than a key-specific one. -/
example :
    diagnostic? (key ["Probe", "Rows"] "Nope") = some .invalidEntity := by
  native_decide

/-! ## Accepted controls

Each names a shape the classes above must not claim: one key, two keys in the same repeatable group,
and a Number key — the last because the local error type has an `unsupportedKeyKind` arm whose class
no measured row covers, and Number is measured *admitted*. -/

example : diagnostic? (key ["Probe", "Rows"] "RowVal") = none := by
  native_decide

example :
    diagnostic? (key ["Probe", "Rows"] "RowVal") [key ["Probe", "Rows"] "RowKey2"] =
      none := by
  native_decide

example : diagnostic? (key ["Probe", "Rows"] "RowNum") = none := by
  native_decide

/-! ## The whole-rule error-field reference gate

Not an operand gate: it reads the assembled rule, so it is projected at rule assembly. An RNU rule
whose keys name a sibling rather than the error field draws it, while naming the error field among
the keys is admitted — which is what lets an RNU rule carry an error field inside the iterated row. -/

private def ruleDiagnostic? (errorField : FieldId)
    (first : SurfaceFieldPath) : Option KernelStaticDiagnostic := do
  let condition ← (CheckedValidationCondition.fromRepetitionNotUnique probeModel
    ["Probe"] { firstKey := first, restKeys := [] }).toOption
  match assembleResolvedValidationRule probeModel condition errorField "RNU"
      .error { parts := [] } with
  | .ok _ => none
  | .error error => error.diagnostic?

example :
    ruleDiagnostic? 3 (key ["Probe", "Rows"] "RowVal") =
      some .errorFieldNotReferenced := by
  native_decide

example : ruleDiagnostic? 2 (key ["Probe", "Rows"] "RowVal") = none := by
  native_decide

end A12Kernel.Conformance.RepetitionNotUniqueDiagnostic
