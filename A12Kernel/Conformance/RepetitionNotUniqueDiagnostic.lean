import A12Kernel.Elaboration.ValidationRule

/-! # A12Kernel.Conformance.RepetitionNotUniqueDiagnostic — RNU key-admission diagnostic identity

`RepetitionNotUnique` reuses two classes the group-list families already own and adds one of its own,
and the separating fact is the **collapse**: three structurally different shapes draw one Kernel
class — a second key in a nonrepeatable group, a sole key whose group is not repeatable, and the rule
already placed at that repeated group. The local error type is finer than the observable.

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
        repeatableScope := [10] },
      { id := 5, groupPath := ["Probe", "Coupons"], name := "CouponVal",
        policy := { kind := .string }, repeatableScope := [11] }]
    repeatableGroups := [
      { level := 10, path := ["Probe", "Rows"] },
      { level := 11, path := ["Probe", "Coupons"] }] }

private def indexedProbeModel : FlatModel :=
  { probeModel with repeatableGroups := [
      { level := 10, path := ["Probe", "Rows"], indexField := some 2 },
      { level := 11, path := ["Probe", "Coupons"] }] }

private def key (groups : List String) (field : String) : SurfaceFieldPath :=
  { base := .absolute, groups, field }

private def relativeKey (field : String) : SurfaceFieldPath := { base := .relative 0, groups := [], field }

private def diagnosticAt (rowGroup : GroupPath) (first : SurfaceFieldPath) (rest : List SurfaceFieldPath := []) : Option KernelStaticDiagnostic :=
  match CheckedValidationCondition.fromRepetitionNotUnique probeModel rowGroup
      { firstKey := first, restKeys := rest } with
  | .ok _ => none
  | .error (.repetitionNotUnique error) => error.diagnostic?
  | .error _ => none

private def refusesParallelAt (rowGroup : GroupPath) (first : SurfaceFieldPath) (rest : List SurfaceFieldPath := []) : Bool :=
  match CheckedValidationCondition.fromRepetitionNotUnique probeModel rowGroup
      { firstKey := first, restKeys := rest } with
  | .error (.repetitionNotUnique
      (.unsupportedParallelRepeatableKeyPaths _ _)) => true
  | .ok _ | .error _ => false

private def diagnostic? (first : SurfaceFieldPath) (rest : List SurfaceFieldPath := []) : Option KernelStaticDiagnostic :=
  diagnosticAt ["Probe"] first rest

private def indexedRnuUse
    (token : String := "SKU-1") : SurfaceRepetitionNotUniqueSemanticIndexUse := {
  target := key ["Probe", "Rows"] "RowVal"
  token
}

private def indexedRnuRefusal?
    (token : String := "SKU-1") :
    Option (CheckedRepetitionNotUniqueSemanticIndexRefusal indexedProbeModel) :=
  (elaborateRepetitionNotUniqueSemanticIndexRefusal indexedProbeModel ["Probe"] 2
    (indexedRnuUse token)).toOption

private def indexedRnuDiagnostic?
    (sourceModel : FlatModel := indexedProbeModel) (errorField : FieldId := 2) :
    Option KernelStaticDiagnostic :=
  projectRepetitionNotUniqueSemanticIndexDiagnostic? sourceModel ["Probe"] errorField
    (indexedRnuUse "SKU-1")

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

/- The otherwise-valid RNU key and semantic-index selection return the measured carrier refusal and
   its exact external code. -/
example : indexedRnuDiagnostic? = some .semanticIndexNotAllowed ∧
    indexedRnuDiagnostic?.map (·.kernelCode) =
      some "MVK_SEMANTIC_INDEX_NOT_ALLOWED" := by
  native_decide

/- The checked refusal retains one exact field, group, index, and token before projecting that
   refusal. -/
example : indexedRnuRefusal?.map (fun checked =>
    checked.source.firstKey.fieldId) = some 2 ∧
    indexedRnuRefusal?.map (fun checked =>
      checked.selection.targetDeclaration.id) = some 2 ∧
    indexedRnuRefusal?.map (fun checked =>
      checked.selection.indexDeclaration.id) = some 2 ∧
    indexedRnuRefusal?.map (fun checked =>
      checked.selection.group.path) = some ["Probe", "Rows"] ∧
    indexedRnuRefusal?.map (fun checked =>
      checked.selection.key) =
        some (CheckedSemanticIndexKey.literal (.text "SKU-1")) := by
  native_decide

/- The checked refusal retains the caller's exact token rather than specializing the measured
   `SKU-1` row. This is an internal identity guard, not wider Kernel correspondence. -/
example : (indexedRnuRefusal? "SKU-2").map
    (fun checked => checked.selection.key) =
      some (.literal (.text "SKU-2")) := by
  native_decide

/- An unindexed target, a different error field, and a rule already placed at the repeated group do
   not inherit the measured carrier code. The last keeps the otherwise-valid semantic-index side
   from replacing the RNU source check. -/
example : indexedRnuDiagnostic? probeModel = none ∧
    indexedRnuDiagnostic? indexedProbeModel 3 = none ∧
    projectRepetitionNotUniqueSemanticIndexDiagnostic? indexedProbeModel
      ["Probe", "Rows"] 2 (indexedRnuUse "SKU-1") = none := by
  native_decide

/- At the repeated rule group, both path spellings draw the third missing-repeatable shape. -/
example :
    diagnosticAt ["Probe", "Rows"] (key ["Probe", "Rows"] "RowVal") =
      some .repeatableGroupMissing ∧
    diagnosticAt ["Probe", "Rows"] (relativeKey "RowVal") =
      some .repeatableGroupMissing := by
  native_decide

/- The exact upstream index-free parallel fixture reports `MVK_NO_WILDCARD`, but the indexed
   fixture differs without an established discriminator, so the generic projector refuses. -/
example :
    refusesParallelAt ["Probe"] (key ["Probe", "Rows"] "RowVal")
        [key ["Probe", "Coupons"] "CouponVal"] = true ∧
    refusesParallelAt ["Probe", "Rows"] (key ["Probe", "Rows"] "RowVal")
        [key ["Probe", "Coupons"] "CouponVal"] = true ∧
    diagnostic? (key ["Probe", "Rows"] "RowVal")
        [key ["Probe", "Coupons"] "CouponVal"] = none := by
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
