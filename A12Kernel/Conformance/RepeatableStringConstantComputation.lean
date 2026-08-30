import A12Kernel.Elaboration.RepeatableStringConstantComputation
import A12Kernel.Elaboration.CheckedDocument

/-! # Repeatable ordinary String constant locks

The Kernel rows behind these cases are the [cross-group carrier](../../docs/SOURCES.md#src-cross-group-repeatable-constant-target)
and the [target-check](../../docs/SOURCES.md#src-repeatable-string-constant-target-check) checkpoints.
-/

namespace A12Kernel.Conformance.RepeatableStringConstantComputation

open A12Kernel

private def label : FlatFieldDecl := {
  id := 1
  groupPath := ["Probe", "Tasks"]
  name := "Label"
  policy := { kind := .string }
  repeatableScope := [10]
}

private def short : FlatFieldDecl := {
  id := 2
  groupPath := ["Probe", "Tasks"]
  name := "Short"
  policy := { kind := .string }
  stringPolicy := { maxLength := some 3 }
  repeatableScope := [10]
}

private def note : FlatFieldDecl := {
  id := 3
  groupPath := ["Probe", "Store"]
  name := "Note"
  policy := { kind := .string }
}

/-- A patterned target, so the prepared-matcher control below can be missing something real: a
target that declares no pattern needs no prepared entry and never reaches that failure. -/
private def coded : FlatFieldDecl := {
  id := 4
  groupPath := ["Probe", "Tasks"]
  name := "Coded"
  policy := { kind := .string }
  stringPatternSource := some "A+"
  repeatableScope := [10]
}

private def model : FlatModel := {
  fields := [label, short, note, coded]
  repeatableGroups := [
    { level := 10, path := ["Probe", "Tasks"], repeatability := some 3 }]
}

/-- One recognized source keeps the fixture's pattern independent of the host regex engine; the
builtin compiler is exercised by the families that actually depend on it. -/
private def patternCompiler : StringPatternCompiler := fun pattern =>
  if pattern == "A+" then
    some fun value =>
      !value.isEmpty && value.toList.all fun character => character == 'A'
  else
    none

private def prepared : PreparedFlatStringContext model patternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    patternCompiler model).toOption.get (by native_decide)

private def rows (count : Nat) : Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows :=
      (List.range count).map fun index => { group := 10, path := [index + 1] }
    cells := [] }).toOption

private def stored (text : String) (nonempty : text ≠ "" := by decide) :
    StoredString :=
  { text, nonempty }

private def outcomes? (declaringGroup : GroupPath) (target : FieldId)
    (literal : String) (count : Nat) :
    Option (List RepeatableStringConstantComputationOutcome) :=
  (checkRepeatableStringConstantComputation model declaringGroup target literal).toOption.bind
    fun operation => (rows count).bind fun input =>
      (operation.execute prepared.patterns input).toOption

/- The constant reaches every physical target row and no more, from an ancestor exactly as from the
target's own group. Two rows, two outcomes; no rows, none at all rather than one implicit instance. -/
example : (outcomes? ["Probe"] label.id "FIXED" 2,
    outcomes? ["Probe", "Tasks"] label.id "FIXED" 2,
    outcomes? ["Probe"] label.id "FIXED" 0) =
    (some [{ targetField := { field := label.id, path := [1] }
             outcome := .accepted (stored "FIXED") },
           { targetField := { field := label.id, path := [2] }
             outcome := .accepted (stored "FIXED") }],
     some [{ targetField := { field := label.id, path := [1] }
             outcome := .accepted (stored "FIXED") },
           { targetField := { field := label.id, path := [2] }
             outcome := .accepted (stored "FIXED") }],
     some []) := by
  native_decide

/- A constant the target refuses keeps its **exact attempted payload** rather than being truncated,
blanked, or dropped, and the refusal repeats per row like an accepted write. Measured on kernel
30.8.1, where the same shape reports `value: "FIXEDLONG"` with `errored` set and no clear. -/
example : outcomes? ["Probe"] short.id "FIXEDLONG" 2 =
    some [{ targetField := { field := short.id, path := [1] }
            outcome := .errored (stored "FIXEDLONG") .tooLong },
          { targetField := { field := short.id, path := [2] }
            outcome := .errored (stored "FIXEDLONG") .tooLong }] := by
  native_decide

/- The empty literal is a no-value, not an accepted empty string. That rule belongs to
`StringTerm.store` and is reused rather than restated, so a constant cannot drift from concatenation.
The fitting control on the same target separates it from the length refusal above. -/
example : (outcomes? ["Probe"] short.id "" 1, outcomes? ["Probe"] short.id "AB" 1) =
    (some [{ targetField := { field := short.id, path := [1] }
             outcome := .noValue }],
     some [{ targetField := { field := short.id, path := [1] }
             outcome := .accepted (stored "AB") }]) := by
  native_decide

/- Placement is containment: the target's own group and every ancestor admit it, and only a group the
target does not lie below is refused — with the Kernel identity that refusal actually carries. -/
example : ([["Probe", "Tasks"], ["Probe"]].map fun group =>
      (checkRepeatableStringConstantComputation model group label.id "X").toOption.isSome,
    match checkRepeatableStringConstantComputation model ["Probe", "Store"] label.id "X" with
    | .error cause => cause.diagnostic?.map KernelStaticDiagnostic.kernelCode
    | .ok _ => none) =
    ([true, true], some "MVK_ERROR_FIELD_NOT_IN_RULEGROUP") := by
  native_decide

/- A nonrepeatable target belongs to no carrier here and is declined by the shared certificate rather
than by a second local gate, so it claims no Kernel class. -/
example : (match checkRepeatableStringConstantComputation model ["Probe"] note.id "X" with
    | .error cause => (cause.diagnostic?.isSome, true)
    | .ok _ => (false, false)) = (false, true) := by
  native_decide

private def missingMatcher :
    PreparedFlatStringPatterns model patternCompiler := {
  fields := []
  modelWellFormed := prepared.patterns.modelWellFormed
}

/- An incomplete prepared-pattern input fails at the exact target instead of letting any row bypass
the target's declared policy silently. -/
example : ((checkRepeatableStringConstantComputation model ["Probe"] coded.id "FIXED").toOption.bind
    fun operation => (rows 2).bind fun input =>
      match operation.execute missingMatcher input with
      | .error fault => some fault
      | .ok _ => none) = some (.targetPatternUnavailable coded.id) := by
  native_decide

end A12Kernel.Conformance.RepeatableStringConstantComputation
