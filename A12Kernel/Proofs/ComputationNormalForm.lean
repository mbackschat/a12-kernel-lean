import A12Kernel.Elaboration.ComputationNormalForm

/-! # The joiner satisfies the checker

The one theorem this module exists for is a semantic-preservation bridge: every normalized condition the joiner emits from a structured computation passes the shape half of the calculation checker. It is what makes the shape classes unreachable from a model that declares its computations structurally, and it is the obligation a reimplementer that emits its own condition inherits.

The rounding-mode results characterize the arm the generator leaves to a member declared beside the structure: this check fires exactly when the declared mode is not exact and some alternative declares no tolerance range. That `RoundDown` counts as not exact is measured ([inbound](../../docs/SOURCES.md#inbound-2026-09-25g-rounding-mode)).
-/

namespace A12Kernel

/-- Every branch the joiner emits compares the computed field itself, so no emitted member is
malformed. -/
@[simp] theorem branchRefusal_emitBranch (computedField : String)
    (alternative : DeclaredComputationAlternative) :
    branchRefusal computedField (emitBranch computedField alternative) = none := by
  simp [branchRefusal, emitBranch]

/-- **The bridge.** Every condition the joiner emits passes the shape checks, for every structured
computation and every alternative list it accepts. A reimplementer emitting its own condition owes
exactly this. -/
theorem joinAlternatives_passes_shape_checks (computation : StructuredComputation)
    (condition : NormalizedCondition) (h : joinAlternatives computation = some condition) :
    normalizedFormRefusal computation.computedField condition = none := by
  unfold joinAlternatives at h
  cases hAlternatives : computation.alternatives with
  | nil => simp only [hAlternatives] at h; simp at h
  | cons first rest =>
    cases rest with
    | nil =>
      simp only [hAlternatives] at h
      cases hCommon : computation.commonPrecondition <;> simp only [hCommon] at h <;>
        simp only [Option.map_some, Option.map_none, Option.toList_some, Option.toList_none,
          List.nil_append, List.cons_append, Option.some.injEq] at h <;>
        subst h <;>
        simp [normalizedFormRefusal, memberRefusal]
    | cons second more =>
      simp only [hAlternatives] at h
      cases hCommon : computation.commonPrecondition <;> simp only [hCommon] at h <;>
        simp only [Option.map_some, Option.map_none, Option.toList_some, Option.toList_none,
          List.nil_append, List.cons_append, Option.some.injEq] at h <;>
        subst h <;>
        simp [normalizedFormRefusal, memberRefusal, List.findSome?_eq_none_iff]

/-- An empty alternative list emits no condition, so there is nothing for the checker to see. This
is the sole input the bridge above does not cover, and it is covered by there being no condition
rather than by a passing one. -/
theorem joinAlternatives_empty (computation : StructuredComputation)
    (h : computation.alternatives = []) : joinAlternatives computation = none := by
  simp [joinAlternatives, h]

/-- One alternative's rounding check fires exactly when it declares no tolerance range and the mode
is not exact. -/
theorem roundingRefusal_emitted_isSome_iff (alternative : DeclaredComputationAlternative)
    (mode : ComputationRoundingMode) :
    (roundingRefusal (emittedSpelling alternative) mode).isSome ↔
      mode ≠ .exact ∧ alternative.toleranceRange = none := by
  cases h : alternative.toleranceRange <;> cases mode <;>
    simp [roundingRefusal, emittedSpelling, h]

/-- **The rounding-mode class is a judgement about a pair, owed by every alternative.** A
computation draws it exactly when its declared mode is not exact and at least one alternative
declares no tolerance range. So the mode alone never decides it, and under a non-exact mode one
alternative without a range is enough, whatever the others declare. -/
theorem roundingModeRefusal_isSome_iff (computation : StructuredComputation) :
    (roundingModeRefusal computation).isSome ↔
      computation.roundingMode ≠ .exact ∧
        ∃ alternative ∈ computation.alternatives, alternative.toleranceRange = none := by
  simp only [roundingModeRefusal, List.findSome?_isSome_iff, roundingRefusal_emitted_isSome_iff]
  constructor
  · rintro ⟨alternative, hMember, hMode, hRange⟩
    exact ⟨hMode, alternative, hMember, hRange⟩
  · rintro ⟨hMode, alternative, hMember, hRange⟩
    exact ⟨alternative, hMember, hMode, hRange⟩

/-- The checker is not vacuous: a condition with no gate is refused, which is what makes the bridge
a statement about the generator rather than about a check that accepts everything. -/
theorem normalizedFormRefusal_ungated (computedField : String)
    (members : List NormalizedMember) :
    normalizedFormRefusal computedField { gateField := none, members := members } =
      some .invalidFieldGate := by
  simp [normalizedFormRefusal]

end A12Kernel
