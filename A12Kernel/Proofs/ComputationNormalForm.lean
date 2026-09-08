import A12Kernel.Elaboration.ComputationNormalForm

/-! # The joiner satisfies the checker

The one theorem this module exists for is a semantic-preservation bridge: every normalized condition the joiner emits from a structured computation passes the shape half of the calculation checker. It is what makes the shape classes unreachable from a model that declares its computations structurally, and it is the obligation a reimplementer that emits its own condition inherits.

The rounding-mode result is the same argument on a second axis: the emitted comparison and the accompanying rounding mode are two readings of one field, so the check's two conditions are complementary and its conjunction is empty.
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

/-- The emitted comparison and the accompanying rounding mode are two readings of one declared
field, so `!=` arrives exactly with exact rounding. -/
theorem emittedSpelling_notEqual_iff_exact (alternative : DeclaredComputationAlternative) :
    emittedSpelling alternative = .notEqual ↔ alternativeRounding alternative = .exact := by
  cases h : alternative.toleranceRange <;> simp [emittedSpelling, alternativeRounding, h]

/-- **The rounding-mode check never fires on an emitted alternative.** Its two conditions are
complementary by construction, which is a property of the generator rather than of the checker — so
a reimplementer deriving the rounding mode from anywhere but the tolerance range breaks it
silently, and the checker is where that would surface. -/
theorem roundingRefusal_emitted (alternative : DeclaredComputationAlternative) :
    roundingRefusal (emittedSpelling alternative) (alternativeRounding alternative) = none := by
  cases h : alternative.toleranceRange <;> simp [roundingRefusal, emittedSpelling,
    alternativeRounding, h]

/-- The checker is not vacuous: a condition with no gate is refused, which is what makes the bridge
a statement about the generator rather than about a check that accepts everything. -/
theorem normalizedFormRefusal_ungated (computedField : String)
    (members : List NormalizedMember) :
    normalizedFormRefusal computedField { gateField := none, members := members } =
      some .invalidFieldGate := by
  simp [normalizedFormRefusal]

end A12Kernel
