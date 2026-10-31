import A12Kernel.Elaboration.ComparisonEntry

/-! # Guarantees and grouping limits of comparison entry

The constant-pair refusal dominates every operator family. Grouping both constants forces that
refusal at any depth, while grouping just one clock can enable a comparison (the conformance
module retains the non-law). A successful pattern entry carries exactly its slot prerequisites;
only tolerance can finish here, so ordinary success must not discharge later kind/scale obligations.
-/

namespace A12Kernel

theorem comparisonConstantPairAllowed_nonconstant_left (left right : ComparisonEntryOperand)
    (h : left.constantForm = .variable) : comparisonConstantPairAllowed left right = true := by
  simp [comparisonConstantPairAllowed, h]

theorem comparisonEntry_constant_refusal (family : ComparisonEntryFamily)
    (left right : ComparisonEntryOperand) (h : comparisonConstantPairAllowed left right = false) :
    checkComparisonEntry family left right = .error .invalidCompareToConst := by
  simp [checkComparisonEntry, h]

theorem comparisonEntry_grouped_constants (family : ComparisonEntryFamily)
    (left right : ComparisonEntryOperand)
    (hl : left.constantForm ≠ .variable) (hr : right.constantForm ≠ .variable) :
    checkComparisonEntry family (.grouped left) (.grouped right) =
      .error .invalidCompareToConst := by
  cases heql : left.constantForm <;> cases heqr : right.constantForm <;>
    simp_all [checkComparisonEntry, comparisonConstantPairAllowed, ComparisonEntryOperand.constantForm]

theorem comparisonEntry_tolerance_iff (left right : ComparisonEntryOperand) :
    checkComparisonEntry .tolerance left right = .ok .complete ↔
      comparisonConstantPairAllowed left right = true ∧
        left.kind = .number ∧ right.kind = .number := by
  unfold checkComparisonEntry
  split
  · simp_all
  · split <;> simp_all

theorem comparisonEntry_pattern_iff (left right : ComparisonEntryOperand) :
    checkComparisonEntry .pattern left right = .ok .patternSource ↔
      left = .field .string ∧ right.kind = .string ∧ right.constantForm ≠ .variable := by
  cases left with
  | field k =>
      simp only [checkComparisonEntry, comparisonConstantPairAllowed,
        ComparisonEntryOperand.constantForm, Bool.not_true, Bool.false_eq_true, ite_false]
      by_cases hk : k = .string
      · subst hk
        by_cases hr : right.kind = .string <;> simp [hr]
      · simp [hk]
  | expression k =>
      simp [checkComparisonEntry, comparisonConstantPairAllowed, ComparisonEntryOperand.constantForm]
  | literal k | clock k | grouped k =>
      unfold checkComparisonEntry
      split <;> simp

theorem comparisonEntry_complete_only_tolerance (family : ComparisonEntryFamily)
    (left right : ComparisonEntryOperand)
    (h : checkComparisonEntry family left right = .ok .complete) : family = .tolerance := by
  unfold checkComparisonEntry at h
  split at h
  · contradiction
  · cases family with
    | tolerance => rfl
    | equality => simp at h
    | ordering =>
        simp only [] at h
        split at h <;> simp_all
    | pattern =>
        cases left <;> simp only [] at h
        · split at h
          · contradiction
          · split at h <;> simp_all
        all_goals simp_all

end A12Kernel
