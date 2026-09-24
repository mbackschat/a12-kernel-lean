import A12Kernel.Elaboration.ValidationRuleGroupOperand

/-! # Laws for the rule-owned one-level unstarred group decision table -/

namespace A12Kernel

open OneLevelUnstarredGroupUse

/-- Outside the repeated group, every shape in the measured denominator reaches the walk's class,
whatever its own gates would say. -/
theorem oneLevelUnstarredGroup_outside_refuses
    (use : OneLevelUnstarredGroupUse) (unbound : UnboundOperandLevel) :
    use.admission (.outside unbound) = .rejected unbound.diagnostic := by
  cases use <;> rfl

/-- The three positive-presence shapes are admitted once the error field binds the measured level. -/
theorem oneLevelUnstarredGroup_inside_positive_admitted :
    groupFilled.admission .inside = .admitted ∧
      atLeastOneSole.admission .inside = .admitted ∧
      allThenFixed.admission .inside = .admitted := by
  exact ⟨rfl, rfl, rfl⟩

/-- Binding the level does not collapse the carrier distinction: sole and paired counts retain different diagnostics. -/
theorem oneLevelUnstarredGroup_inside_counts_separate :
    filledGroupCountSole.admission .inside =
        .rejected KernelStaticDiagnostic.paramSizeInvalidGN ∧
      filledGroupCountThenFixed.admission .inside =
        .rejected KernelStaticDiagnostic.negativeConditionInIteration := by
  exact ⟨rfl, rfl⟩

/-- The inside-locus count and positive-quantifier accounts are observably unequal. -/
theorem oneLevelUnstarredGroup_carrier_nonlaw :
    filledGroupCountSole.admission .inside ≠
      atLeastOneSole.admission .inside := by
  decide

/-- The reviewed outside-error-field carrier has its exact refusal, while the unmeasured inside
locus remains explicitly unmapped rather than inheriting it. -/
theorem filledGroupCountSemanticIndex_locus_separates (unbound : UnboundOperandLevel) :
    (OneLevelGroupErrorLocus.outside unbound).filledGroupCountSemanticIndexAdmission =
        .rejected KernelStaticDiagnostic.semanticIndexNotAllowed ∧
      OneLevelGroupErrorLocus.inside.filledGroupCountSemanticIndexAdmission =
        .unmapped := by
  exact ⟨rfl, rfl⟩

end A12Kernel
