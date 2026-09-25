import A12Kernel.Elaboration.ValidationRuleGroupOperand

/-! # Laws for the rule-owned one-level unstarred group decision table -/

namespace A12Kernel

open OneLevelUnstarredGroupUse

/-- Outside the repeated group, every shape in the measured denominator reaches the walk's class,
whatever its own gates would say. -/
theorem oneLevelUnstarredGroup_outside_refuses
    (use : OneLevelUnstarredGroupUse) (unbound : UnboundOperandLevel)
    (diagnostic : KernelStaticDiagnostic) (classed : unbound.diagnostic? = some diagnostic) :
    use.admission (.outside unbound) = .rejected diagnostic := by
  cases use <;> simp [OneLevelUnstarredGroupUse.admission, classed]

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

/-- The semantic-index count's refusal ignores the error field's locus, so it answers ahead of the
walk's class, which would otherwise separate the loci. -/
theorem filledGroupCountSemanticIndex_locus_irrelevant (locus : OneLevelGroupErrorLocus) :
    locus.filledGroupCountSemanticIndexAdmission =
      .rejected KernelStaticDiagnostic.semanticIndexNotAllowed := by
  cases locus <;> rfl

end A12Kernel
