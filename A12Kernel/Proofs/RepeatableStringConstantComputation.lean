import A12Kernel.Proofs.CheckedDocument
import A12Kernel.Elaboration.RepeatableStringConstantComputation

/-! # Repeatable ordinary String constant laws -/

namespace A12Kernel

/-- Two checked constants with the same target and the same literal execute identically however they
are placed. This is the measured claim stated as a law: a root declaration and a declaration at the
target's own group produce the same rows and the same outcomes, because iteration comes from the
target's scope and a constant supplies no other source
([checkpoint](../../docs/SOURCES.md#src-cross-group-repeatable-constant-target)). -/
theorem checkedRepeatableStringConstantComputation_execute_ignoresDeclaringGroup
    {model : FlatModel}
    (first second : CheckedRepeatableStringConstantComputation model)
    (sameTarget :
      first.checkedTarget.targetField = second.checkedTarget.targetField)
    (sameDeclaration :
      first.checkedTarget.declaration = second.checkedTarget.declaration)
    (sameLiteral : first.literal = second.literal)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model) :
    first.execute patterns input = second.execute patterns input := by
  simp only [CheckedRepeatableStringConstantComputation.execute,
    CheckedRepeatableStringConstantComputation.store,
    sameTarget, sameDeclaration, sameLiteral]

/-- Every row's outcome is either the declaration's own target check applied to the one root write
attempt, or the over-limit clear. The family therefore adds no acceptance or rejection logic of its
own, which is what lets the measured `tooLong` row stand for the whole target policy rather than for
one clause of it. -/
theorem checkedRepeatableStringConstantComputation_execute_delegatesTargetCheck
    {model : FlatModel}
    (operation : CheckedRepeatableStringConstantComputation model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model) (matcher : Option (String → Bool))
    (prepared :
      patterns.targetMatcher? operation.checkedTarget.targetField = some matcher)
    (outcomes : List RepeatableStringConstantComputationOutcome)
    (executed : operation.execute patterns input = .ok outcomes) :
    ∀ entry ∈ outcomes,
      entry.outcome =
        StringFieldPolicy.checkTargetWithPattern
          operation.checkedTarget.declaration.stringPolicy matcher operation.store ∨
        entry.outcome = .noValue := by
  simp only [CheckedRepeatableStringConstantComputation.execute, prepared] at executed
  intro entry member
  rcases checkedDocument_computationRowOutcomes_mem input _ _ _ _ outcomes executed
      entry member with ⟨environment, built⟩ | ⟨environment, built⟩
  · split at built
    · exact absurd built (by simp)
    · exact .inr (by simp [← Except.ok.inj built])
  · split at built
    · exact absurd built (by simp)
    · exact .inl (by simp [← Except.ok.inj built])

end A12Kernel
