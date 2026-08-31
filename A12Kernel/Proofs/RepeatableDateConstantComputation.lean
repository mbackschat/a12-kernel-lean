import A12Kernel.Elaboration.RepeatableDateConstantComputation

/-! # Repeatable Date constant laws -/

namespace A12Kernel

/-- Two checked constants with the same target and the same date execute identically however they are
placed. This is the measured claim stated as a law: a root declaration and a declaration at the
target's own group produce the same rows and the same outcomes, because iteration comes from the
target's scope and a constant supplies no other source
([checkpoint](../../docs/SOURCES.md#src-cross-group-repeatable-constant-target)). -/
theorem checkedRepeatableDateConstantComputation_execute_ignoresDeclaringGroup
    {model : FlatModel}
    (first second : CheckedRepeatableDateConstantComputation model)
    (sameTarget :
      first.checkedTarget.targetField = second.checkedTarget.targetField)
    (sameDeclaration :
      first.checkedTarget.declaration = second.checkedTarget.declaration)
    (sameDateTarget : first.dateTarget = second.dateTarget)
    (sameConstant : first.constant = second.constant)
    (input : CheckedDocument model) :
    first.execute input = second.execute input := by
  simp only [CheckedRepeatableDateConstantComputation.execute,
    CheckedRepeatableDateConstantComputation.outcome,
    sameTarget, sameDeclaration, sameDateTarget, sameConstant]

/-- Every row's outcome is exactly the declaration's own render-and-check applied to the one literal
date. The family adds no acceptance or rejection logic, which is what lets the measured formatting
rows stand for the whole target rather than for one clause of it: the declared format reaches the
result only through `evaluateCivil`'s renderer, so a constant and a computed Date producing the same
civil date cannot store different text. -/
theorem checkedRepeatableDateConstantComputation_execute_delegatesTargetRendering
    {model : FlatModel}
    (operation : CheckedRepeatableDateConstantComputation model)
    (input : CheckedDocument model)
    (outcomes : List RepeatableDateConstantComputationOutcome)
    (executed : operation.execute input = .ok outcomes) :
    ∀ entry ∈ outcomes,
      entry.outcome = operation.dateTarget.evaluateCivil operation.constant := by
  simp only [CheckedRepeatableDateConstantComputation.execute,
    CheckedRepeatableDateConstantComputation.outcome] at executed
  split at executed
  · simp at executed
  · split at executed
    · simp at executed
    · obtain ⟨rfl⟩ := Except.ok.inj executed
      intro entry member
      simp only [List.mem_map] at member
      obtain ⟨path, _, built⟩ := member
      exact built ▸ rfl

/-- The literal's stored text is the target's format applied to it, and nothing else. Stated
separately from the delegation law because it is the half the Kernel rows actually measured: one
constant into two declared formats produced two different accepted texts, so a carrier retaining the
authored spelling would satisfy every same-format fixture and fail this. -/
theorem checkedRepeatableDateConstantComputation_accepted_rendersInTargetFormat
    {model : FlatModel}
    (operation : CheckedRepeatableDateConstantComputation model)
    (stored : StoredDate)
    (accepted : operation.outcome = .accepted stored) :
    stored = operation.dateTarget.renderCivil operation.constant := by
  simp only [CheckedRepeatableDateConstantComputation.outcome] at accepted
  cases hTarget : operation.dateTarget with
  | complete target =>
      simp only [hTarget, CheckedDateConstantTarget.evaluateCivil,
        CheckedFullDateTarget.evaluateCivil] at accepted
      simp only [CheckedDateConstantTarget.renderCivil]
      split at accepted
      · exact absurd accepted (by simp)
      · split at accepted
        · exact absurd accepted (by simp)
        · exact (FullDateTargetOutcome.accepted.inj accepted).symm
  | omittedComponent target =>
      simp only [hTarget, CheckedDateConstantTarget.evaluateCivil,
        CheckedOmittedComponentDateTarget.evaluateCivil] at accepted
      simp only [CheckedDateConstantTarget.renderCivil]
      split at accepted
      · exact absurd accepted (by simp)
      · split at accepted
        · exact absurd accepted (by simp)
        · exact (FullDateTargetOutcome.accepted.inj accepted).symm

end A12Kernel
