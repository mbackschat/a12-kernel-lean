import A12Kernel.Proofs.CheckedDocument
import A12Kernel.Elaboration.RepeatableDateTimeConstantComputation

/-! # Repeatable DateTime constant laws -/

namespace A12Kernel

/-- Two checked constants with the same target and the same wall label execute identically however
they are placed: iteration comes from the target's scope and a constant supplies no other source
([checkpoint](../../docs/SOURCES.md#src-cross-group-repeatable-constant-target)). -/
theorem checkedRepeatableDateTimeConstantComputation_execute_ignoresDeclaringGroup
    {model : FlatModel}
    (first second : CheckedRepeatableDateTimeConstantComputation model)
    (sameTarget :
      first.checkedTarget.targetField = second.checkedTarget.targetField)
    (sameDeclaration :
      first.checkedTarget.declaration = second.checkedTarget.declaration)
    (sameDateTimeTarget : first.dateTimeTarget = second.dateTimeTarget)
    (sameConstant : first.constant = second.constant)
    (input : CheckedDocument model) :
    first.execute input = second.execute input := by
  simp only [CheckedRepeatableDateTimeConstantComputation.execute,
    CheckedRepeatableDateTimeConstantComputation.outcome,
    sameTarget, sameDeclaration, sameDateTimeTarget, sameConstant]

/-- **Every in-capacity row is accepted, and no row is rejected.** This family owns no rejection
branch and no evaluation fault: the constant is already a wall label, so nothing can fail to resolve.
The second disjunct is the capacity clear rather than a refusal — no label and no target makes this
fail, only an address beyond the declared repetition. -/
theorem checkedRepeatableDateTimeConstantComputation_execute_alwaysAccepts
    {model : FlatModel}
    (operation : CheckedRepeatableDateTimeConstantComputation model)
    (input : CheckedDocument model)
    (outcomes : List RepeatableDateTimeConstantComputationOutcome)
    (executed : operation.execute input = .ok outcomes) :
    ∀ entry ∈ outcomes,
      entry.outcome =
        .accepted
          (DateTimeTargetFormat.render operation.dateTimeTarget.format operation.constant) ∨
        entry.outcome = .noValue := by
  simp only [CheckedRepeatableDateTimeConstantComputation.execute,
    CheckedRepeatableDateTimeConstantComputation.outcome] at executed
  intro entry member
  rcases checkedDocument_computationRowOutcomes_mem input _ _ _ _ outcomes executed
      entry member with ⟨environment, built⟩ | ⟨environment, built⟩
  · split at built
    · exact absurd built (by simp)
    · exact .inr (by simp [← Except.ok.inj built])
  · split at built
    · exact absurd built (by simp)
    · exact .inl (by simp [← Except.ok.inj built])

/-- **Where the computed route is defined, the two routes store the same text.** A computed DateTime
reaches its target through the model zone and can fail when an instant has no local label; a constant
skips that step entirely. This says the shortcut is not a second rendering rule: whenever the zone
does map an instant to this carrier's own label, the computed outcome is exactly the constant one, so
the constant route is a strict *widening* of the computed one rather than a divergence from it. The
gap label its conformance case locks is the witness that the widening is proper. -/
theorem checkedRepeatableDateTimeConstantComputation_agreesWithResolvedInstant
    {model : FlatModel}
    (operation : CheckedRepeatableDateTimeConstantComputation model)
    (instant : Instant)
    (resolves :
      operation.dateTimeTarget.profile.localDateTime? instant = some operation.constant) :
    operation.dateTimeTarget.evaluate (.value instant) = .ok operation.outcome := by
  simp only [CheckedDateTimeTarget.evaluate,
    CheckedRepeatableDateTimeConstantComputation.outcome, resolves]
  rfl

end A12Kernel
