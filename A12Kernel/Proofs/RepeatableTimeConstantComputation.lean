import A12Kernel.Proofs.CheckedDocument
import A12Kernel.Elaboration.RepeatableTimeConstantComputation

/-! # Repeatable Time constant laws -/

namespace A12Kernel

/-- Two checked constants with the same target and the same clock execute identically however they
are placed: iteration comes from the target's scope and a constant supplies no other source
([checkpoint](../../docs/SOURCES.md#src-cross-group-repeatable-constant-target)). -/
theorem checkedRepeatableTimeConstantComputation_execute_ignoresDeclaringGroup
    {model : FlatModel}
    (first second : CheckedRepeatableTimeConstantComputation model)
    (sameTarget :
      first.checkedTarget.targetField = second.checkedTarget.targetField)
    (sameDeclaration :
      first.checkedTarget.declaration = second.checkedTarget.declaration)
    (sameTimeTarget : first.timeTarget = second.timeTarget)
    (sameConstant : first.constant = second.constant)
    (input : CheckedDocument model) :
    first.execute input = second.execute input := by
  simp only [CheckedRepeatableTimeConstantComputation.execute,
    CheckedRepeatableTimeConstantComputation.outcome,
    sameTarget, sameDeclaration, sameTimeTarget, sameConstant]

/-- **Every in-capacity row is accepted, and no row is rejected.** This family owns no rejection
branch, matching a target domain whose every admitted clock passes the basic check — so unlike its
Number and Date siblings there is no attempted-value retention rule to get wrong, and a consumer may
read the store without a failure case. The second disjunct is the capacity clear rather than a
refusal: no clock or target makes this fail, only an address beyond the declared repetition. -/
theorem checkedRepeatableTimeConstantComputation_execute_alwaysAccepts
    {model : FlatModel}
    (operation : CheckedRepeatableTimeConstantComputation model)
    (input : CheckedDocument model)
    (outcomes : List RepeatableTimeConstantComputationOutcome)
    (executed : operation.execute input = .ok outcomes) :
    ∀ entry ∈ outcomes,
      entry.outcome =
        .accepted (TimeTargetFormat.render operation.timeTarget.format operation.constant) ∨
        entry.outcome = .noValue := by
  simp only [CheckedRepeatableTimeConstantComputation.execute,
    CheckedRepeatableTimeConstantComputation.outcome] at executed
  intro entry member
  rcases checkedDocument_computationRowOutcomes_mem input _ _ _ _ outcomes executed
      entry member with ⟨environment, built⟩ | ⟨environment, built⟩
  · split at built
    · exact absurd built (by simp)
    · exact .inr (by simp [← Except.ok.inj built])
  · split at built
    · exact absurd built (by simp)
    · exact .inl (by simp [← Except.ok.inj built])

/-- The stored text is the target's declared format applied to the clock and nothing else, so a
constant and a computed Time producing the same clock cannot store different text. Stated separately
from acceptance because it is the half that would break if the carrier rendered at a fixed shape
rather than through the declaration. -/
theorem checkedRepeatableTimeConstantComputation_accepted_rendersInTargetFormat
    {model : FlatModel}
    (operation : CheckedRepeatableTimeConstantComputation model)
    (stored : StoredTime)
    (accepted : operation.outcome = .accepted stored) :
    stored = TimeTargetFormat.render operation.timeTarget.format operation.constant :=
  (TimeTargetOutcome.accepted.inj accepted).symm

end A12Kernel
