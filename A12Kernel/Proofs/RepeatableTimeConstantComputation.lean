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

/-- **Every row is accepted, unconditionally.** This family owns no rejection branch, matching a
target domain whose every admitted clock passes the basic check — so unlike its Number and Date
siblings there is no attempted-value retention rule to get wrong, and a consumer may read the store
without a failure case. The hypothesis-free form is the content: no clock, target, or row makes it
fail. -/
theorem checkedRepeatableTimeConstantComputation_execute_alwaysAccepts
    {model : FlatModel}
    (operation : CheckedRepeatableTimeConstantComputation model)
    (input : CheckedDocument model)
    (outcomes : List RepeatableTimeConstantComputationOutcome)
    (executed : operation.execute input = .ok outcomes) :
    ∀ entry ∈ outcomes, entry.outcome =
      .accepted (TimeTargetFormat.render operation.timeTarget.format operation.constant) := by
  simp only [CheckedRepeatableTimeConstantComputation.execute,
    CheckedRepeatableTimeConstantComputation.outcome] at executed
  split at executed
  · simp at executed
  · split at executed
    · simp at executed
    · obtain ⟨rfl⟩ := Except.ok.inj executed
      intro entry member
      simp only [List.mem_map] at member
      obtain ⟨path, _, built⟩ := member
      exact built ▸ rfl

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
