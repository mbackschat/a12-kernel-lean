import A12Kernel.Proofs.CheckedDocument
import A12Kernel.Elaboration.RepeatableNumberConstantComputation

/-! # Repeatable ordinary Number constant laws -/

namespace A12Kernel

/-- Two checked constants with the same target and the same value execute identically however they
are placed. This is the measured claim stated as a law: a root declaration and a declaration at the
target's own group produce the same rows and the same outcomes, because iteration comes from the
target's scope and a constant supplies no other source
([checkpoint](../../docs/SOURCES.md#src-cross-group-repeatable-constant-target)). -/
theorem checkedRepeatableNumberConstantComputation_execute_ignoresDeclaringGroup
    {model : FlatModel}
    (first second : CheckedRepeatableNumberConstantComputation model)
    (sameTarget :
      first.checkedTarget.targetField = second.checkedTarget.targetField)
    (sameDeclaration :
      first.checkedTarget.declaration = second.checkedTarget.declaration)
    (samePolicy : first.targetPolicy = second.targetPolicy)
    (sameConstant : first.constant = second.constant)
    (input : CheckedDocument model) :
    first.execute input = second.execute input := by
  simp only [CheckedRepeatableNumberConstantComputation.execute,
    CheckedRepeatableNumberConstantComputation.outcome,
    CheckedRepeatableNumberConstantComputation.storedConstant,
    sameTarget, sameDeclaration, samePolicy, sameConstant]

/-- Every row's outcome is either the target policy's own attempt check applied to the one stored
constant, or the over-limit clear. The family therefore adds no acceptance or rejection logic of its
own, which is what lets the measured over-maximum row stand for the whole target policy rather than
for one clause of it, and what makes the retained attempt uncapped by construction rather than by a
local decision. The capacity disjunct is an address-level exclusion, not a policy outcome. -/
theorem checkedRepeatableNumberConstantComputation_execute_delegatesTargetCheck
    {model : FlatModel}
    (operation : CheckedRepeatableNumberConstantComputation model)
    (input : CheckedDocument model)
    (outcomes : List RepeatableNumberConstantComputationOutcome)
    (executed : operation.execute input = .ok outcomes) :
    ∀ entry ∈ outcomes,
      entry.outcome =
        NumericTargetPolicy.checkAttempt operation.targetPolicy operation.storedConstant ∨
        entry.outcome = .noValue := by
  simp only [CheckedRepeatableNumberConstantComputation.execute,
    CheckedRepeatableNumberConstantComputation.outcome] at executed
  intro entry member
  rcases checkedDocument_computationRowOutcomes_mem input _ _ _ _ outcomes executed
      entry member with ⟨environment, built⟩ | ⟨environment, built⟩
  · split at built
    · exact absurd built (by simp)
    · exact .inr (by simp [← Except.ok.inj built])
  · split at built
    · exact absurd built (by simp)
    · exact .inl (by simp [← Except.ok.inj built])

/-- The carrier's per-row outcome is exactly what the shared computed-Number target check produces
for an operation yielding the same amount, so a constant and an operation cannot disagree about the
same value. The fit hypothesis is a hypothesis rather than a consequence of `scaleFits`, and that is
the point: the static gate bounds the constant's **authored** scale while this branch is chosen by
its **stripped** one, so the two are not the same number and one does not imply the other here. -/
theorem checkedRepeatableNumberConstantComputation_outcome_isSharedTargetCheck
    {model : FlatModel}
    (operation : CheckedRepeatableNumberConstantComputation model)
    (naturalScale : Nat)
    (rendered :
      StoredNumber.fromComputed operation.constant.amount
          operation.targetPolicy.minFractionalDigits =
        (naturalScale, operation.storedConstant))
    (fits : naturalScale ≤ operation.targetPolicy.info.scale) :
    operation.targetPolicy.check (.value operation.constant.amount) =
      .supported operation.outcome := by
  simp [NumericTargetPolicy.check, rendered, fits,
    CheckedRepeatableNumberConstantComputation.outcome]

end A12Kernel
