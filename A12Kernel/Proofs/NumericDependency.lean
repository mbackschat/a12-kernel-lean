import A12Kernel.Semantics.NumericApplication
import A12Kernel.Semantics.NumericDependency

/-! # Numeric dependency-projection laws -/

namespace A12Kernel

/-- Clean emptiness at the dependency boundary comes exactly from a clean no-result producer. -/
theorem numericDependency_empty_iff_noValue
    (outcome : NumericTargetOutcome) :
    outcome.dependencyObservation = .empty ↔ outcome = .noValue := by
  cases outcome <;>
    simp [NumericTargetOutcome.dependencyObservation]

/-- An exact stored dependency value comes exactly from the matching accepted producer outcome. -/
theorem numericDependency_value_iff_accepted
    (outcome : NumericTargetOutcome) (stored : StoredNumber) :
    outcome.dependencyObservation = .value stored ↔
      outcome = .accepted stored := by
  cases outcome <;>
    simp [NumericTargetOutcome.dependencyObservation]

/-- A calculation-local invalid result is poison rather than clean empty at the dependency boundary. -/
theorem numericInvalidity_dependency_is_poisoned
    (cause : NumericTargetInvalidity) :
    (NumericTargetOutcome.invalidNoValue cause).dependencyObservation =
      .poisoned := by
  rfl

/-- The dependency projection never exposes a rejected attempted value or its target-check subclass. -/
theorem rejectedNumericDependency_doesNotExposeAttempt
    (first second : StoredNumber)
    (firstCause secondCause : NumericTargetError) :
    (NumericTargetOutcome.rejected first firstCause).dependencyObservation =
      (NumericTargetOutcome.rejected second secondCause).dependencyObservation := by
  rfl

/-- Exact application plus observable delta still cannot determine dependency meaning: quiet no-result is clean empty, while calculation invalidity is poison. -/
theorem same_numericApplicationAndDelta_doesNotImply_sameDependency
    (prior : NumericTargetState) (cause : NumericTargetInvalidity) :
    NumericTargetOutcome.noValue.applyTo prior =
        (NumericTargetOutcome.invalidNoValue cause).applyTo prior ∧
      NumericTargetOutcome.noValue.projectDelta prior.toDeltaPrior =
        (NumericTargetOutcome.invalidNoValue cause).projectDelta
          prior.toDeltaPrior ∧
      NumericTargetOutcome.noValue.dependencyObservation ≠
        (NumericTargetOutcome.invalidNoValue cause).dependencyObservation := by
  exact ⟨rfl, rfl, by
    simp [NumericTargetOutcome.dependencyObservation]⟩

end A12Kernel
