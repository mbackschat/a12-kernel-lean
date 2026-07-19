import A12Kernel.Proofs.NumericTarget
import A12Kernel.Semantics.NumericApplication

/-! # Exact one-target Number application laws -/

namespace A12Kernel

/-- Independent relational account of exact one-target Number application. -/
def NumericTargetApplies :
    NumericTargetOutcome → NumericTargetState → NumericTargetState → Prop
  | .accepted stored, _, .presentValue applied => stored = applied
  | .noValue, .absent, .absent => True
  | .noValue, .presentEmpty, .presentEmpty => True
  | .noValue, .presentValue _, .presentEmpty => True
  | .rejected _ _, .absent, .absent => True
  | .rejected _ _, .presentEmpty, .presentEmpty => True
  | .rejected _ _, .presentValue _, .presentEmpty => True
  | .invalidNoValue _, .absent, .absent => True
  | .invalidNoValue _, .presentEmpty, .presentEmpty => True
  | .invalidNoValue _, .presentValue _, .presentEmpty => True
  | .inheritedPoison _, .absent, .absent => True
  | .inheritedPoison _, .presentEmpty, .presentEmpty => True
  | .inheritedPoison _, .presentValue _, .presentEmpty => True
  | _, _, _ => False

/-- The executable transition is sound and complete with respect to the independent relation. -/
theorem numericTargetApplies_iff_applyTo (outcome : NumericTargetOutcome)
    (prior after : NumericTargetState) :
    NumericTargetApplies outcome prior after ↔ outcome.applyTo prior = after := by
  cases outcome <;> cases prior <;> cases after <;>
    simp [NumericTargetApplies, NumericTargetOutcome.applyTo,
      NumericTargetState.clearValue]

/-- Exact one-target Number application is deterministic. -/
theorem numericTargetApplies_deterministic (outcome : NumericTargetOutcome)
    (prior first second : NumericTargetState)
    (firstApplies : NumericTargetApplies outcome prior first)
    (secondApplies : NumericTargetApplies outcome prior second) :
    first = second := by
  rw [numericTargetApplies_iff_applyTo] at firstApplies secondApplies
  exact firstApplies.symm.trans secondApplies

/-- Accepted output yields the exact coefficient and scale in the abstract final state. -/
theorem acceptedNumericTarget_applies_exactly (stored : StoredNumber)
    (prior : NumericTargetState) :
    (NumericTargetOutcome.accepted stored).applyTo prior =
      .presentValue stored := by
  rfl

/-- Every outcome without an applied value empties a present target in place and leaves an absent target absent. -/
theorem noAppliedNumericValue_clears_exactly
    (outcome : NumericTargetOutcome) (prior : NumericTargetState)
    (noAppliedValue : outcome.appliedValue = none) :
    outcome.applyTo prior = prior.clearValue := by
  cases outcome <;>
    simp [NumericTargetOutcome.appliedValue, NumericTargetOutcome.applyTo]
      at noAppliedValue ⊢

/-- Applying no value preserves whether the target cell exists. -/
theorem noAppliedNumericValue_preserves_presence
    (outcome : NumericTargetOutcome) (prior : NumericTargetState)
    (noAppliedValue : outcome.appliedValue = none) :
    (outcome.applyTo prior).isPresent = prior.isPresent := by
  rw [noAppliedNumericValue_clears_exactly outcome prior noAppliedValue]
  cases prior <;> rfl

/-- Exact application retains precisely the classified stored decimal and never stores a rejected attempt. -/
theorem exactNumericApplication_storedValue
    (outcome : NumericTargetOutcome) (prior : NumericTargetState) :
    (outcome.applyTo prior).storedValue = outcome.appliedValue := by
  cases outcome <;> cases prior <;> rfl

/-- Delta-only prior state cannot recover absent versus present-empty placement. -/
theorem equal_numericDeltaPrior_doesNotImply_equalApplication :
    NumericTargetState.absent.toDeltaPrior =
        NumericTargetState.presentEmpty.toDeltaPrior ∧
      NumericTargetOutcome.noValue.applyTo .absent ≠
        NumericTargetOutcome.noValue.applyTo .presentEmpty := by
  decide

/-- Equal final empty states do not identify delta provenance: target rejection remains ERRORED rather than CLEARED. -/
theorem equal_numericApplication_doesNotImply_equalDelta
    (prior attempted : StoredNumber) (cause : NumericTargetError) :
    NumericTargetOutcome.noValue.applyTo (.presentValue prior) =
        (NumericTargetOutcome.rejected attempted cause).applyTo
          (.presentValue prior) ∧
      NumericTargetOutcome.noValue.projectDelta (.filled prior) ≠
        (NumericTargetOutcome.rejected attempted cause).projectDelta
          (.filled prior) := by
  simp [NumericTargetOutcome.applyTo, NumericTargetState.clearValue,
    NumericTargetOutcome.projectDelta]

/-- Even exact application plus delta cannot reconstruct why a value disappeared: target-local invalidity remains a distinct semantic outcome. -/
theorem equal_numericApplicationAndDelta_doesNotIdentify_invalidity
    (prior : NumericTargetState) (cause : NumericTargetInvalidity) :
    NumericTargetOutcome.noValue.applyTo prior =
        (NumericTargetOutcome.invalidNoValue cause).applyTo prior ∧
      NumericTargetOutcome.noValue.projectDelta prior.toDeltaPrior =
        (NumericTargetOutcome.invalidNoValue cause).projectDelta
          prior.toDeltaPrior ∧
      NumericTargetOutcome.noValue ≠ .invalidNoValue cause := by
  exact ⟨rfl, rfl, numericTarget_noValue_ne_invalid cause⟩

end A12Kernel
