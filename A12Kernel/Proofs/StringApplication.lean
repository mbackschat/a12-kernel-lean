import A12Kernel.Semantics.StringApplication

/-! # A12Kernel.Proofs.StringApplication — exact one-target String application laws

The relation below states the same narrow transition independently of the executable function. The bridge theorem connects the two accounts without introducing document traversal, scheduling, or a general mutation framework.
-/

namespace A12Kernel

/-- Independent relational account of exact one-target String application. -/
def StringTargetApplies : StringTargetOutcome → StringTargetState → StringTargetState → Prop
  | .accepted value, _, .presentValue applied => value = applied
  | .noValue, .absent, .absent => True
  | .noValue, .presentEmpty, .presentEmpty => True
  | .noValue, .presentValue _, .presentEmpty => True
  | .errored _ _, .absent, .absent => True
  | .errored _ _, .presentEmpty, .presentEmpty => True
  | .errored _ _, .presentValue _, .presentEmpty => True
  | .poison _, .absent, .absent => True
  | .poison _, .presentEmpty, .presentEmpty => True
  | .poison _, .presentValue _, .presentEmpty => True
  | _, _, _ => False

/-- The executable transition is sound and complete with respect to the independent relation. -/
theorem stringTargetApplies_iff_applyTo (outcome : StringTargetOutcome)
    (prior after : StringTargetState) :
    StringTargetApplies outcome prior after ↔ outcome.applyTo prior = after := by
  cases outcome <;> cases prior <;> cases after <;>
    simp [StringTargetApplies, StringTargetOutcome.applyTo,
      StringTargetState.clearValue]

/-- Exact one-target application is deterministic. -/
theorem stringTargetApplies_deterministic (outcome : StringTargetOutcome)
    (prior first second : StringTargetState)
    (firstApplies : StringTargetApplies outcome prior first)
    (secondApplies : StringTargetApplies outcome prior second) :
    first = second := by
  rw [stringTargetApplies_iff_applyTo] at firstApplies secondApplies
  exact firstApplies.symm.trans secondApplies

/-- An accepted String creates or replaces the exact target state with that checked value. -/
theorem acceptedStringTarget_applies_exactly (value : StoredString)
    (prior : StringTargetState) :
    (StringTargetOutcome.accepted value).applyTo prior = .presentValue value := by
  rfl

/-- Every outcome without an applied value clears the exact prior state: it empties a present target in place and leaves an absent target absent. -/
theorem noAppliedStringValue_clears_exactly (outcome : StringTargetOutcome)
    (prior : StringTargetState) (noAppliedValue : outcome.appliedValue = none) :
    outcome.applyTo prior = prior.clearValue := by
  cases outcome <;>
    simp [StringTargetOutcome.appliedValue, StringTargetOutcome.applyTo] at noAppliedValue ⊢

/-- Clearing a target preserves whether that target exists. -/
theorem noAppliedStringValue_preserves_presence (outcome : StringTargetOutcome)
    (prior : StringTargetState) (noAppliedValue : outcome.appliedValue = none) :
    (outcome.applyTo prior).isPresent = prior.isPresent := by
  rw [noAppliedStringValue_clears_exactly outcome prior noAppliedValue]
  cases prior <;> rfl

/-- The exact application state retains precisely the checked stored value exposed by the older value-only view. -/
theorem exactStringApplication_storedValue (outcome : StringTargetOutcome)
    (prior : StringTargetState) :
    (outcome.applyTo prior).storedValue = outcome.appliedValue := by
  cases outcome <;> cases prior <;> rfl

/-- Delta-only prior state is insufficient for exact application: absent and present-empty inputs collapse to the same delta prior while remaining observably distinct after quiet no-value application. -/
theorem equal_noValue_delta_does_not_imply_equal_exact_application :
    StringTargetOutcome.noValue.projectDelta StringTargetState.absent.toDeltaPrior =
        StringTargetOutcome.noValue.projectDelta
          StringTargetState.presentEmpty.toDeltaPrior ∧
      StringTargetOutcome.noValue.applyTo .absent ≠
        StringTargetOutcome.noValue.applyTo .presentEmpty := by
  decide

/-- Equal final empty states do not identify the outcome: quiet no-value and target rejection retain distinct delta/report provenance. -/
theorem equal_exact_application_does_not_imply_equal_delta
    (prior : StoredString) (attempted : StoredString) (cause : StringTargetError) :
    StringTargetOutcome.noValue.applyTo (.presentValue prior) =
        (StringTargetOutcome.errored attempted cause).applyTo (.presentValue prior) ∧
      StringTargetOutcome.noValue.projectDelta (.filled prior) ≠
        (StringTargetOutcome.errored attempted cause).projectDelta (.filled prior) := by
  simp [StringTargetOutcome.applyTo, StringTargetState.clearValue,
    StringTargetOutcome.projectDelta, StringDelta.projectNoValue]

end A12Kernel
