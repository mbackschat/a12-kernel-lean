import A12Kernel.Semantics.FullDateApplication

/-! # Full-Date delta and application laws

The independent transition relation connects the executable one-cell application to the source-relative delta without introducing a document mutation framework.
-/

namespace A12Kernel

/-- Independent relational account of exact one-target full-Date application. -/
def FullDateTargetApplies :
    FullDateTargetOutcome → FullDateTargetState → FullDateTargetState → Prop
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

/-- Executable one-target application is sound and complete for the independent transition relation. -/
theorem fullDateTargetApplies_iff_applyTo (outcome : FullDateTargetOutcome)
    (prior after : FullDateTargetState) :
    FullDateTargetApplies outcome prior after ↔ outcome.applyTo prior = after := by
  cases outcome <;> cases prior <;> cases after <;>
    simp [FullDateTargetApplies, FullDateTargetOutcome.applyTo,
      FullDateTargetState.clearValue]

/-- Exact one-target full-Date application is deterministic. -/
theorem fullDateTargetApplies_deterministic (outcome : FullDateTargetOutcome)
    (prior first second : FullDateTargetState)
    (firstApplies : FullDateTargetApplies outcome prior first)
    (secondApplies : FullDateTargetApplies outcome prior second) :
    first = second := by
  rw [fullDateTargetApplies_iff_applyTo] at firstApplies secondApplies
  exact firstApplies.symm.trans secondApplies

/-- An unchanged accepted stored Date produces no source-relative delta. -/
theorem acceptedFullDate_unchanged_noDelta (value : StoredDate) :
    (FullDateTargetOutcome.accepted value).projectDelta (.filled value) = none := by
  simp [FullDateTargetOutcome.projectDelta, FullDateDelta.projectValue]

/-- Any outcome without an applied stored Date clears exactly in place. -/
theorem noAppliedFullDateValue_clears_exactly
    (outcome : FullDateTargetOutcome) (prior : FullDateTargetState)
    (noAppliedValue : outcome.appliedValue = none) :
    outcome.applyTo prior = prior.clearValue := by
  cases outcome <;>
    simp [FullDateTargetOutcome.appliedValue, FullDateTargetOutcome.applyTo] at noAppliedValue ⊢

/-- Exact application retains precisely the accepted stored Date exposed by the value-only projection. -/
theorem exactFullDateApplication_storedValue
    (outcome : FullDateTargetOutcome) (prior : FullDateTargetState) :
    (outcome.applyTo prior).storedValue = outcome.appliedValue := by
  cases outcome <;> cases prior <;> rfl

/-- Delta classification cannot recover placement: absent and present-empty sources classify equally while quiet no-value preserves their distinct placement. -/
theorem equal_fullDate_delta_does_not_imply_equal_exact_application :
    FullDateTargetOutcome.noValue.projectDelta
          FullDateTargetState.absent.toDeltaPrior =
        FullDateTargetOutcome.noValue.projectDelta
          FullDateTargetState.presentEmpty.toDeltaPrior ∧
      FullDateTargetOutcome.noValue.applyTo .absent ≠
        FullDateTargetOutcome.noValue.applyTo .presentEmpty := by
  decide

/-- Equal final empty states do not identify provenance: target rejection retains an unconditional error delta while quiet no-value only clears a source value. -/
theorem equal_fullDate_application_does_not_imply_equal_delta
    (prior attempted : StoredDate) (cause : FullDateTargetError) :
    FullDateTargetOutcome.noValue.applyTo (.presentValue prior) =
        (FullDateTargetOutcome.errored attempted cause).applyTo
          (.presentValue prior) ∧
      FullDateTargetOutcome.noValue.projectDelta (.filled prior) ≠
        (FullDateTargetOutcome.errored attempted cause).projectDelta
          (.filled prior) := by
  simp [FullDateTargetOutcome.applyTo, FullDateTargetState.clearValue,
    FullDateTargetOutcome.projectDelta, FullDateDelta.projectNoValue]

end A12Kernel
