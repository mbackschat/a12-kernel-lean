import A12Kernel.Semantics.TemporalApplication

/-! # DateTime delta and application laws -/

namespace A12Kernel

/-- Independent relational account of exact one-target DateTime application. -/
def DateTimeTargetApplies :
    DateTimeTargetOutcome →
      DateTimeTargetState → DateTimeTargetState → Prop
  | .accepted value, _, .presentValue applied => value = applied
  | .noValue, .absent, .absent => True
  | .noValue, .presentEmpty, .presentEmpty => True
  | .noValue, .presentValue _, .presentEmpty => True
  | .poison _, .absent, .absent => True
  | .poison _, .presentEmpty, .presentEmpty => True
  | .poison _, .presentValue _, .presentEmpty => True
  | _, _, _ => False

/-- Executable DateTime application is sound and complete for the independent transition relation. -/
theorem dateTimeTargetApplies_iff_applyTo
    (outcome : DateTimeTargetOutcome)
    (prior after : DateTimeTargetState) :
    DateTimeTargetApplies outcome prior after ↔
      outcome.applyTo prior = after := by
  cases outcome <;> cases prior <;> cases after <;>
    simp [DateTimeTargetApplies, DateTimeTargetOutcome.applyTo,
      DateTimeTargetState.clearValue, TemporalTargetState.clearValue]

/-- Exact one-target DateTime application is deterministic. -/
theorem dateTimeTargetApplies_deterministic
    (outcome : DateTimeTargetOutcome)
    (prior first second : DateTimeTargetState)
    (firstApplies : DateTimeTargetApplies outcome prior first)
    (secondApplies : DateTimeTargetApplies outcome prior second) :
    first = second := by
  rw [dateTimeTargetApplies_iff_applyTo] at firstApplies secondApplies
  exact firstApplies.symm.trans secondApplies

/-- An unchanged accepted stored DateTime produces no source-relative delta. -/
theorem acceptedDateTime_unchanged_noDelta
    (value : StoredDateTime) :
    (DateTimeTargetOutcome.accepted value).projectDelta
      (.filled value) = none := by
  simp [DateTimeTargetOutcome.projectDelta,
    TemporalValueDelta.projectValue]

/-- Any DateTime outcome without an applied stored value clears exactly in place. -/
theorem noAppliedDateTimeValue_clears_exactly
    (outcome : DateTimeTargetOutcome)
    (prior : DateTimeTargetState)
    (noAppliedValue : outcome.appliedValue = none) :
    outcome.applyTo prior = prior.clearValue := by
  cases outcome <;>
    simp [DateTimeTargetOutcome.appliedValue,
      DateTimeTargetOutcome.applyTo] at noAppliedValue ⊢

/-- Exact application retains precisely the accepted stored DateTime text exposed by the value-only projection. -/
theorem exactDateTimeApplication_storedValue
    (outcome : DateTimeTargetOutcome)
    (prior : DateTimeTargetState) :
    (outcome.applyTo prior).storedValue = outcome.appliedValue := by
  cases outcome <;> cases prior <;> rfl

/-- Source-relative delta cannot recover absent versus present-empty placement. -/
theorem equal_dateTime_delta_does_not_imply_equal_exact_application :
    DateTimeTargetOutcome.noValue.projectDelta
          (DateTimeTargetState.toDeltaPrior .absent) =
        DateTimeTargetOutcome.noValue.projectDelta
          (DateTimeTargetState.toDeltaPrior .presentEmpty) ∧
      DateTimeTargetOutcome.noValue.applyTo .absent ≠
        DateTimeTargetOutcome.noValue.applyTo .presentEmpty := by
  decide

end A12Kernel
