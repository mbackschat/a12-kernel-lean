import A12Kernel.Semantics.TemporalApplication

/-! # DateTime delta and one-target application locks -/

namespace A12Kernel.Conformance.DateTimeApplication

open A12Kernel

private def oldValue : StoredDateTime :=
  ⟨"23.06.2025T09:59:59", by decide⟩

private def nextValue : StoredDateTime :=
  ⟨"23.06.2025T10:00:00", by decide⟩

/- Accepted DateTime text is change-sensitive but always applies exactly. -/
example :
    (DateTimeTargetOutcome.accepted nextValue).projectDelta
      (.filled nextValue) = none := by
  rfl

example :
    (DateTimeTargetOutcome.accepted nextValue).projectDelta
      (.filled oldValue) = some (.value nextValue) := by
  rfl

example :
    (DateTimeTargetOutcome.accepted nextValue).applyTo .absent =
      .presentValue nextValue := by
  rfl

/- Quiet no-value and poison clear a filled target, preserve present-empty placement, and never create an absent cell. -/
example :
    DateTimeTargetOutcome.noValue.projectDelta (.filled oldValue) =
      some .cleared := by
  rfl

example :
    (DateTimeTargetOutcome.poison .malformed).applyTo
      (.presentValue oldValue) = .presentEmpty := by
  rfl

example :
    DateTimeTargetOutcome.noValue.applyTo .absent = .absent ∧
      DateTimeTargetOutcome.noValue.applyTo .presentEmpty =
        .presentEmpty := by
  decide

/- Delta state cannot recover absent versus present-empty placement. -/
example :
    DateTimeTargetState.toDeltaPrior .absent =
        DateTimeTargetState.toDeltaPrior .presentEmpty ∧
      DateTimeTargetOutcome.noValue.applyTo .absent ≠
        DateTimeTargetOutcome.noValue.applyTo .presentEmpty := by
  decide

end A12Kernel.Conformance.DateTimeApplication
