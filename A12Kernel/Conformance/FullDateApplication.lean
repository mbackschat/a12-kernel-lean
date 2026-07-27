import A12Kernel.Semantics.TemporalApplication

/-! # Full-Date delta and one-target application locks

These cases distinguish source-relative change classification from the exact placement effect of applying one already-checked full-Date target outcome.
-/

namespace A12Kernel.Conformance.FullDateApplication

open A12Kernel

private def oldDate : StoredDate := ⟨"06.04.2024", by decide⟩
private def nextDate : StoredDate := ⟨"07.04.2024", by decide⟩

/- Accepted outcomes are change-sensitive but always write their exact rendered text. -/
example :
    (FullDateTargetOutcome.accepted nextDate).projectDelta (.filled nextDate) = none := by
  rfl

example :
    (FullDateTargetOutcome.accepted nextDate).projectDelta (.filled oldDate) =
      some (.value nextDate) := by
  rfl

example :
    (FullDateTargetOutcome.accepted nextDate).applyTo .absent =
      .presentValue nextDate := by
  rfl

/- Rejection retains the exact attempt even though application clears a present target. -/
example :
    (FullDateTargetOutcome.errored nextDate .before1900).projectDelta .empty =
      some (.errored nextDate .before1900) := by
  rfl

example :
    (FullDateTargetOutcome.errored nextDate .before1900).applyTo
      (.presentValue oldDate) = .presentEmpty := by
  rfl

/- Quiet no-value and poison clear only a filled delta prior and never create an absent cell. -/
example : FullDateTargetOutcome.noValue.projectDelta .empty = none := by
  rfl

example :
    FullDateTargetOutcome.noValue.projectDelta (.filled oldDate) =
      some .cleared := by
  rfl

example :
    (FullDateTargetOutcome.poison .malformed).applyTo .absent = .absent := by
  rfl

example :
    (FullDateTargetOutcome.poison .malformed).applyTo
      (.presentValue oldDate) = .presentEmpty := by
  rfl

/- Delta state cannot recover absent versus present-empty placement. -/
example :
    FullDateTargetState.toDeltaPrior .absent =
        FullDateTargetState.toDeltaPrior .presentEmpty ∧
      FullDateTargetOutcome.noValue.applyTo .absent ≠
        FullDateTargetOutcome.noValue.applyTo .presentEmpty := by
  decide

end A12Kernel.Conformance.FullDateApplication
