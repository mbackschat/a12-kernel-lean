import A12Kernel.Semantics.NumericApplication

/-! # Exact one-target Number application locks -/

namespace A12Kernel.Conformance.NumericApplication

open A12Kernel

private def old : StoredNumber := { unscaled := 7, scale := 0 }
private def next : StoredNumber := { unscaled := 700, scale := 2 }
private def overlong : StoredNumber :=
  { unscaled := 1234567890123456, scale := 0 }

/- Accepted output yields its exact decimal form. The equal-value control is extensional and does not claim a physical rewrite. -/
example : (NumericTargetOutcome.accepted next).applyTo .absent =
    .presentValue (.decimal next) := by
  rfl

example : (NumericTargetOutcome.accepted next).applyTo .presentEmpty =
    .presentValue (.decimal next) := by
  rfl

example : (NumericTargetOutcome.accepted next).applyTo
    (.presentValue (.decimal old)) =
    .presentValue (.decimal next) := by
  rfl

example : (NumericTargetOutcome.accepted next).applyTo
    (.presentValue (.decimal next)) =
    .presentValue (.decimal next) := by
  rfl

/- Clean no-value preserves placement and clears a filled target in place. -/
example : NumericTargetOutcome.noValue.applyTo .absent = .absent := by
  rfl

example : NumericTargetOutcome.noValue.applyTo .presentEmpty =
    .presentEmpty := by
  rfl

example : NumericTargetOutcome.noValue.applyTo
    (.presentValue (.decimal old)) =
    .presentEmpty := by
  rfl

/- Rejection, target invalidity, and inherited poison apply no value. -/
example :
    (NumericTargetOutcome.rejected overlong .totalDigitsTooLong).applyTo
        .absent = .absent ∧
      (NumericTargetOutcome.rejected overlong .totalDigitsTooLong).applyTo
        (.presentValue (.decimal overlong)) = .presentEmpty := by
  decide

example :
    (NumericTargetOutcome.invalidNoValue .calculationValue).applyTo
        (.presentValue (.decimal old)) = .presentEmpty := by
  rfl

example :
    (NumericTargetOutcome.inheritedPoison .malformed).applyTo
        (.presentValue (.decimal old)) = .presentEmpty := by
  rfl

/- Delta state loses placement, while application preserves it. -/
example :
    NumericTargetState.absent.toDeltaPrior =
        NumericTargetState.presentEmpty.toDeltaPrior ∧
      NumericTargetOutcome.noValue.applyTo .absent ≠
        NumericTargetOutcome.noValue.applyTo .presentEmpty := by
  decide

/- Equal empty application does not erase delta or semantic-outcome provenance. -/
example :
    NumericTargetOutcome.noValue.applyTo (.presentValue (.decimal overlong)) =
        (NumericTargetOutcome.rejected overlong .totalDigitsTooLong).applyTo
          (.presentValue (.decimal overlong)) ∧
      NumericTargetOutcome.noValue.projectDelta (.filled (.decimal overlong)) ≠
        (NumericTargetOutcome.rejected overlong .totalDigitsTooLong).projectDelta
          (.filled (.decimal overlong)) := by
  decide

example :
    NumericTargetOutcome.noValue.applyTo (.presentValue (.decimal old)) =
        (NumericTargetOutcome.invalidNoValue .calculationValue).applyTo
          (.presentValue (.decimal old)) ∧
      NumericTargetOutcome.noValue.projectDelta (.filled (.decimal old)) =
        (NumericTargetOutcome.invalidNoValue .calculationValue).projectDelta
          (.filled (.decimal old)) ∧
      NumericTargetOutcome.noValue ≠
        .invalidNoValue .calculationValue := by
  decide

end A12Kernel.Conformance.NumericApplication
