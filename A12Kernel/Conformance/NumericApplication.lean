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
    .presentValue next := by
  rfl

example : (NumericTargetOutcome.accepted next).applyTo .presentEmpty =
    .presentValue next := by
  rfl

example : (NumericTargetOutcome.accepted next).applyTo (.presentValue old) =
    .presentValue next := by
  rfl

example : (NumericTargetOutcome.accepted next).applyTo (.presentValue next) =
    .presentValue next := by
  rfl

/- Clean no-value preserves placement and clears a filled target in place. -/
example : NumericTargetOutcome.noValue.applyTo .absent = .absent := by
  rfl

example : NumericTargetOutcome.noValue.applyTo .presentEmpty =
    .presentEmpty := by
  rfl

example : NumericTargetOutcome.noValue.applyTo (.presentValue old) =
    .presentEmpty := by
  rfl

/- Rejection, target invalidity, and inherited poison apply no value. -/
example :
    (NumericTargetOutcome.rejected overlong .totalDigitsTooLong).applyTo
        .absent = .absent ∧
      (NumericTargetOutcome.rejected overlong .totalDigitsTooLong).applyTo
        (.presentValue overlong) = .presentEmpty := by
  decide

example :
    (NumericTargetOutcome.invalidNoValue .calculationValue).applyTo
        (.presentValue old) = .presentEmpty := by
  rfl

example :
    (NumericTargetOutcome.inheritedPoison .malformed).applyTo
        (.presentValue old) = .presentEmpty := by
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
    NumericTargetOutcome.noValue.applyTo (.presentValue overlong) =
        (NumericTargetOutcome.rejected overlong .totalDigitsTooLong).applyTo
          (.presentValue overlong) ∧
      NumericTargetOutcome.noValue.projectDelta (.filled overlong) ≠
        (NumericTargetOutcome.rejected overlong .totalDigitsTooLong).projectDelta
          (.filled overlong) := by
  decide

example :
    NumericTargetOutcome.noValue.applyTo (.presentValue old) =
        (NumericTargetOutcome.invalidNoValue .calculationValue).applyTo
          (.presentValue old) ∧
      NumericTargetOutcome.noValue.projectDelta (.filled old) =
        (NumericTargetOutcome.invalidNoValue .calculationValue).projectDelta
          (.filled old) ∧
      NumericTargetOutcome.noValue ≠
        .invalidNoValue .calculationValue := by
  decide

end A12Kernel.Conformance.NumericApplication
