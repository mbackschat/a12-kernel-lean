import A12Kernel.Semantics.NumericTarget

/-! # Numeric target and delta locks -/

namespace A12Kernel.Conformance.NumericTarget

open A12Kernel

private def target
    (maximumFractionalDigits minimumFractionalDigits : Nat)
    (signed : Bool := true)
    (admitted : minimumFractionalDigits ≤ maximumFractionalDigits := by decide) :
    NumericTargetPolicy where
  info := { scale := maximumFractionalDigits, signed }
  minFractionalDigits := minimumFractionalDigits
  minLeMax := admitted

private def stored (unscaled : Int) (scale : Nat) : StoredNumber :=
  { unscaled, scale }

private def flexibleScaleTwo : NumericTargetPolicy := target 2 0

private def scaleTwo : NumericTargetPolicy := target 2 2

/- Scale-19 store pre-rounding is observable in the retained attempted form. -/
example : (target 19 0).check (.value (1 / 3)) =
    .supported (.rejected
      (stored 3333333333333333333 19)
      .totalDigitsTooLong) := by
  native_decide

/- Pre-rounding happens before fit routing: below-half becomes zero, while a positive tie becomes scale 19 and no longer fits scale 0. -/
example : (target 0 0).check (.value (4 / (10 ^ 20 : Rat))) =
    .supported (.accepted (stored 0 0)) := by
  native_decide

example : (target 0 0).check (.value (5 / (10 ^ 20 : Rat))) =
    .unsupported (.fractionalScaleDoesNotFit 19 0) := by
  native_decide

/- A fitting over-long value is retained in full rather than shortened to pass the target check. -/
example : flexibleScaleTwo.check (.value (35402723184747801 / 100)) =
    .supported (.rejected
      (stored 35402723184747801 2)
      .totalDigitsTooLong) := by
  native_decide

/- Exactly 15 stored digits fit the universal limit. -/
example : (target 0 0).check (.value 123456789012345) =
    .supported (.accepted (stored 123456789012345 0)) := by
  native_decide

/- Total-digit overflow precedes unsigned-target rejection when both apply. -/
example : (target 0 0 false).check (.value (-1234567890123456)) =
    .supported (.rejected
      (stored (-1234567890123456) 0)
      .totalDigitsTooLong) := by
  native_decide

/- A within-limit negative attempt reaches the unsigned-target check. -/
example : (target 0 0 false).check (.value (-1)) =
    .supported (.rejected (stored (-1) 0) .negativeNotAllowed) := by
  native_decide

/- A fitting nonnegative value is accepted even when the target is unsigned. -/
example : (target 2 2 false).check (.value (3 / 2)) =
    .supported (.accepted (stored 150 2)) := by
  native_decide

/- The warning-suppressed runtime no-fit arm is a separate, fail-closed fragment. -/
example : flexibleScaleTwo.check (.value (24723 / 10000)) =
    .unsupported (.fractionalScaleDoesNotFit 4 2) := by
  native_decide

/- Arithmetic invalidity creates a target invalidity with no attempted stored value. -/
example : scaleTwo.check .domainFailure =
    .supported (.invalidNoValue .calculationValue) := by
  rfl

/- A read poison remains distinct from the target's own calculation invalidity. -/
example : scaleTwo.check (.poison .malformed) =
    .supported (.inheritedPoison .malformed) := by
  rfl

/- Accepted delta equality is stored-form equality: 7 versus 7.00 is a change. -/
example :
    (NumericTargetOutcome.accepted (stored 700 2)).projectDelta .empty =
        some (.value (stored 700 2)) ∧
      (NumericTargetOutcome.accepted (stored 700 2)).projectDelta
        (.filled (stored 700 2)) = none ∧
      (NumericTargetOutcome.accepted (stored 700 2)).projectDelta
        (.filled (stored 7 0)) = some (.value (stored 700 2)) := by
  native_decide

/- Target rejection reports unconditionally and keeps its exact attempt. -/
example :
    (NumericTargetOutcome.rejected (stored 35402723184747801 2)
      .totalDigitsTooLong).projectDelta .empty =
        some (.errored (stored 35402723184747801 2)
          .totalDigitsTooLong) := by
  rfl

/- Clean no-result, domain invalidity, and inherited poison share an immediate delta shape without sharing semantics. -/
example :
    NumericTargetOutcome.noValue.projectDelta .empty = none ∧
      (NumericTargetOutcome.invalidNoValue .calculationValue).projectDelta
        .empty = none ∧
      (NumericTargetOutcome.inheritedPoison .malformed).projectDelta
        .empty = none ∧
      NumericTargetOutcome.noValue.projectDelta (.filled (stored 7 0)) =
        some .cleared ∧
      (NumericTargetOutcome.invalidNoValue .calculationValue).projectDelta
        (.filled (stored 7 0)) = some .cleared ∧
      (NumericTargetOutcome.inheritedPoison .malformed).projectDelta
        (.filled (stored 7 0)) = some .cleared := by
  decide

end A12Kernel.Conformance.NumericTarget
