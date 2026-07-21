import A12Kernel.Semantics.NumericComputationResult
import A12Kernel.Semantics.NumericStoredNumber

/-! # Numeric computed-target classification

This capsule consumes one already-evaluated Number expression at one nonrepeatable target after separate static assignment-scale admission. It owns the first admitted target checks and change-only delta projection. Exact decimal conversion and placement-sensitive document application remain separate.
-/

namespace A12Kernel

/-- After separate assignment-scale admission, the runtime target policy checks signedness plus minimum/maximum fractional digits, with no range, zero, or integer-digit extension. Warning suppression selects an evaluator entry point rather than changing this policy. -/
structure NumericTargetPolicy where
  info : NumField
  minFractionalDigits : Nat
  minLeMax : minFractionalDigits ≤ info.scale
  deriving Repr, DecidableEq

/-- Target-check failures represented by the first admitted policy. The names correspond to the target's own formal-check class, not inherited operand invalidity. -/
inductive NumericTargetError where
  | totalDigitsTooLong
  | negativeNotAllowed
  | suppressedScaleMismatch
  deriving Repr, DecidableEq

/-- A calculation-local invalid result with no attempted decimal to store. `calculationValue` is the language-neutral cause behind `berechnungsWertFehler`. -/
inductive NumericTargetInvalidity where
  | calculationValue
  deriving Repr, DecidableEq

/-- Fail-closed routing outside the ordinary unsuppressed target fragment. The runtime no-fit arm is reachable only through the separately authorable comparison-scale warning suppression. -/
inductive NumericTargetCheckFault where
  | fractionalScaleDoesNotFit (naturalScale maximumScale : Nat)
  deriving Repr, DecidableEq

/-- Complete one-target semantic outcome needed before document application. A clean no-result, rejected attempt, domain-invalid no-value, and inherited poison remain distinct even where delta projection later agrees. -/
inductive NumericTargetOutcome where
  | noValue
  | accepted (stored : StoredNumber)
  | rejected (attempted : StoredNumber) (cause : NumericTargetError)
  | invalidNoValue (cause : NumericTargetInvalidity)
  | inheritedPoison (cause : FormalCause)
  deriving Repr, DecidableEq

/-- Supported target outcome or explicit refusal of an ordinary no-fit value whose scale warning was not suppressed. -/
inductive NumericTargetCheckResult where
  | supported (outcome : NumericTargetOutcome)
  | unsupported (fault : NumericTargetCheckFault)
  deriving Repr, DecidableEq

/-- The universal Number digit limit applied by the reduced computed-target format check. -/
def numericStoredDigitLimit : Nat := 15

/-- Significant-digit budget of the warning-suppressed no-fit renderer. -/
def numericComputedNoFitPrecisionLimit : Nat := 16

namespace NumericTargetPolicy

/-- Return the first reduced formal-check failure shared by both stored-value branches. Digit overflow precedes signedness. -/
def firstAttemptError? (policy : NumericTargetPolicy)
    (attempted : StoredNumber) : Option NumericTargetError :=
  if numericStoredDigitLimit < attempted.digitCount then
    some .totalDigitsTooLong
  else if attempted.unscaled < 0 then
    if policy.info.signed then
      none
    else
      some .negativeNotAllowed
  else
    none

/-- Apply the reduced formal checks to one stored attempt. -/
def checkAttempt (policy : NumericTargetPolicy)
    (attempted : StoredNumber) : NumericTargetOutcome :=
  match policy.firstAttemptError? attempted with
  | some cause => .rejected attempted cause
  | none => .accepted attempted

/-- Classify one expression result after separate static assignment-scale admission. Fit rendering is uncapped; digit overflow therefore retains the full attempted value. The universal digit check precedes signedness. -/
def check (policy : NumericTargetPolicy) :
    NumericComputationResult → NumericTargetCheckResult
  | .domainFailure =>
      .supported (.invalidNoValue .calculationValue)
  | .poison cause =>
      .supported (.inheritedPoison cause)
  | .value amount =>
      let (naturalScale, attempted) :=
        StoredNumber.fromComputed amount policy.minFractionalDigits
      if naturalScale ≤ policy.info.scale then
        .supported (policy.checkAttempt attempted)
      else
        .unsupported
          (.fractionalScaleDoesNotFit naturalScale policy.info.scale)

/-- Classify one expression result when the computation explicitly suppresses the assignment-scale warning. Values that fit use the ordinary path unchanged. A no-fit value is rendered through the separate 16-significant-digit compatibility boundary and remains rejected even when the reduced target checks would accept it. -/
def checkWithScaleWarningSuppressed (policy : NumericTargetPolicy) :
    NumericComputationResult → NumericTargetCheckResult
  | .domainFailure =>
      .supported (.invalidNoValue .calculationValue)
  | .poison cause =>
      .supported (.inheritedPoison cause)
  | .value amount =>
      let (naturalScale, attempted) :=
        StoredNumber.fromComputed amount policy.minFractionalDigits
      if naturalScale ≤ policy.info.scale then
        .supported (policy.checkAttempt attempted)
      else
        let boundedAttempt :=
          StoredNumber.fromComputedBounded amount
            numericComputedNoFitPrecisionLimit
        match policy.firstAttemptError? boundedAttempt with
        | some cause => .supported (.rejected boundedAttempt cause)
        | none =>
            .supported (.rejected boundedAttempt .suppressedScaleMismatch)

end NumericTargetPolicy

/-- Prior target state used only for change-only delta reporting. It intentionally erases absent versus present-empty placement. -/
inductive PriorNumericTarget where
  | empty
  | filled (stored : StoredNumber)
  deriving Repr, DecidableEq

/-- Observable Number computation delta. Domain invalidity and inherited poison have no attempted stored value and therefore use the same immediate clear/silence projection as clean no-result. -/
inductive NumericDelta where
  | value (stored : StoredNumber)
  | cleared
  | errored (attempted : StoredNumber) (cause : NumericTargetError)
  deriving Repr, DecidableEq

namespace NumericTargetOutcome

/-- Project a checked outcome against the previous stored form. Accepted equality is exact decimal equality, target rejection reports unconditionally, and every no-applied-value outcome clears only a previously filled target. -/
def projectDelta (outcome : NumericTargetOutcome)
    (prior : PriorNumericTarget) : Option NumericDelta :=
  match outcome with
  | .accepted stored =>
      match prior with
      | .empty => some (.value stored)
      | .filled previous =>
          if stored = previous then none else some (.value stored)
  | .rejected attempted cause => some (.errored attempted cause)
  | .noValue | .invalidNoValue _ | .inheritedPoison _ =>
      match prior with
      | .empty => none
      | .filled _ => some .cleared

end NumericTargetOutcome

end A12Kernel
