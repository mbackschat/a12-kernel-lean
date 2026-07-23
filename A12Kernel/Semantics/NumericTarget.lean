import A12Kernel.Semantics.NumericComputationResult
import A12Kernel.Semantics.NumericStoredNumber

/-! # Numeric computed-target classification

This capsule consumes one already-evaluated Number expression at one nonrepeatable target after separate static assignment-scale admission. It owns the resolved declaration constraints, their proof-bearing target-policy construction, the reachable target checks, and change-only delta projection. Exact decimal conversion and placement-sensitive document application remain separate.
-/

namespace A12Kernel

/-- Resolved Number declaration constraints that remain reachable from canonical computed rendering. Scale and signedness stay in the shared `NumField`; leading-zero policy is omitted because computed rendering cannot reach it. -/
structure NumericTargetConstraints where
  minFractionalDigits : Nat := 0
  maxIntegerDigits : Option Nat := none
  zeroAllowed : Bool := true
  minStoredLength : Option Nat := none
  maxStoredLength : Option Nat := none
  minimum : Option Rat := none
  maximum : Option Rat := none
  deriving Repr, DecidableEq

/-- Resolved Number target constraints consumed after separate assignment-scale admission. The declaration data is retained structurally rather than copied into a parallel policy shape. Warning suppression selects an evaluator entry point rather than changing this policy. -/
structure NumericTargetPolicy extends NumericTargetConstraints where
  info : NumField
  minLeMax : minFractionalDigits ≤ info.scale
  deriving Repr, DecidableEq

namespace NumericTargetConstraints

/-- Default Number declaration constraints. This named value keeps declaration defaults and legality checks in one owner. -/
def unconstrained : NumericTargetConstraints :=
  { minFractionalDigits := 0 }

/-- Construct the complete checked target policy from one resolved declaration. The only dependent fact is the declaration's required fractional digits fitting its existing maximum scale. -/
def toPolicy? (constraints : NumericTargetConstraints)
    (info : NumField) : Option NumericTargetPolicy :=
  if admitted : constraints.minFractionalDigits ≤ info.scale then
    some {
      info
      minFractionalDigits := constraints.minFractionalDigits
      minLeMax := admitted
      maxIntegerDigits := constraints.maxIntegerDigits
      zeroAllowed := constraints.zeroAllowed
      minStoredLength := constraints.minStoredLength
      maxStoredLength := constraints.maxStoredLength
      minimum := constraints.minimum
      maximum := constraints.maximum }
  else
    none

end NumericTargetConstraints

/-- Reachable computed-Number target failures. The names correspond to the target's own formal-check class, not inherited operand invalidity. -/
inductive NumericTargetError where
  | totalDigitsTooLong
  | negativeNotAllowed
  | integerDigitsTooLong
  | zeroNotAllowed
  | storedTextTooShort
  | storedTextTooLong
  | belowMinimum
  | aboveMaximum
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

/-- The universal Number digit limit applied by the basic computed-target format check. -/
def numericStoredDigitLimit : Nat := 15

/-- Significant-digit budget of the warning-suppressed no-fit renderer. -/
def numericComputedNoFitPrecisionLimit : Nat := 16

namespace NumericTargetPolicy

/-- Return the formal-check prefix shared by fitting and warning-suppressed no-fit attempts. Universal digit overflow precedes signedness; a no-fit decimal-place error precedes every later constraint. -/
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

/-- Continue the fitting-value check after the shared prefix. Integer-digit capacity, zero prohibition, rendered length, and inclusive numeric bounds follow the kernel's first-error order. Canonical computed rendering cannot contain leading zeroes, so that intervening source check has no reachable failing branch here. -/
def firstFittingAttemptError? (policy : NumericTargetPolicy)
    (attempted : StoredNumber) : Option NumericTargetError :=
  match policy.firstAttemptError? attempted with
  | some cause => some cause
  | none =>
      match policy.maxIntegerDigits with
      | some maximum =>
          if maximum < attempted.integerDigitCount then
            some .integerDigitsTooLong
          else
            fittingAfterInteger policy attempted
      | none => fittingAfterInteger policy attempted
where
  fittingAfterInteger (policy : NumericTargetPolicy)
      (attempted : StoredNumber) : Option NumericTargetError :=
    if attempted.unscaled = 0 && !policy.zeroAllowed then
      some .zeroNotAllowed
    else
      match policy.minStoredLength with
      | some minimum =>
          if attempted.render.length < minimum then
            some .storedTextTooShort
          else
            fittingAfterMinLength policy attempted
      | none => fittingAfterMinLength policy attempted
  fittingAfterMinLength (policy : NumericTargetPolicy)
      (attempted : StoredNumber) : Option NumericTargetError :=
    match policy.maxStoredLength with
    | some maximum =>
        if maximum < attempted.render.length then
          some .storedTextTooLong
        else
          fittingAfterMaxLength policy attempted
    | none => fittingAfterMaxLength policy attempted
  fittingAfterMaxLength (policy : NumericTargetPolicy)
      (attempted : StoredNumber) : Option NumericTargetError :=
    match policy.minimum with
    | some minimum =>
        if attempted.amount < minimum then
          some .belowMinimum
        else
          fittingAfterMinimum policy attempted
    | none => fittingAfterMinimum policy attempted
  fittingAfterMinimum (policy : NumericTargetPolicy)
      (attempted : StoredNumber) : Option NumericTargetError :=
    match policy.maximum with
    | some maximum =>
        if maximum < attempted.amount then
          some .aboveMaximum
        else
          none
    | none => none

/-- Apply every reachable fitting-value target check to one stored attempt. -/
def checkAttempt (policy : NumericTargetPolicy)
    (attempted : StoredNumber) : NumericTargetOutcome :=
  match policy.firstFittingAttemptError? attempted with
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

/-- Classify one expression result when the computation explicitly suppresses the assignment-scale warning. Values that fit use the ordinary path unchanged. A no-fit value is rendered through the separate 16-significant-digit compatibility boundary; only the shared prefix can provide a more specific error before the decimal mismatch. -/
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
