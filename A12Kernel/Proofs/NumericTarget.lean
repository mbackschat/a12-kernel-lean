import A12Kernel.Semantics.NumericTarget

/-! # Numeric target and delta laws -/

namespace A12Kernel

/-- Declaration construction retains every reachable constraint and cannot change the shared scale/signedness summary. -/
theorem numericTargetConstraints_policyConstruction_retains
    (constraints : NumericTargetConstraints) (info : NumField)
    (policy : NumericTargetPolicy)
    (built : constraints.toPolicy? info = some policy) :
    policy.info = info ∧
      policy.minFractionalDigits = constraints.minFractionalDigits ∧
      policy.maxIntegerDigits = constraints.maxIntegerDigits ∧
      policy.zeroAllowed = constraints.zeroAllowed ∧
      policy.minStoredLength = constraints.minStoredLength ∧
      policy.maxStoredLength = constraints.maxStoredLength ∧
      policy.minimum = constraints.minimum ∧
      policy.maximum = constraints.maximum := by
  unfold NumericTargetConstraints.toPolicy? at built
  split at built
  · simp only [Option.some.injEq] at built
    subst policy
    simp
  · simp at built

/-- Arithmetic domain failure becomes the target's own no-value calculation invalidity, not an inherited operand cause. -/
theorem numericTarget_domainFailure_invalidNoValue
    (policy : NumericTargetPolicy) :
    policy.check .domainFailure =
      .supported (.invalidNoValue .calculationValue) := by
  rfl

/-- An inherited computation-read poison retains its exact cause at the target boundary. -/
theorem numericTarget_inheritedPoison_preservesCause
    (policy : NumericTargetPolicy) (cause : FormalCause) :
    policy.check (.poison cause) =
      .supported (.inheritedPoison cause) := by
  rfl

/-- A value whose store-time natural scale exceeds the target maximum is refused by this unsuppressed fragment rather than silently rounded to fit. -/
theorem numericTarget_noFit_failsClosed
    (policy : NumericTargetPolicy) (amount : Rat)
    (naturalScale : Nat) (attempted : StoredNumber)
    (rendered :
      StoredNumber.fromComputed amount policy.minFractionalDigits =
        (naturalScale, attempted))
    (doesNotFit : ¬ naturalScale ≤ policy.info.scale) :
    policy.check (.value amount) =
      .unsupported
        (.fractionalScaleDoesNotFit naturalScale policy.info.scale) := by
  simp [NumericTargetPolicy.check, rendered, doesNotFit]

/-- The universal digit check precedes signedness and retains the full fit-path attempt. -/
theorem numericTarget_digitOverflow_retainsAttempt
    (policy : NumericTargetPolicy) (amount : Rat)
    (naturalScale : Nat) (attempted : StoredNumber)
    (rendered :
      StoredNumber.fromComputed amount policy.minFractionalDigits =
        (naturalScale, attempted))
    (fits : naturalScale ≤ policy.info.scale)
    (tooLong : numericStoredDigitLimit < attempted.digitCount) :
    policy.check (.value amount) =
      .supported (.rejected attempted .totalDigitsTooLong) := by
  simp [NumericTargetPolicy.check, NumericTargetPolicy.checkAttempt,
    NumericTargetPolicy.firstFittingAttemptError?,
    NumericTargetPolicy.firstAttemptError?, rendered, fits, tooLong]

/-- A fitting attempt that passes the complete ordered target check is accepted in its exact stored form. -/
theorem numericTarget_fittingAttempt_accepts
    (policy : NumericTargetPolicy) (amount : Rat)
    (naturalScale : Nat) (attempted : StoredNumber)
    (rendered :
      StoredNumber.fromComputed amount policy.minFractionalDigits =
        (naturalScale, attempted))
    (fits : naturalScale ≤ policy.info.scale)
    (passes : policy.firstFittingAttemptError? attempted = none) :
    policy.check (.value amount) =
      .supported (.accepted attempted) := by
  simp [NumericTargetPolicy.check, NumericTargetPolicy.checkAttempt,
    rendered, fits, passes]

/-- A fitting attempt is rejected with the first error selected by the complete ordered target check. -/
theorem numericTarget_fittingAttempt_rejectsFirstError
    (policy : NumericTargetPolicy) (amount : Rat)
    (naturalScale : Nat) (attempted : StoredNumber)
    (cause : NumericTargetError)
    (rendered :
      StoredNumber.fromComputed amount policy.minFractionalDigits =
        (naturalScale, attempted))
    (fits : naturalScale ≤ policy.info.scale)
    (fails : policy.firstFittingAttemptError? attempted = some cause) :
    policy.check (.value amount) =
      .supported (.rejected attempted cause) := by
  simp [NumericTargetPolicy.check, NumericTargetPolicy.checkAttempt,
    rendered, fits, fails]

/-- Warning suppression does not alter the ordinary branch when the scale-19 stored value fits the target maximum. -/
theorem numericTarget_suppressedFit_eq_check
    (policy : NumericTargetPolicy) (amount : Rat)
    (naturalScale : Nat) (attempted : StoredNumber)
    (rendered :
      StoredNumber.fromComputed amount policy.minFractionalDigits =
        (naturalScale, attempted))
    (fits : naturalScale ≤ policy.info.scale) :
    policy.checkWithScaleWarningSuppressed (.value amount) =
      policy.check (.value amount) := by
  simp [NumericTargetPolicy.checkWithScaleWarningSuppressed,
    NumericTargetPolicy.check, rendered, fits]

/-- A warning-suppressed no-fit attempt with no more specific reduced target error is nevertheless rejected for the scale mismatch. -/
theorem numericTarget_suppressedNoFit_rejects
    (policy : NumericTargetPolicy) (amount : Rat)
    (naturalScale : Nat) (ordinaryAttempt boundedAttempt : StoredNumber)
    (rendered :
      StoredNumber.fromComputed amount policy.minFractionalDigits =
        (naturalScale, ordinaryAttempt))
    (doesNotFit : ¬ naturalScale ≤ policy.info.scale)
    (bounded : StoredNumber.fromComputedBounded amount
      numericComputedNoFitPrecisionLimit = boundedAttempt)
    (noSpecificError :
      policy.firstAttemptError? boundedAttempt = none) :
    policy.checkWithScaleWarningSuppressed (.value amount) =
      .supported
        (.rejected boundedAttempt .suppressedScaleMismatch) := by
  simp [NumericTargetPolicy.checkWithScaleWarningSuppressed, rendered,
    doesNotFit, bounded, noSpecificError]

/-- A reduced target error on the warning-suppressed no-fit attempt takes precedence over the generic scale-mismatch cause. -/
theorem numericTarget_suppressedNoFit_specificErrorPrecedes
    (policy : NumericTargetPolicy) (amount : Rat)
    (naturalScale : Nat) (ordinaryAttempt boundedAttempt : StoredNumber)
    (cause : NumericTargetError)
    (rendered :
      StoredNumber.fromComputed amount policy.minFractionalDigits =
        (naturalScale, ordinaryAttempt))
    (doesNotFit : ¬ naturalScale ≤ policy.info.scale)
    (bounded : StoredNumber.fromComputedBounded amount
      numericComputedNoFitPrecisionLimit = boundedAttempt)
    (specificError :
      policy.firstAttemptError? boundedAttempt = some cause) :
    policy.checkWithScaleWarningSuppressed (.value amount) =
      .supported (.rejected boundedAttempt cause) := by
  simp [NumericTargetPolicy.checkWithScaleWarningSuppressed, rendered,
    doesNotFit, bounded, specificError]

/-- A newly accepted value always produces a VALUE delta carrying its exact stored form. -/
theorem numericTarget_freshAccepted_reports (stored : StoredNumber) :
    (NumericTargetOutcome.accepted stored).projectDelta .empty =
      some (.value stored) := by
  rfl

/-- An accepted value equal in exact coefficient and scale to the prior stored form produces no delta. -/
theorem numericTarget_unchangedStored_silent (stored : StoredNumber) :
    (NumericTargetOutcome.accepted stored).projectDelta (.filled stored) =
      none := by
  simp [NumericTargetOutcome.projectDelta]

/-- A changed exact stored form produces a VALUE delta carrying that new form. -/
theorem numericTarget_changedStored_reports
    (previous stored : StoredNumber) (changed : stored ≠ previous) :
    (NumericTargetOutcome.accepted stored).projectDelta (.filled previous) =
      some (.value stored) := by
  simp [NumericTargetOutcome.projectDelta, changed]

/-- Target rejection is reported unconditionally, including over an empty prior target. -/
theorem numericTarget_rejection_reports
    (attempted : StoredNumber) (cause : NumericTargetError)
    (prior : PriorNumericTarget) :
    (NumericTargetOutcome.rejected attempted cause).projectDelta prior =
      some (.errored attempted cause) := by
  rfl

/-- Clean no-result reports CLEARED exactly when the prior target was filled. -/
theorem numericTarget_noValue_delta_iff_filled
    (prior : PriorNumericTarget) :
    NumericTargetOutcome.noValue.projectDelta prior = some .cleared ↔
      ∃ previous, prior = .filled previous := by
  cases prior <;> simp [NumericTargetOutcome.projectDelta]

/-- Target-local invalidity has the same immediate delta as clean no-result. -/
theorem numericTarget_invalid_delta_eq_noValue
    (cause : NumericTargetInvalidity) (prior : PriorNumericTarget) :
    (NumericTargetOutcome.invalidNoValue cause).projectDelta prior =
      NumericTargetOutcome.noValue.projectDelta prior := by
  rfl

/-- Inherited poison has the same immediate delta as clean no-result. -/
theorem numericTarget_poison_delta_eq_noValue
    (cause : FormalCause) (prior : PriorNumericTarget) :
    (NumericTargetOutcome.inheritedPoison cause).projectDelta prior =
      NumericTargetOutcome.noValue.projectDelta prior := by
  rfl

/-- Clean no-result and target-local invalidity remain different semantic outcomes even when their deltas agree. -/
theorem numericTarget_noValue_ne_invalid
    (invalidity : NumericTargetInvalidity) :
    NumericTargetOutcome.noValue ≠ .invalidNoValue invalidity := by
  intro equality
  cases equality

/-- Clean no-result and inherited poison remain different semantic outcomes even when their deltas agree. -/
theorem numericTarget_noValue_ne_inheritedPoison
    (cause : FormalCause) :
    NumericTargetOutcome.noValue ≠ .inheritedPoison cause := by
  intro equality
  cases equality

/-- Domain invalidity and inherited poison cannot be identified merely because their delta projections agree. -/
theorem numericTarget_invalidity_ne_inheritedPoison
    (invalidity : NumericTargetInvalidity) (cause : FormalCause) :
    NumericTargetOutcome.invalidNoValue invalidity ≠
      .inheritedPoison cause := by
  intro equality
  cases equality

end A12Kernel
