import A12Kernel.Elaboration.DateTimeDayShiftEvaluation
import A12Kernel.Proofs.BerlinLegacyCalendarArithmetic

/-! # Checked DateTime calendar-day shift laws -/

namespace A12Kernel

/-- A source-side unknown result decides the shared calendar-day observation before any amount reader can run. -/
@[simp] theorem dateTimeDayShiftObservation_unknown
    (profile : ModelZone.ConcreteProfile) (sourceField : FieldId)
    (readAmount : Unit →
      Except Fault
        (Except NumericValidationUnavailable NumericArithmeticOutcome))
    (mapFault : DateTimeDayShiftFault → Fault) (cause : FormalCause) :
    CheckedDateTimeDayShift.evaluateObservation profile sourceField
        (.unknown cause) readAmount mapFault =
      .ok (.unavailable cause) := by
  rfl

/-- Source-side poison likewise decides the shared calendar-day observation before any amount reader can run. -/
@[simp] theorem dateTimeDayShiftObservation_poison
    (profile : ModelZone.ConcreteProfile) (sourceField : FieldId)
    (readAmount : Unit →
      Except Fault
        (Except NumericValidationUnavailable NumericArithmeticOutcome))
    (mapFault : DateTimeDayShiftFault → Fault) (cause : FormalCause) :
    CheckedDateTimeDayShift.evaluateObservation profile sourceField
        (.poison cause) readAmount mapFault =
      .ok (.unavailable cause) := by
  rfl

/-- An empty source reaches the caller-supplied amount reader, whose formal cause remains the shared result. -/
theorem dateTimeDayShiftObservation_empty_formal
    (profile : ModelZone.ConcreteProfile) (sourceField : FieldId)
    (readAmount : Unit →
      Except Fault
        (Except NumericValidationUnavailable NumericArithmeticOutcome))
    (mapFault : DateTimeDayShiftFault → Fault) (cause : FormalCause)
    (amount : readAmount () = .ok (.error (.formal cause))) :
    CheckedDateTimeDayShift.evaluateObservation profile sourceField
        .empty readAmount mapFault =
      .ok (.unavailable cause) := by
  rw [CheckedDateTimeDayShift.evaluateObservation, amount]
  rfl

/-- A reached exact zero amount preserves the already selected DateTime instant under
    both admitted profiles; an ambiguous Berlin label is never re-resolved. -/
@[simp] theorem checkedDateTimeDayShift_applyAmount_zero
    (checked : CheckedDateTimeDayShift model)
    (sourceLocal : LocalDateTime) (sourceInstant : Instant) :
    checked.applyAmount sourceLocal sourceInstant
        (.value 0 .fixed) =
      .ok (.value sourceLocal sourceInstant false) := by
  have offsetZero : temporalShiftAmountToInt32 0 = 0 := by
    decide
  change CheckedDateTimeDayShift.applyProfileAmount
    checked.profile sourceLocal sourceInstant (.value 0 .fixed) =
      .ok (.value sourceLocal sourceInstant false)
  simp only [CheckedDateTimeDayShift.applyProfileAmount.eq_def]
  rw [offsetZero]
  rfl

/-- A reached formal DateTime source decides the generated source-before-amount
    evaluation without any hypothesis about the amount or its document cell. -/
theorem checkedDateTimeDayShift_source_unavailable
    (checked : CheckedDateTimeDayShift model)
    (phase : Phase) (input : CheckedDocument model)
    (cell : CheckedCell) (cause : FormalCause)
    (read :
      input.read { field := checked.source.id, path := [] } = .ok cell)
    (observed : observeCell phase cell = .unknown cause) :
    checked.evaluate phase input = .ok (.unavailable cause) := by
  have cellResult :
      checked.evaluateCell phase input cell =
        .ok (.unavailable cause) := by
    rw [CheckedDateTimeDayShift.evaluateCell, observed]
    exact dateTimeDayShiftObservation_unknown _ _ _ _ _
  simp [CheckedDateTimeDayShift.evaluate, read, cellResult,
    Except.mapError, bind, Except.bind]

/-- An empty DateTime source still reaches the amount, whose formal cause remains
    visible instead of being replaced by ordinary source missingness. -/
theorem checkedDateTimeDayShift_empty_reaches_amount
    (checked : CheckedDateTimeDayShift model)
    (phase : Phase) (input : CheckedDocument model)
    (cell : CheckedCell) (cause : FormalCause)
    (read :
      input.read { field := checked.source.id, path := [] } = .ok cell)
    (observed : observeCell phase cell = .empty)
    (amount :
      checked.amount.read phase input =
        .ok (.error (.formal cause))) :
    checked.evaluate phase input = .ok (.unavailable cause) := by
  have cellResult :
      checked.evaluateCell phase input cell =
        .ok (.unavailable cause) := by
    rw [CheckedDateTimeDayShift.evaluateCell, observed]
    apply dateTimeDayShiftObservation_empty_formal
    rw [amount]
    rfl
  simp [CheckedDateTimeDayShift.evaluate, read, cellResult,
    Except.mapError, bind, Except.bind]

/-- A reached inner formal cause decides nested generated evaluation before the outer
    DateTime day amount is read. -/
theorem checkedDateTimeDayShift_evaluateThen_inner_unavailable
    (checked : CheckedDateTimeDayShift model)
    (nextAmount : CheckedTemporalShiftAmount model)
    (phase : Phase) (input : CheckedDocument model)
    (cause : FormalCause)
    (inner :
      checked.evaluate phase input = .ok (.unavailable cause)) :
    checked.evaluateThen nextAmount phase input =
      .ok (.unavailable cause) := by
  simp [CheckedDateTimeDayShift.evaluateThen, inner,
    CheckedDateTimeDayShift.evaluateResult,
    CheckedDateTimeDayShift.evaluateProfileResult]

/-- A formally unavailable dynamic day amount remains the exact result once this
    execution's world instant has decoded under the checked profile. -/
theorem checkedNowDateTimeDayShift_formal_amount
    (checked : CheckedNowDateTimeDayShift model)
    (phase : Phase) (world : World) (input : CheckedDocument model)
    (sourceLocal : LocalDateTime) (cause : FormalCause)
    (decoded : checked.profile.localDateTime? world.now = some sourceLocal)
    (amount :
      checked.amount.read phase input =
        .ok (.error (.formal cause))) :
    checked.evaluate phase world input =
      .ok (.unavailable cause) := by
  simp [CheckedNowDateTimeDayShift.evaluate, decoded,
    CheckedDateTimeDayShift.evaluateProfileResult, amount]

/-- A fixed zero dynamic day amount preserves the supplied world's exact instant
    instead of re-resolving its decoded label. -/
theorem checkedNowDateTimeDayShift_zero
    (checked : CheckedNowDateTimeDayShift model)
    (phase : Phase) (world : World) (input : CheckedDocument model)
    (sourceLocal : LocalDateTime)
    (decoded : checked.profile.localDateTime? world.now = some sourceLocal)
    (amount :
      checked.amount.read phase input =
        .ok (.ok (.value 0 .fixed))) :
    checked.evaluate phase world input =
      .ok (.value sourceLocal world.now false) := by
  have offsetZero : temporalShiftAmountToInt32 0 = 0 := by
    decide
  rw [CheckedNowDateTimeDayShift.evaluate, decoded]
  simp only [CheckedDateTimeDayShift.evaluateProfileResult, amount]
  have applied :
      CheckedDateTimeDayShift.applyProfileAmount checked.profile
          sourceLocal world.now (.value 0 .fixed) =
        .ok (.value sourceLocal world.now false) := by
    simp only [CheckedDateTimeDayShift.applyProfileAmount.eq_def]
    rw [offsetZero]
    rfl
  simp only [CheckedDateTimeDayShift.applyProfileResultAmount.eq_def,
    applied, ValueAsDateTimeResult.inheritNotGiven]
  rfl

/-- A reached inner formal cause decides dynamic two-day evaluation before the outer
    amount is read. -/
theorem checkedNowDateTimeDayShift_evaluateThen_inner_unavailable
    (checked : CheckedNowDateTimeDayShift model)
    (nextAmount : CheckedTemporalShiftAmount model)
    (phase : Phase) (world : World) (input : CheckedDocument model)
    (cause : FormalCause)
    (inner :
      checked.evaluate phase world input = .ok (.unavailable cause)) :
    checked.evaluateThen nextAmount phase world input =
      .ok (.unavailable cause) := by
  simp [CheckedNowDateTimeDayShift.evaluateThen, inner,
    CheckedDateTimeDayShift.evaluateProfileResult]

/-- Cause-free inner no-value reaches the outer amount and retains its formal cause. -/
theorem checkedNowDateTimeDayShift_evaluateThen_noValue_reaches_amount
    (checked : CheckedNowDateTimeDayShift model)
    (nextAmount : CheckedTemporalShiftAmount model)
    (phase : Phase) (world : World) (input : CheckedDocument model)
    (notGiven : Bool) (cause : FormalCause)
    (inner :
      checked.evaluate phase world input = .ok (.noValue notGiven))
    (amount :
      nextAmount.read phase input =
        .ok (.error (.formal cause))) :
    checked.evaluateThen nextAmount phase world input =
      .ok (.unavailable cause) := by
  simp [CheckedNowDateTimeDayShift.evaluateThen, inner,
    CheckedDateTimeDayShift.evaluateProfileResult, amount]

/-- A zero outer day amount preserves the inner exact instant and omission provenance. -/
theorem checkedNowDateTimeDayShift_evaluateThen_zero
    (checked : CheckedNowDateTimeDayShift model)
    (nextAmount : CheckedTemporalShiftAmount model)
    (phase : Phase) (world : World) (input : CheckedDocument model)
    (sourceLocal : LocalDateTime) (sourceInstant : Instant)
    (notGiven : Bool)
    (inner :
      checked.evaluate phase world input =
        .ok (.value sourceLocal sourceInstant notGiven))
    (amount :
      nextAmount.read phase input =
        .ok (.ok (.value 0 .fixed))) :
    checked.evaluateThen nextAmount phase world input =
      .ok (.value sourceLocal sourceInstant notGiven) := by
  have offsetZero : temporalShiftAmountToInt32 0 = 0 := by
    decide
  rw [CheckedNowDateTimeDayShift.evaluateThen, inner]
  simp only [CheckedDateTimeDayShift.evaluateProfileResult, amount]
  have applied :
      CheckedDateTimeDayShift.applyProfileAmount checked.profile
          sourceLocal sourceInstant (.value 0 .fixed) =
        .ok (.value sourceLocal sourceInstant false) := by
    simp only [CheckedDateTimeDayShift.applyProfileAmount.eq_def]
    rw [offsetZero]
    rfl
  simp only [CheckedDateTimeDayShift.applyProfileResultAmount.eq_def,
    applied, ValueAsDateTimeResult.inheritNotGiven]
  cases notGiven <;> rfl

end A12Kernel
