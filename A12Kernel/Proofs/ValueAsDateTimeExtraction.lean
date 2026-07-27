import A12Kernel.Elaboration.ValueAsDateTimeExtraction
import A12Kernel.Proofs.ValueAsDate

/-! # Checked `TimeFromDateTime` laws -/

namespace A12Kernel

/-- A present DateTime projects exactly its retained wall clock; neither exact instant identity nor the Date half enters the result. -/
@[simp] theorem timeFromDateTime_projects_clock
    (instant : Instant) (date : DateParts) (clock : TimeOfDay)
    (basis : DateCalendarBasis) :
    ValueAsDateTimeTimeOperand.ofDateTimeValueObservation
      (.value (.temporal (.dateTime instant date clock basis))) =
        some (.value clock false) := by
  rfl

/-- Generated Date-before-Time evaluation does not read the checked DateTime extraction source after the partial-Date source has already failed formally. -/
theorem valueAsDateTimeExtraction_evaluateRaw_date_unavailable
    (checked : CheckedValueAsDateTimeExtraction model)
    (phase : Phase) (input : CheckedDocument model)
    (raw : RawCell String) (cause : FormalCause)
    (observed :
      checked.construction.toCheckedValueAsDateSource.observe phase
        (checked.construction.toCheckedValueAsDateSource.checkSourceRaw raw) =
          .unavailable cause) :
    checked.evaluateRaw phase input raw = .ok (.unavailable cause) := by
  simpa only [CheckedValueAsDateTimeExtraction.evaluateRaw] using
    valueAsDateTime_evaluateTimeOperandRaw_date_unavailable
      checked.construction phase raw
        (fun _ => checked.readTime phase input) cause observed

/-- The legal sub-day DateTime-shift route retains the same generated Date-before-Time short circuit as direct `TimeFromDateTime`. -/
theorem valueAsDateTimeShiftExtraction_evaluateRaw_date_unavailable
    (checked : CheckedValueAsDateTimeShiftExtraction model)
    (phase : Phase) (input : CheckedDocument model)
    (raw : RawCell String) (cause : FormalCause)
    (observed :
      checked.construction.toCheckedValueAsDateSource.observe phase
        (checked.construction.toCheckedValueAsDateSource.checkSourceRaw raw) =
          .unavailable cause) :
    checked.evaluateRaw phase input raw = .ok (.unavailable cause) := by
  simpa only [CheckedValueAsDateTimeShiftExtraction.evaluateRaw] using
    valueAsDateTime_evaluateTimeOperandRaw_date_unavailable
      checked.construction phase raw
        (fun _ => checked.readShiftedTime phase input) cause observed

/-- The dynamic `Now` shift route also inherits the shared generated Date-before-Time short circuit, so a failed Date side decides without a semantic clock read. -/
theorem valueAsDateTimeNowShiftExtraction_evaluateRaw_date_unavailable
    (checked : CheckedValueAsDateTimeNowShiftExtraction model)
    (phase : Phase) (world : World) (input : CheckedDocument model)
    (raw : RawCell String) (cause : FormalCause)
    (observed :
      checked.construction.toCheckedValueAsDateSource.observe phase
        (checked.construction.toCheckedValueAsDateSource.checkSourceRaw raw) =
          .unavailable cause) :
    checked.evaluateRaw phase world input raw = .ok (.unavailable cause) := by
  simpa only [CheckedValueAsDateTimeNowShiftExtraction.evaluateRaw] using
    valueAsDateTime_evaluateTimeOperandRaw_date_unavailable
      checked.construction phase raw
        (fun _ => checked.readShiftedTime phase world input) cause observed

/-- The checked field-amount route retains the literal route exactly when its numeric operand is fixed. -/
theorem shiftedNumericOperand_fixed
    (profile : ModelZone.ConcreteProfile) (unit : DateTimeSubdayUnit)
    (instant : Instant) (amount : Rat) :
    ValueAsDateTimeTimeOperand.ofShiftedNumericOperand?
        profile unit instant (.value amount .fixed) =
      ValueAsDateTimeTimeOperand.ofShiftedInstant?
        profile unit amount instant := by
  rfl

/-- Arithmetic domain failure remains a present-but-valueless Time operand; it is never reinterpreted as a zero shift. -/
theorem valueAsDateTimeShiftAmount_notEvaluated
    (amount : CheckedTemporalShiftAmount model)
    (phase : Phase) (input : CheckedDocument model)
    (profile : ModelZone.ConcreteProfile)
    (unit : DateTimeSubdayUnit) (instant : Instant)
    (read :
      amount.read phase input = .ok (.ok .notEvaluated)) :
    amount.readShiftedTime phase input profile unit instant =
      .ok (.noValue false) := by
  rw [CheckedTemporalShiftAmount.readShiftedTime, read]
  rfl

/-- Missing provenance on a concrete constructed DateTime is observable as omission polarity without changing its exact instant. -/
theorem valueAsDateTimeResult_equal_self
    (localDateTime : LocalDateTime) (instant : Instant)
    (notGiven : Bool) :
    (ValueAsDateTimeResult.value localDateTime instant notGiven).evalFixedRight
        .equal instant =
      .fired (if notGiven then .omission else .value) := by
  cases notGiven <;> simp [ValueAsDateTimeResult.evalFixedRight,
    TemporalComparisonOp.evalInstant, evalSymmetricComparison,
    TemporalComparisonOp.holdsInstant]

end A12Kernel
