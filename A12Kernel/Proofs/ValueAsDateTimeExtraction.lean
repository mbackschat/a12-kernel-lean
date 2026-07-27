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
        some (.value clock) := by
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

end A12Kernel
