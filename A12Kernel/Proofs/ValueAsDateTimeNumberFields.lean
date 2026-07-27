import A12Kernel.Elaboration.ValueAsDateTimeNumberFields
import A12Kernel.Proofs.ValueAsDate

/-! # Checked Number-field `Time(...)` laws -/

namespace A12Kernel

/-- A formally unavailable partial Date prevents every checked Time component read,
    preserving generated Date-before-Time evaluation. -/
theorem valueAsDateTimeNumberFields_evaluateRaw_date_unavailable
    (checked : CheckedValueAsDateTime model)
    (time : CheckedTimeNumberFields model)
    (phase : Phase) (input : CheckedDocument model)
    (raw : RawCell String) (cause : FormalCause)
    (observed :
      checked.toCheckedValueAsDateSource.observe phase
        (checked.toCheckedValueAsDateSource.checkSourceRaw raw) =
          .unavailable cause) :
    checked.evaluateNumberFieldsRaw time phase input raw =
      .ok (.unavailable cause) := by
  simpa only [CheckedValueAsDateTime.evaluateNumberFieldsRaw] using
    valueAsDateTime_evaluateTimeOperandRaw_date_unavailable checked phase raw
      (fun _ => do
        let timeResult ← time.evaluate phase input
        pure timeResult.asDateTimeOperand)
      cause observed

end A12Kernel
