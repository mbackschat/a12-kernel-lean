import A12Kernel.Elaboration.ValueAsDateTimeComponents
import A12Kernel.Proofs.ValueAsDate

/-! # Checked mixed-component `Time(...)` laws -/

namespace A12Kernel

/-- A checked extractor cannot retain a token from another constructor position. -/
theorem checkedTimeExtractorField_position_matches
    (checked : CheckedTimeExtractorField model) :
    checked.position.extractor = checked.part := by
  have admitted := checked.admitted
  unfold FlatModel.admitsTimeExtractorField at admitted
  split at admitted <;> simp_all

/-- A formally unavailable partial Date prevents every checked Time component read,
    preserving generated Date-before-Time evaluation. -/
theorem valueAsDateTimeComponents_evaluateRaw_date_unavailable
    (checked : CheckedValueAsDateTime model)
    (time : CheckedTimeComponents model)
    (phase : Phase) (input : CheckedDocument model)
    (raw : RawCell String) (cause : FormalCause)
    (observed :
      checked.toCheckedValueAsDateSource.observe phase
        (checked.toCheckedValueAsDateSource.checkSourceRaw raw) =
          .unavailable cause) :
    checked.evaluateComponentsRaw time phase input raw =
      .ok (.unavailable cause) := by
  simpa only [CheckedValueAsDateTime.evaluateComponentsRaw] using
    valueAsDateTime_evaluateTimeOperandRaw_date_unavailable checked phase raw
      (fun _ => do
        let timeResult ← time.evaluate phase input
        pure timeResult.asDateTimeOperand)
      cause observed

end A12Kernel
