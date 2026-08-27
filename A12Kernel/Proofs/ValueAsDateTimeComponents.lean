import A12Kernel.Elaboration.ValueAsDateTimeWorldComponents
import A12Kernel.Proofs.ValueAsDate

/-! # Checked mixed-component `Time(...)` laws -/

namespace A12Kernel

/-- The zero-component prefix performs no read and delegates fixed omitted zeroes to the resolved arity owner. -/
@[simp] theorem timeComponentPrefix_evaluateWith_empty
    (read : Component → Except Error TimeConstructionComponent) :
    (TimeComponentPrefix.empty : TimeComponentPrefix Component).evaluateWith read =
      .ok (TimeConstructionArity.zero.evaluate .empty .empty .empty) := rfl

/-- A reached, checked digit String contributes the exact natural-number component; no
    truncating numeric operation is introduced by the constructor adapter. -/
@[simp] theorem checkedTimeStringField_classify_value
    (checked : CheckedTimeStringField model) (text : String) (amount : Nat)
    (parsed : parseAsciiNatural? text = some amount) :
    checked.classify (.value (.str text)) = .ok (.value amount) := by
  simp [CheckedTimeStringField.classify,
    CheckedTimeStringField.classifyTimeStringComponent, parsed]
  rfl

/-- A checked extractor cannot retain a token from another constructor position. -/
theorem checkedTimeExtractorField_position_matches
    (checked : CheckedTimeExtractorField model) :
    checked.position.extractor = checked.part := by
  have admitted := checked.admitted
  unfold FlatModel.admitsTimeExtractorField at admitted
  split at admitted <;> simp_all [FlatModel.admitsTimeExtractorComponentField]

/-- A nested temporal expression that produces no DateTime value still follows the
    runtime extractor's numeric-zero rule; only not-given provenance keeps the enclosing
    `Time(...)` component empty. -/
@[simp] theorem valueAsDateTimeTimeOperand_extractComponent_noValue
    (part : TimeNumericPart) (notGiven : Bool) :
    ValueAsDateTimeTimeOperand.extractComponent (.noValue notGiven) part =
      if notGiven then .empty else .value 0 := by
  cases notGiven <;> rfl

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

/-- A formally unavailable partial Date also prevents every world-dependent Time
    component read, so the result is independent of both the document and `World`. -/
theorem valueAsDateTimeWorldComponents_evaluateRaw_date_unavailable
    (checked : CheckedValueAsDateTime model)
    (time : CheckedWorldTimeComponents model)
    (phase : Phase) (world : World) (input : CheckedDocument model)
    (raw : RawCell String) (cause : FormalCause)
    (observed :
      checked.toCheckedValueAsDateSource.observe phase
        (checked.toCheckedValueAsDateSource.checkSourceRaw raw) =
          .unavailable cause) :
    checked.evaluateWorldComponentsRaw time phase world input raw =
      .ok (.unavailable cause) := by
  simpa only [CheckedValueAsDateTime.evaluateWorldComponentsRaw] using
    valueAsDateTime_evaluateTimeOperandRaw_date_unavailable checked phase raw
      (fun _ => do
        let timeResult ← time.evaluate phase world input
        pure timeResult.asDateTimeOperand)
      cause observed

end A12Kernel
