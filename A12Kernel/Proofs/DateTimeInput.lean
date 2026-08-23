import A12Kernel.Elaboration.DateTimeInput

/-! # DateTime stored-input laws

The zone decides the retained **instant** and nothing else: the decoded wall-label components and the
calendar provenance come from the text, so two models differing only in zone agree on everything except
the instant. That separation is what lets a consumer compare stored labels without re-resolving them. -/

namespace A12Kernel

/-- Present-empty stored text is never a formal rejection, whatever the zone. -/
@[simp] theorem dateTimeInput_classify_empty
    (checked : CheckedDateTimeInputField)
    (profile : ModelZone.ConcreteProfile) (zoneId : String)
    (resolved : ModelZone.ConcreteProfile.ofId? zoneId = some profile) :
    checked.classifyStoredForModel zoneId "" = .ok .presentEmpty := by
  simp [CheckedDateTimeInputField.classifyStoredForModel, resolved,
    bind, Except.bind, pure, Except.pure]

/-- An unsupported zone is a **context** error rather than a formal finding, so a model this classifier
cannot serve is never reported as invalid stored data. -/
theorem dateTimeInput_unsupportedZone
    (checked : CheckedDateTimeInputField) (zoneId text : String)
    (unsupported : ModelZone.ConcreteProfile.ofId? zoneId = none) :
    checked.classifyStoredForModel zoneId text =
      .error (.unsupportedZone zoneId) := by
  simp [CheckedDateTimeInputField.classifyStoredForModel, unsupported,
    bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw]

/-- A certified declaration retains the one declarable storage format and its kind, so a consumer never
re-derives which spelling produced the cell. -/
theorem checkedDateTimeInputField_format_declared
    (checked : CheckedDateTimeInputField) :
    DateTimeTargetFormat.ofSource? checked.policy.format = some checked.format ∧
      checked.field.kind = .dateTime :=
  ⟨checked.formatOwned, checked.kindOwned⟩

/-- The date half of the one storage format is the dashed full-Date format, which is what makes the
component parser and the calendar-reality test shared rather than duplicated. -/
@[simp] theorem dateTimeTargetFormat_dateHalf
    (format : DateTimeTargetFormat) :
    format.dateHalf = .yearMonthDayDashes := by
  cases format; rfl

end A12Kernel
