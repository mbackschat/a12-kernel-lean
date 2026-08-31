import A12Kernel.Elaboration.TemporalTargetPolicy

/-! # Checked temporal-target policy law -/

namespace A12Kernel

/-- The model zone is observed directly from the same checked model, not copied into or inferred from the field format. -/
@[simp] theorem checkedTemporalTargetPolicy_timeZoneId
    (checked : CheckedTemporalTargetPolicy model) :
    checked.timeZoneId = model.timeZoneId := rfl

/-- The optional pre-1900 branch retains the renderer's exact attempted stored form. -/
theorem fullDateTarget_evaluate_pre1900
    (target : CheckedFullDateTarget model)
    (instant : Instant) (date : FullDate)
    (localDate : target.profile.localDate? instant = some date)
    (check : target.checked.policy.youngerThan1900Check = true)
    (before : date.before1900 = true) :
    target.evaluate (.value instant) =
      .ok (.errored (target.format.render date) .before1900) := by
  have before' :
      date.civil.Before FullDate.year1900Start.civil := by
    simpa [FullDate.before1900, FullDate.before] using before
  simp [CheckedFullDateTarget.evaluate, localDate,
    CheckedFullDateTarget.evaluateCivil, check, before',
    FullDateTargetFormat.render]
  rfl

/-- Without the optional pre-1900 policy, a real civil result below the universal Date floor retains the renderer's exact attempted stored form. -/
theorem fullDateTarget_evaluateCivil_beforeGregorianFloor
    (target : CheckedFullDateTarget model) (date : CivilDate)
    (noAdditionalCheck :
      target.checked.policy.youngerThan1900Check = false)
    (beforeFloor : date.Before CivilDate.gregorianFloor) :
    target.evaluateCivil date =
      .errored (target.format.renderCivil date) .beforeGregorianFloor := by
  simp [CheckedFullDateTarget.evaluateCivil, noAdditionalCheck,
    beforeFloor]

/-- Every executable computed-Date target carries the FULL-precision authoring certificate. -/
@[simp] theorem checkedFullDateTarget_precisionFull
    (target : CheckedFullDateTarget model) :
    target.checked.policy.partialMode = .full :=
  target.precisionFull

/-- DateTime rendering uses the local wall label selected from the exact input instant; no caller-supplied label or host zone can replace it. -/
theorem dateTimeTarget_evaluate_value
    (target : CheckedDateTimeTarget model)
    (instant : Instant) (dateTime : LocalDateTime)
    (decoded :
      target.profile.localDateTime? instant = some dateTime) :
    target.evaluate (.value instant) =
      .ok (.accepted (target.format.render dateTime)) := by
  simp [CheckedDateTimeTarget.evaluate, decoded]
  rfl

/-- **A yearless target's stored text does not depend on the year.** Two dates sharing a month and a
day render identically however far apart their years are, which is the whole content of the measured
rule that a declared Base Year gates admission and contributes nothing to the store. A carrier that
completed the rendering from the Base Year, or from the constant's own year, would satisfy every
year-leading fixture and fail this. -/
theorem omittedComponentDateFormat_yearless_renderCivilText_yearIrrelevant
    (format : OmittedComponentDateFormat) (yearless : format.needsBaseYear = true)
    (left right : CivilDate)
    (sameMonth : left.parts.month = right.parts.month)
    (sameDay : left.parts.day = right.parts.day) :
    format.renderCivilText left = format.renderCivilText right := by
  cases format <;> simp_all [OmittedComponentDateFormat.needsBaseYear,
    OmittedComponentDateFormat.renderCivilText]

/-- The Base Year is consumed by the certificate and nowhere else: a checked component-omitting
target can exist for a yearless format only in a model that declares one. Stated as the contrapositive
a consumer actually needs — no Base Year, no yearless target. -/
theorem checkedOmittedComponentDateTarget_yearless_hasBaseYear
    {model : FlatModel} (target : CheckedOmittedComponentDateTarget model)
    (yearless : target.format.needsBaseYear = true) :
    model.hasBaseYear = true := by
  have := target.baseYearWhenYearless
  simp [yearless] at this
  exact this

end A12Kernel
