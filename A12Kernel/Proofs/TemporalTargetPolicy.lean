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

end A12Kernel
