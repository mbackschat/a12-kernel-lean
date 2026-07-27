import A12Kernel.Elaboration.TemporalTargetPolicy

/-! # Checked temporal-target policy law -/

namespace A12Kernel

/-- The checked target cannot be the Time kind excluded by this capsule. -/
theorem checkedTemporalTargetPolicy_not_time
    (checked : CheckedTemporalTargetPolicy model) :
    checked.target.kind ≠ .time := by
  intro isTime
  rcases checked.targetSupported with isDate | isDateTime <;>
    simp_all

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
  simp [CheckedFullDateTarget.evaluate, localDate, check, before]
  rfl

end A12Kernel
