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

end A12Kernel
