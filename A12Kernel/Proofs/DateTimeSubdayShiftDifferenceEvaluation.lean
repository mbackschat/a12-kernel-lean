import A12Kernel.Elaboration.DateTimeSubdayShiftDifferenceEvaluation

/-! # Checked DateTime sub-day shift/difference laws -/

namespace A12Kernel

/-- A first-position shift cause stops before the direct DateTime operand. -/
theorem checkedDateTimeSubdayShiftDifference_first_unavailable
    (checked : CheckedDateTimeSubdayShiftDifference model)
    (phase : Phase) (input : CheckedDocument model)
    (cause : FormalCause)
    (position : checked.position = .first)
    (shift :
      checked.shift.evaluate phase input = .ok (.unavailable cause)) :
    checked.evaluate phase input = .ok (.unknown cause) := by
  simp [CheckedDateTimeSubdayShiftDifference.evaluate, position, shift]

/-- A second-position direct DateTime cause stops before the shifted operand. -/
theorem checkedDateTimeSubdayShiftDifference_second_unavailable
    (checked : CheckedDateTimeSubdayShiftDifference model)
    (phase : Phase) (input : CheckedDocument model)
    (cause : FormalCause)
    (position : checked.position = .second)
    (other :
      checked.other.readDateTimeDifferenceOperand phase input =
        .ok (.unavailable cause)) :
    checked.evaluate phase input = .ok (.unknown cause) := by
  simp [CheckedDateTimeSubdayShiftDifference.evaluate, position, other]

/-- A first-position dynamic shift cause stops before the direct DateTime operand. -/
theorem checkedShiftedNowDateTimeDifference_first_unavailable
    (checked : CheckedShiftedNowDateTimeDifference model)
    (phase : Phase) (world : World) (input : CheckedDocument model)
    (cause : FormalCause)
    (position : checked.position = .first)
    (shift :
      checked.shift.evaluate phase world input = .ok (.unavailable cause)) :
    checked.evaluate phase world input = .ok (.unknown cause) := by
  simp [CheckedShiftedNowDateTimeDifference.evaluate, position, shift]

/-- A second-position direct DateTime cause stops before the world-dependent shift. -/
theorem checkedShiftedNowDateTimeDifference_second_unavailable
    (checked : CheckedShiftedNowDateTimeDifference model)
    (phase : Phase) (world : World) (input : CheckedDocument model)
    (cause : FormalCause)
    (position : checked.position = .second)
    (other :
      checked.other.readDateTimeDifferenceOperand phase input =
        .ok (.unavailable cause)) :
    checked.evaluate phase world input = .ok (.unknown cause) := by
  simp [CheckedShiftedNowDateTimeDifference.evaluate, position, other]

end A12Kernel
