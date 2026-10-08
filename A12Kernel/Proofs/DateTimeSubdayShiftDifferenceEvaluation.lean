import A12Kernel.Elaboration.DateTimeSubdayShiftDifferenceEvaluation

/-! # Checked DateTime sub-day shift/difference laws -/

namespace A12Kernel

/-- A first-position shift cause in computation stops before the direct DateTime operand. -/
theorem checkedDateTimeSubdayShiftDifference_first_unavailable
    (checked : CheckedDateTimeSubdayShiftDifference model)
    (input : CheckedDocument model)
    (cause : FormalCause)
    (position : checked.position = .first)
    (shift :
      checked.shift.evaluate .computation input = .ok (.unavailable cause)) :
    checked.evaluate .computation input = .ok (.unknown cause) := by
  simp [CheckedDateTimeSubdayShiftDifference.evaluate, readTemporalPairWith, bind, Except.bind, pure, Except.pure, Except.mapError, position, shift]

/-- A second-position direct DateTime cause in computation stops before the shifted operand. -/
theorem checkedDateTimeSubdayShiftDifference_second_unavailable
    (checked : CheckedDateTimeSubdayShiftDifference model)
    (input : CheckedDocument model)
    (cause : FormalCause)
    (position : checked.position = .second)
    (other :
      checked.other.readDateTimeDifferenceOperand .computation input =
        .ok (.unavailable cause)) :
    checked.evaluate .computation input = .ok (.unknown cause) := by
  simp [CheckedDateTimeSubdayShiftDifference.evaluate, readTemporalPairWith, bind, Except.bind, pure, Except.pure, Except.mapError, position, other]

/-- A first-position dynamic shift cause in computation stops before the direct DateTime operand. -/
theorem checkedShiftedNowDateTimeDifference_first_unavailable
    (checked : CheckedShiftedNowDateTimeDifference model)
    (world : World) (input : CheckedDocument model)
    (cause : FormalCause)
    (position : checked.position = .first)
    (shift :
      checked.shift.evaluate .computation world input = .ok (.unavailable cause)) :
    checked.evaluate .computation world input = .ok (.unknown cause) := by
  simp [CheckedShiftedNowDateTimeDifference.evaluate, readTemporalPairWith, bind, Except.bind, pure, Except.pure, Except.mapError, position, shift]

/-- A second-position direct DateTime cause in computation stops before the world-dependent shift. -/
theorem checkedShiftedNowDateTimeDifference_second_unavailable
    (checked : CheckedShiftedNowDateTimeDifference model)
    (world : World) (input : CheckedDocument model)
    (cause : FormalCause)
    (position : checked.position = .second)
    (other :
      checked.other.readDateTimeDifferenceOperand .computation input =
        .ok (.unavailable cause)) :
    checked.evaluate .computation world input = .ok (.unknown cause) := by
  simp [CheckedShiftedNowDateTimeDifference.evaluate, readTemporalPairWith, bind, Except.bind, pure, Except.pure, Except.mapError, position, other]

end A12Kernel
