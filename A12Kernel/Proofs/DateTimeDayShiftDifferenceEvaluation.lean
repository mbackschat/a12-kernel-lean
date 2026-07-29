import A12Kernel.Elaboration.DateTimeDayShiftDifferenceEvaluation

/-! # Checked DateTime day-shift difference laws -/

namespace A12Kernel

/-- A first-position shift cause stops before the direct DateTime operand. -/
theorem checkedDateTimeDayShiftDifference_first_unavailable
    (checked : CheckedDateTimeDayShiftDifference model)
    (phase : Phase) (input : CheckedDocument model)
    (cause : FormalCause)
    (position : checked.position = .first)
    (shift :
      checked.shift.evaluate phase input = .ok (.unavailable cause)) :
    checked.evaluate phase input = .ok (.unknown cause) := by
  simp [CheckedDateTimeDayShiftDifference.evaluate, position, shift]

/-- A second-position direct DateTime cause stops before the shift operand. -/
theorem checkedDateTimeDayShiftDifference_second_unavailable
    (checked : CheckedDateTimeDayShiftDifference model)
    (phase : Phase) (input : CheckedDocument model)
    (cause : FormalCause)
    (position : checked.position = .second)
    (other :
      checked.other.readCalendarDayOperand phase input =
        .ok (.unavailable cause)) :
    checked.evaluate phase input = .ok (.unknown cause) := by
  simp [CheckedDateTimeDayShiftDifference.evaluate, position, other]

/-- Both operands select the same concrete profile because they were checked against
    one model zone id. -/
theorem checkedDateTimeDayShiftDifference_profiles_eq
    (checked : CheckedDateTimeDayShiftDifference model) :
    checked.shift.profile = checked.other.profile := by
  have selected :
      some checked.shift.profile = some checked.other.profile :=
    checked.shift.profileMatches.symm.trans checked.other.profileMatches
  exact Option.some.inj selected

end A12Kernel
