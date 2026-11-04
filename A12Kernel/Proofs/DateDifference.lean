import A12Kernel.Proofs.CalendarArithmetic
import A12Kernel.Semantics.DateDifference

/-! # Checked calendar-difference laws -/

namespace A12Kernel

/-- Exchanging the two Dates negates the completed-period count, because both read as exact instants in one zone and the instant counters are antisymmetric. -/
theorem dateDifferenceUnit_betweenIn_swap (unit : DateDifferenceUnit)
    (profile : ModelZone.ConcreteProfile) (first second : DateParts) :
    unit.betweenIn? profile second first =
      (unit.betweenIn? profile first second).map (-·) := by
  unfold DateDifferenceUnit.betweenIn?
  cases resolvedFirst : profile.resolveCalendarLabel? (CalendarLabel.midnight first) <;>
    cases resolvedSecond : profile.resolveCalendarLabel? (CalendarLabel.midnight second) <;>
    simp_all
  next start finish =>
    cases unit
    · exact (ModelZone.ConcreteProfile.differenceResolvedInMonths_swap profile start finish).symm
    · exact (ModelZone.ConcreteProfile.differenceResolvedInYears_swap profile start finish).symm

/-- A left formal cause wins before any empty/default branch is considered, unless the other operand is a constant without an instant, which fails first. -/
theorem dateDifferenceOperand_unavailable_left
    (profile : ModelZone.ConcreteProfile) (unit : DateDifferenceUnit) (cause : FormalCause)
    (right : DateDifferenceOperand) (reached : right ≠ .noInstantConstant) :
    DateDifferenceOperand.evaluate profile unit (.unavailable cause) right =
      .ok (.unknown cause) := by
  cases right <;> first | exact absurd rfl reached | rfl

/-- Empty supplies symmetric numeric zero without consulting the other present operand. -/
theorem dateDifferenceOperand_empty_zero
    (profile : ModelZone.ConcreteProfile) (unit : DateDifferenceUnit) (parts : DateParts) :
    DateDifferenceOperand.evaluate profile unit .empty (.value parts) =
      .ok (.value 0 .both) := by
  rfl

/-- Two decoded values delegate exactly to the completed-period count on their model-zone midnights. -/
theorem dateDifferenceOperand_values_delegate
    (profile : ModelZone.ConcreteProfile) (unit : DateDifferenceUnit) (first second : DateParts)
    (value : Int) (counted : unit.betweenIn? profile first second = some value) :
    DateDifferenceOperand.evaluate profile unit (.value first) (.value second) =
      .ok (.value value .fixed) := by
  simp only [DateDifferenceOperand.evaluate, counted]
  rfl

/-- A date constant the model zone gives no instant fails the evaluation in either operand position, whatever the other operand holds (spec/05 §1). -/
theorem dateDifferenceOperand_noInstantConstant_fails
    (profile : ModelZone.ConcreteProfile) (unit : DateDifferenceUnit)
    (other : DateDifferenceOperand) :
    DateDifferenceOperand.evaluate profile unit .noInstantConstant other =
        .error .constantHasNoInstant ∧
      DateDifferenceOperand.evaluate profile unit other .noInstantConstant =
        .error .constantHasNoInstant := by
  cases other <;> exact ⟨rfl, rfl⟩

/-- A left formal cause wins before day-difference empty substitution or calendar support is consulted, unless the other operand is a constant without an instant, which fails first. -/
theorem calendarDayDifferenceOperand_unavailable_left
    (profile : ModelZone.ConcreteProfile) (cause : FormalCause)
    (right : CalendarDayDifferenceOperand) (reached : right ≠ .noInstantConstant) :
    CalendarDayDifferenceOperand.evaluate profile (.unavailable cause) right =
      .ok (.unknown cause) := by
  cases right <;> first | exact absurd rfl reached | rfl

/-- A date constant the model zone gives no instant fails the day difference in either operand position, whatever the other operand holds (spec/05 §1). -/
theorem calendarDayDifferenceOperand_noInstantConstant_fails
    (profile : ModelZone.ConcreteProfile) (other : CalendarDayDifferenceOperand) :
    CalendarDayDifferenceOperand.evaluate profile .noInstantConstant other =
        .error .constantHasNoInstant ∧
      CalendarDayDifferenceOperand.evaluate profile other .noInstantConstant =
        .error .constantHasNoInstant := by
  cases other <;> exact ⟨rfl, rfl⟩

/-- Empty supplies symmetric zero even when the other day operand lies outside the current concrete calendar fragment. -/
theorem calendarDayDifferenceOperand_empty_unsupported_zero
    (profile : ModelZone.ConcreteProfile) :
    CalendarDayDifferenceOperand.evaluate profile .empty .unsupportedCalendar =
      .ok (.value 0 .both) := by
  rfl

/-- Two resolved day operands delegate exactly to the selected profile without re-resolving either local label. -/
theorem calendarDayDifferenceOperand_values_delegate
    (profile : ModelZone.ConcreteProfile)
    (first : CalendarLabel) (firstInstant : Instant)
    (second : CalendarLabel) (secondInstant : Instant) (days : Int)
    (evaluated : profile.differenceResolvedInDays? firstInstant secondInstant = some days) :
    CalendarDayDifferenceOperand.evaluate profile
        (.value first firstInstant) (.value second secondInstant) =
      .ok (.value days .fixed) := by
  simp only [CalendarDayDifferenceOperand.evaluate, evaluated]
  rfl

end A12Kernel
