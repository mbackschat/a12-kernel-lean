import A12Kernel.Semantics.LegacyCalendarExpression

namespace A12Kernel

/-- A zero mutation retains the chosen instant, including an overlap choice and milliseconds;
it does not resolve the decoded label as a fresh input. -/
theorem calendarShift_zero (profile : ModelZone.ConcreteProfile) (unit : DateShiftUnit)
    (instant : Instant) :
    profile.shiftCalendar? unit instant 0 =
      (profile.calendarLabel? instant).map (fun label => (label, instant)) := by
  cases decoded : profile.calendarLabel? instant <;>
    simp [ModelZone.ConcreteProfile.shiftCalendar?, decoded]

end A12Kernel
