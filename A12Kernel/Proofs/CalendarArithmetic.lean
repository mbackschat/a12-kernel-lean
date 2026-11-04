import A12Kernel.Semantics.CalendarArithmetic

/-! # Model-zone completed-period laws

The sign laws are proved once at the shared exact-instant wrapper and specialized to months and years. They hold for every concrete profile and claim no Kernel correspondence by themselves.
-/

namespace A12Kernel.ModelZone.ConcreteProfile

/-- A zero shift returns its source unchanged; an ambiguous source label is never resolved again. -/
@[simp] theorem shiftCalendar_zero (profile : ConcreteProfile) (unit : DateShiftUnit)
    (instant : Instant) :
    profile.shiftCalendar? unit instant 0 =
      (profile.calendarLabel? instant).map fun label => (label, instant) := by
  cases label : profile.calendarLabel? instant <;> simp [shiftCalendar?, label]

/-- Identical operands are zero periods apart, whatever the forward count. -/
@[simp] theorem signedWholePeriods_self (forward : Instant → Instant → Option Nat)
    (instant : Instant) : signedWholePeriods? forward instant instant = some 0 := by
  simp [signedWholePeriods?]

/-- The exact-instant sign wrapper is antisymmetric for every forward count. -/
theorem signedWholePeriods_swap (forward : Instant → Instant → Option Nat)
    (first second : Instant) :
    (signedWholePeriods? forward first second).map (-·) =
      signedWholePeriods? forward second first := by
  by_cases before : first.epochMillis < second.epochMillis
  · have notAfter : ¬second.epochMillis < first.epochMillis := by omega
    simp [signedWholePeriods?, before, notAfter, Function.comp_def]
  · by_cases after : second.epochMillis < first.epochMillis
    · simp [signedWholePeriods?, before, after, Function.comp_def]
    · simp [signedWholePeriods?, before, after]

theorem differenceResolvedInMonths_swap (profile : ConcreteProfile) (first second : Instant) :
    (profile.differenceResolvedInMonths? first second).map (-·) =
      profile.differenceResolvedInMonths? second first :=
  signedWholePeriods_swap profile.wholeMonthsForward? first second

theorem differenceResolvedInYears_swap (profile : ConcreteProfile) (first second : Instant) :
    (profile.differenceResolvedInYears? first second).map (-·) =
      profile.differenceResolvedInYears? second first :=
  signedWholePeriods_swap profile.wholeYearsForward? first second

end A12Kernel.ModelZone.ConcreteProfile
