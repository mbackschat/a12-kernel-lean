import A12Kernel.Semantics.LegacyCalendarExpression

namespace A12Kernel.Conformance.CalendarExpressions

private def shifted (profile : ModelZone.ConcreteProfile) (unit : DateShiftUnit)
    (year : Int) (month day : Nat) (amount : Int) : Option DateParts := do
  let source ← profile.resolveCalendarLabel? {
    parts := { year, month, day }
    time := { hour := 0, minute := 0, second := 0, valid := by decide } }
  pure (← profile.shiftCalendar? unit source amount).1.parts

-- The retained calendar-expression grid separates arithmetic from the later storage check.
example : [.utc, .europeBerlin].all (fun profile =>
    shifted profile .days 1583 10 16 (-1) == some { year := 1583, month := 10, day := 15 } &&
    shifted profile .months 1583 10 16 (-1) == some { year := 1583, month := 9, day := 16 } &&
    shifted profile .years 1583 10 16 (-1) == some { year := 1582, month := 10, day := 16 } &&
    shifted profile .days 9999 12 31 1 == some { year := 10000, month := 1, day := 1 }) = true := by
  native_decide

-- KF89 distinguishes the year correction from ordinary month-end clamping.
example : [.utc, .europeBerlin].all (fun profile =>
    shifted profile .months 2024 1 31 1 == some { year := 2024, month := 2, day := 29 } &&
    shifted profile .years 2023 2 28 1 == some { year := 2024, month := 2, day := 29 }) = true := by
  native_decide

-- Chained operations consume the inner exact result; month/day mutations do not commute.
example :
    (do
      let source ← ModelZone.ConcreteProfile.europeBerlin.resolveCalendarLabel? {
        parts := { year := 2024, month := 1, day := 30 }
        time := { hour := 0, minute := 0, second := 0, valid := by decide } }
      let (_, month) ← ModelZone.ConcreteProfile.europeBerlin.shiftCalendar? .months source 1
      let (monthDay, _) ← ModelZone.ConcreteProfile.europeBerlin.shiftCalendar? .days month 1
      let (_, day) ← ModelZone.ConcreteProfile.europeBerlin.shiftCalendar? .days source 1
      let (dayMonth, _) ← ModelZone.ConcreteProfile.europeBerlin.shiftCalendar? .months day 1
      pure (monthDay.parts, dayMonth.parts)) =
      some ({ year := 2024, month := 3, day := 1 }, { year := 2024, month := 2, day := 29 }) := by
  native_decide

end A12Kernel.Conformance.CalendarExpressions
