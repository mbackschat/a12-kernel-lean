import A12Kernel.Semantics.BerlinLegacyCalendarArithmetic
import A12Kernel.Semantics.DateTimeDayDifference

/-! # Model-zone calendar shift and completed-period locks (kernel 31.1.1)

These cases separate the proleptic calendar and the source-offset preference of `ZonedDateTime` shifts from the 30.8.1 hybrid stepping and compute-time resolution (spec/05 §2.3, §2.4, §2.7, §5). Calendar-only rows hold under UTC and Berlin alike (a12-dmkits `ConstructedDateCalendarDiffTest`, `supportedGmtAndBerlinShareTheProlepticCalendar`); the repeated-midnight rows are Berlin-only (`ConstructedDateInstantDiffTest`, `WallDayArithmeticDiffTest`).
-/

namespace A12Kernel.Conformance.BerlinLegacyCalendarArithmetic

open A12Kernel

private abbrev Profile := ModelZone.ConcreteProfile

/-- A proleptic wall label; a gap label resolves one gap later and an overlap label at its earlier offset. -/
private structure Wall where
  year : Int
  month : Nat
  day : Nat
  hour : Nat := 0
  minute : Nat := 0
  second : Nat := 0

private def Wall.instant? (wall : Wall) (profile : Profile) : Option Instant := do
  let time ← TimeOfDay.ofHms? wall.hour wall.minute wall.second
  profile.resolveCalendarLabel? { parts := { year := wall.year, month := wall.month, day := wall.day }, time }

private def Wall.shifted? (wall : Wall) (profile : Profile) (unit : DateShiftUnit)
    (amount : Int) : Option Instant := do
  pure (← profile.shiftCalendar? unit (← wall.instant? profile) amount).2

/-- Whether shifting `source` freshly resolved lands on the instant of `target` freshly resolved. -/
private def lands (profile : Profile) (source : Wall) (unit : DateShiftUnit)
    (amount : Int) (target : Wall) : Bool :=
  match source.shifted? profile unit amount, target.instant? profile with
  | some landing, some expected => landing == expected
  | _, _ => false

private def months? (profile : Profile) (first second : Wall) : Option Int := do
  profile.differenceResolvedInMonths? (← first.instant? profile) (← second.instant? profile)

private def years? (profile : Profile) (first second : Wall) : Option Int := do
  profile.differenceResolvedInYears? (← first.instant? profile) (← second.instant? profile)

private def days? (profile : Profile) (first second : Wall) : Option Int := do
  profile.differenceResolvedInDays? (← first.instant? profile) (← second.instant? profile)

private def bothProfiles (check : Profile → Bool) : Bool :=
  check .utc && check .europeBerlin

/- `AddYears` maps the last day of February to the last day of February, `AddMonths` clamps (spec/05 §2.3; a12-dmkits `DateArithmeticDiffTest` locks the February row). -/
example :
    bothProfiles (fun p =>
      lands p { year := 1999, month := 2, day := 28 } .years 1 { year := 2000, month := 2, day := 29 } &&
      !lands p { year := 1999, month := 2, day := 28 } .years 1 { year := 2000, month := 2, day := 28 } &&
      lands p { year := 2011, month := 2, day := 28 } .months 12 { year := 2012, month := 2, day := 28 } &&
      lands p { year := 2008, month := 1, day := 31 } .months 1 { year := 2008, month := 2, day := 29 }) = true := by
  native_decide

/- Completed months truncate toward zero in both directions (spec/05 §2.4). The reverse row follows from the sign rule. Unmeasured on 31.1.1. -/
example :
    bothProfiles (fun p =>
      months? p { year := 2010, month := 1, day := 31 } { year := 2010, month := 3, day := 30 } == some 1 &&
      months? p { year := 2010, month := 3, day := 30 } { year := 2010, month := 1, day := 31 } == some (-1)) = true := by
  native_decide

/- Pre-cutover constructed dates step proleptically (spec/05 §2.7; `aPreCutoverConstructionStepsProlepticallyInEveryLegalDateConsumerFamily`): one day from 1500-02-28 is 1 March, one year keeps 28 February, and 365 days separate the two February 28ths. The month row is derived from the same account: 1500-02-28 plus one month is 28 March, not the 29 March the hybrid calendar's February 29 would give. Unmeasured on 31.1.1. -/
example :
    bothProfiles (fun p =>
      lands p { year := 1500, month := 2, day := 28 } .days 1 { year := 1500, month := 3, day := 1 } &&
      lands p { year := 1500, month := 2, day := 28 } .years 1 { year := 1501, month := 2, day := 28 } &&
      lands p { year := 1500, month := 2, day := 28 } .months 1 { year := 1500, month := 3, day := 28 } &&
      days? p { year := 1500, month := 2, day := 28 } { year := 1500, month := 3, day := 1 } == some 1 &&
      days? p { year := 1500, month := 2, day := 28 } { year := 1501, month := 2, day := 28 } == some 365) = true := by
  native_decide

/- The ten days of October 1582 are ordinary: 4 to 15 October is 11 days and 4 October plus 11 days is 15 October (`constructedDatesCountTheFormerCutoverDays`). -/
example :
    bothProfiles (fun p =>
      days? p { year := 1582, month := 10, day := 4 } { year := 1582, month := 10, day := 15 } == some 11 &&
      lands p { year := 1582, month := 10, day := 4 } .days 11 { year := 1582, month := 10, day := 15 }) = true := by
  native_decide

/- Month and year shifts ignore the former cutover: from 1582-09-10 one month does not land on 20 October, and from 1581-10-10 one year does not either (`monthAndYearArithmeticIgnoresTheFormerCutover`, CUTOVER_ADD_MONTH and CUTOVER_ADD_YEAR silent). The exact landings, 10 October of each, are derived. Unmeasured on 31.1.1. -/
example :
    bothProfiles (fun p =>
      !lands p { year := 1582, month := 9, day := 10 } .months 1 { year := 1582, month := 10, day := 20 } &&
      lands p { year := 1582, month := 9, day := 10 } .months 1 { year := 1582, month := 10, day := 10 } &&
      !lands p { year := 1581, month := 10, day := 10 } .years 1 { year := 1582, month := 10, day := 20 } &&
      lands p { year := 1581, month := 10, day := 10 } .years 1 { year := 1582, month := 10, day := 10 }) = true := by
  native_decide

/- Completed-period counts across 1582 (`monthAndYearArithmeticIgnoresTheFormerCutover`): 20 October is one month from 10 September and one year and twelve months from 10 October 1581, rules that hold in both calendars. The 15 October rows are the cutover rows that separate the accounts: the hybrid calendar counted 0 months and 0 years there, and 31.1.1 stays silent on those counts, so 1, 1 and 12 are derived. Unmeasured on 31.1.1. -/
example :
    bothProfiles (fun p =>
      months? p { year := 1582, month := 9, day := 10 } { year := 1582, month := 10, day := 20 } == some 1 &&
      years? p { year := 1581, month := 10, day := 10 } { year := 1582, month := 10, day := 20 } == some 1 &&
      months? p { year := 1581, month := 10, day := 10 } { year := 1582, month := 10, day := 20 } == some 12 &&
      months? p { year := 1582, month := 9, day := 10 } { year := 1582, month := 10, day := 15 } == some 1 &&
      years? p { year := 1581, month := 10, day := 10 } { year := 1582, month := 10, day := 15 } == some 1 &&
      months? p { year := 1581, month := 10, day := 10 } { year := 1582, month := 10, day := 15 } == some 12) = true := by
  native_decide

/- The February-28 promotion holds before the cutover: Julian-leap 1500 is no leap year, and 1499-02-28 plus one year is 1500-02-28 (`monthAndYearArithmeticIgnoresTheFormerCutover`, GREGORIAN_END_OF_FEBRUARY). -/
example :
    bothProfiles (fun p =>
      lands p { year := 1499, month := 2, day := 28 } .years 1 { year := 1500, month := 2, day := 28 }) = true := by
  native_decide

/- A fresh construction takes the earlier offset of the repeated Berlin midnight of 1 October 1916, and a shift keeps its source's offset where the label allows it (spec/05 §2.7, `ConstructedDateInstantDiffTest`). The CEST source of a day or month shift equals the fresh midnight; a CET source keeps the later copy for a year shift and for a long day shift. -/
example :
    (Wall.instant? { year := 1916, month := 10, day := 1 } .europeBerlin).map (·.epochMillis) =
        some (-1680487200000) ∧
    lands .europeBerlin { year := 1916, month := 9, day := 30 } .days 1 { year := 1916, month := 10, day := 1 } ∧
    lands .europeBerlin { year := 1916, month := 9, day := 1 } .months 1 { year := 1916, month := 10, day := 1 } ∧
    (Wall.shifted? { year := 1915, month := 10, day := 1 } .europeBerlin .years 1).map (·.epochMillis) =
        some (-1680483600000) ∧
    (Wall.shifted? { year := 1916, month := 4, day := 1 } .europeBerlin .days 183).map (·.epochMillis) =
        some (-1680483600000) := by
  native_decide

/- A day shift re-resolves the wall label (spec/05 §5): the clock survives a crossing of the autumn overlap and of the evening before the spring gap, and a landing inside the gap moves forward by its length, `03:30` and not `01:30` (`WallDayArithmeticDiffTest`; a12-dmkits `ed58c513` for the first two rows). -/
example :
    lands .europeBerlin { year := 2024, month := 10, day := 27, hour := 0, minute := 30 } .days 1
        { year := 2024, month := 10, day := 28, hour := 0, minute := 30 } ∧
    lands .europeBerlin { year := 2024, month := 3, day := 30, hour := 23, minute := 30 } .days 1
        { year := 2024, month := 3, day := 31, hour := 23, minute := 30 } ∧
    lands .europeBerlin { year := 2024, month := 3, day := 30, hour := 2, minute := 30 } .days 1
        { year := 2024, month := 3, day := 31, hour := 3, minute := 30 } := by
  native_decide

/- A month landing inside the spring gap moves forward by the gap, as the `ZonedDateTime` account says; the kernel's month-and-year gap landing is unmeasured on 31.1.1, so this row is derived. Unmeasured on 31.1.1. -/
example :
    lands .europeBerlin { year := 2024, month := 1, day := 31, hour := 2, minute := 30 } .months 2
      { year := 2024, month := 3, day := 31, hour := 3, minute := 30 } = true := by
  native_decide

/- A completed month is tested by a fresh shift from the earlier operand whose gap landing moves forward: the shift of 1916-03-30T23:30 reaches the evening gap of 30 April and lands at 00:30 on 1 May, past the later operand at 00:00. Unmeasured on 31.1.1. -/
example :
    months? .europeBerlin { year := 1916, month := 3, day := 30, hour := 23, minute := 30 }
      { year := 1916, month := 5, day := 1 } = some 0 := by
  native_decide

/- Moving from a leap year's 28 February to a common year's resets the clock to the landing date's midnight, also for a negative year shift. Unmeasured on 31.1.1. -/
example :
    lands .europeBerlin { year := 2000, month := 2, day := 28, hour := 2, minute := 30 } .years (-1)
      { year := 1999, month := 2, day := 28 } = true := by
  native_decide

end A12Kernel.Conformance.BerlinLegacyCalendarArithmetic
