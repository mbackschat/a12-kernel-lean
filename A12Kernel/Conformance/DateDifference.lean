import A12Kernel.Semantics.DateDifference

/-! # Admitted full-Date month/year difference locks -/

namespace A12Kernel.Conformance.DateDifference

open A12Kernel

private def differenceInMonths? (firstYear : Int) (firstMonth firstDay : Nat)
    (secondYear : Int) (secondMonth secondDay : Nat) : Option Int := do
  let first ← FullDate.ofYmd? firstYear firstMonth firstDay
  let second ← FullDate.ofYmd? secondYear secondMonth secondDay
  pure (first.differenceInMonths second)

private def differenceInYears? (firstYear : Int) (firstMonth firstDay : Nat)
    (secondYear : Int) (secondMonth secondDay : Nat) : Option Int := do
  let first ← FullDate.ofYmd? firstYear firstMonth firstDay
  let second ← FullDate.ofYmd? secondYear secondMonth secondDay
  pure (first.differenceInYears second)

/- Whole-month difference counts a clamped month-end landing but not an overshooting ordinary day. -/
example :
    differenceInMonths? 2020 1 15 2020 2 15 = some 1 ∧
      differenceInMonths? 2020 1 15 2020 2 14 = some 0 ∧
      differenceInMonths? 2020 1 31 2020 2 29 = some 1 ∧
      differenceInMonths? 2010 1 31 2010 3 30 = some 1 := by
  native_decide

/- Whole-month difference is signed after ordering, crosses years, and truncates a reverse partial month toward zero. -/
example :
    differenceInMonths? 2020 12 15 2021 2 15 = some 2 ∧
      differenceInMonths? 2020 2 29 2020 1 30 = some (-1) ∧
      differenceInMonths? 2020 6 15 2020 6 10 = some 0 := by
  native_decide

/- Whole-year difference uses the distinct last-of-February landing rule. -/
example :
    differenceInYears? 2020 6 15 2021 6 15 = some 1 ∧
      differenceInYears? 2020 6 15 2021 6 14 = some 0 ∧
      differenceInYears? 2020 2 29 2024 2 28 = some 3 ∧
      differenceInYears? 1999 2 28 2000 2 28 = some 0 ∧
      differenceInYears? 1999 2 28 2000 2 29 = some 1 := by
  native_decide

/- Equal operands have zero difference in both units. -/
example :
    differenceInMonths? 2024 2 29 2024 2 29 = some 0 ∧
      differenceInYears? 2024 2 29 2024 2 29 = some 0 := by
  native_decide

/- Direct Base Year and its range start are the same date-difference source. -/
example :
    baseYearDateDifferenceInMonths 2024 .direct (.range .start) = 0 ∧
      baseYearDateDifferenceInYears 2024 .direct (.range .start) = 0 := by
  native_decide

/- The selected end of Base Year's range is eleven whole months, but no whole year, after its direct January source. -/
example :
    baseYearDateDifferenceInMonths 2024 .direct (.range .finish) = 11 ∧
      baseYearDateDifferenceInMonths 2024 (.range .finish) .direct = -11 ∧
      baseYearDateDifferenceInYears 2024 .direct (.range .finish) = 0 ∧
      baseYearDateDifferenceInYears 2024 (.range .finish) .direct = 0 := by
  native_decide

/- Configured Base-Year sources remain floor-free before the stored-Date boundary. -/
example :
    baseYearDateDifferenceInMonths 1500 .direct (.range .finish) = 11 ∧
      baseYearDateDifferenceInYears 1500 .direct (.range .finish) = 0 := by
  native_decide

/-- A `dd.MM.` declaration: date components without a year, which is the only shape the Base-Year
    axis can move. -/
private def yearless : TemporalComponents :=
  { year := false, month := true, day := true, hour := false, minute := false, second := false }

/-- A bare `HH:mm:ss` declaration: no calendar component at all. -/
private def clockOnly : TemporalComponents :=
  { year := false, month := false, day := false, hour := true, minute := true, second := true }

/-- A complete `yyyy-MM-dd'T'HH:mm:ss` instant, which carries every component of both halves. -/
private def completeInstant : TemporalComponents :=
  { year := true, month := true, day := true, hour := true, minute := true, second := true }

/- Base Year supplies the year position at the year difference and widens nothing else, which is
   what separates the two completed-period units on one operand. Each row is retained from the
   Kernel at the [difference-gate checkpoint](../../docs/sources/computation-placement-and-constant-probes.md#src-difference-gate-base-year-conditioning). -/
example :
    DateDifferenceUnit.years.admittedBy true yearless = true ∧
      DateDifferenceUnit.years.admittedBy false yearless = false ∧
      DateDifferenceUnit.months.admittedBy true yearless = true ∧
      DateDifferenceUnit.months.admittedBy false yearless = true := by
  native_decide

/- A time half refuses both completed-period units however complete the date half is, while the
   day difference admits the same instant — the pair that keeps the widening at its own family and
   refutes reading one difference family's gate across the three. -/
example :
    DateDifferenceUnit.years.admittedBy true completeInstant = false ∧
      DateDifferenceUnit.months.admittedBy true completeInstant = false ∧
      CalendarDayDifference.admittedBy completeInstant = true ∧
      CalendarDayDifference.admittedBy clockOnly = false ∧
      CalendarDayDifference.admittedBy yearless = true := by
  native_decide

/- No calendar component at all is refused at every unit whether or not Base Year is declared: the
   supplementation reaches the year position, never the date half it would have to stand in for. -/
example :
    DateDifferenceUnit.years.admittedBy true clockOnly = false ∧
      DateDifferenceUnit.years.admittedBy false clockOnly = false ∧
      DateDifferenceUnit.months.admittedBy true clockOnly = false := by
  native_decide

end A12Kernel.Conformance.DateDifference
