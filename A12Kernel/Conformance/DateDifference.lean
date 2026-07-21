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

end A12Kernel.Conformance.DateDifference
