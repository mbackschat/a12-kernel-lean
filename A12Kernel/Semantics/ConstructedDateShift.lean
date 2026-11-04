import A12Kernel.Semantics.DateConstruction
import A12Kernel.Semantics.DateShift

/-! # Hybrid Julian–Gregorian calendar reality

Kernel 31.1.1 computes every runtime date on the proleptic ISO calendar (spec/05 §2.7), but static admission of a date constant keeps the default October 1582 hybrid calendar (spec/05 §1). This capsule owns the hybrid month lengths and reality predicate that static admission and stored-text ingestion still consult; it carries no arithmetic, because no runtime consumer steps on that calendar any more.
-/

namespace A12Kernel

namespace DateParts.LegacyHybrid

/-- Julian leap classification used before the default Gregorian cutover. -/
def isJulianLeapYear (year : Int) : Bool :=
  decide (year % 4 = 0)

/-- Month length under the default legacy hybrid calendar. February is Julian before the 1582 cutover year and Gregorian from then onward. -/
def daysInMonth? (year : Int) : Nat → Option Nat
  | 1 => some 31
  | 2 =>
      some (if year < 1582 then
        if isJulianLeapYear year then 29 else 28
      else if DateParts.isLeapYear year then 29 else 28)
  | 3 => some 31
  | 4 => some 30
  | 5 => some 31
  | 6 => some 30
  | 7 => some 31
  | 8 => some 31
  | 9 => some 30
  | 10 => some 31
  | 11 => some 30
  | 12 => some 31
  | _ => none

/-- Whether a decoded label lies in the ten-date hole of the default legacy-calendar cutover. -/
def inCutoverGap (parts : DateParts) : Bool :=
  parts.year == 1582 && parts.month == 10 &&
    decide (5 ≤ parts.day) && decide (parts.day ≤ 14)

/-- Calendar reality for a positive-era label under the default legacy hybrid calendar. -/
def isReal (parts : DateParts) : Bool :=
  decide (0 < parts.year) &&
    match daysInMonth? parts.year parts.month with
    | some lastDay =>
        decide (0 < parts.day ∧ parts.day ≤ lastDay) && !inCutoverGap parts
    | none => false

end DateParts.LegacyHybrid

end A12Kernel
