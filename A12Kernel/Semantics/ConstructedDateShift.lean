import A12Kernel.Semantics.DateConstruction
import A12Kernel.Semantics.DateShift

/-! # Constructed-Date legacy-hybrid month/year shifts

This capsule applies already-converted integer month and year offsets to a reason-bearing `Date(...)` result under the default October 1582 hybrid-calendar cutover. It preserves the existing construction result rather than introducing a second Date representation. The concrete profile covers the historical cutover behavior shared by UTC, GMT, and the pinned Berlin model zone; other zone-local missing dates, numeric amount evaluation, DateTime, differences, and target storage remain separate.
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

/-- Admit a nominal field-preserving landing, normalizing a missing October 1582 label ten civil labels forward as lenient `GregorianCalendar.add` does. -/
def normalizeTarget? (year : Int) (month day : Nat) : Option DateParts :=
  let nominal : DateParts := { year, month, day }
  let normalized :=
    if DateParts.LegacyHybrid.inCutoverGap nominal then
      { nominal with day := nominal.day + 10 }
    else
      nominal
  if DateParts.LegacyHybrid.isReal normalized then some normalized else none

/-- Shift one legacy-hybrid label by whole months, clamping only at the target month's final day before cutover-hole normalization. -/
def addMonths? (source : DateParts) (offset : Int) : Option DateParts :=
  if !DateParts.LegacyHybrid.isReal source then
    none
  else
    let (targetYear, targetMonth) := DateParts.shiftedYearMonth source offset
    match daysInMonth? targetYear targetMonth with
    | none => none
    | some targetLastDay =>
        normalizeTarget? targetYear targetMonth
          (DateParts.Shift.monthLandingDay source targetLastDay)

/-- Shift one legacy-hybrid label by whole years. The February-28 promotion deliberately tests Gregorian leap status on both sides, including the Julian side of the cutover. -/
def addYears? (source : DateParts) (offset : Int) : Option DateParts :=
  if !DateParts.LegacyHybrid.isReal source then
    none
  else
    let targetYear := source.year + offset
    match daysInMonth? targetYear source.month with
    | none => none
    | some targetLastDay => do
        let landing ← normalizeTarget? targetYear source.month
          (min source.day targetLastDay)
        if source.month == 2 && source.day == 28 &&
            landing.month == 2 && landing.day == 28 &&
            !DateParts.isLeapYear source.year &&
            DateParts.isLeapYear targetYear then
          normalizeTarget? targetYear 2 29
        else
          some landing

end DateParts.LegacyHybrid

namespace DateConstructionResult

/-- Apply a default-profile legacy month shift to a constructed Date while retaining incomplete, unreal, and formally unavailable reasons. -/
def addLegacyMonths? (result : DateConstructionResult) (offset : Int) :
    Option DateConstructionResult :=
  match result with
  | .real parts => (DateParts.LegacyHybrid.addMonths? parts offset).map .real
  | .incomplete => some .incomplete
  | .unreal => some .unreal
  | .unknown => some .unknown

/-- Apply a default-profile legacy year shift to a constructed Date while retaining incomplete, unreal, and formally unavailable reasons. -/
def addLegacyYears? (result : DateConstructionResult) (offset : Int) :
    Option DateConstructionResult :=
  match result with
  | .real parts => (DateParts.LegacyHybrid.addYears? parts offset).map .real
  | .incomplete => some .incomplete
  | .unreal => some .unreal
  | .unknown => some .unknown

end DateConstructionResult

end A12Kernel
