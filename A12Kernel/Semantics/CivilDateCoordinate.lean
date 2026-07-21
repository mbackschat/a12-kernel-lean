import A12Kernel.Semantics.FullDate

/-! # Civil Date coordinate

This module owns the proleptic-Gregorian whole-day coordinate shared by Date and DateTime semantics. The coordinate origin affects representation only; elapsed-day and ordering consumers depend on its differences. Parsing, zones, value provenance, and arithmetic result admission remain separate.
-/

namespace A12Kernel

namespace CivilDate

/-- Complete proleptic-Gregorian days preceding the supplied positive-era year. -/
def daysBeforeYear (year : Int) : Int :=
  let previous := year - 1
  previous * 365 + previous.tdiv 4 - previous.tdiv 100 + previous.tdiv 400

/-- Complete days before a month boundary. Semantic uses are `1..12`; proofs also use `13` as the exclusive end-of-year boundary. -/
def daysBeforeMonth (year : Int) (month : Nat) : Nat :=
  (List.range (month - 1)).foldl (fun total offset =>
    total + (DateParts.daysInMonth? year (offset + 1)).getD 0) 0

/-- Zero-based position within the civil year. -/
def dayOffset (date : CivilDate) : Int :=
  (daysBeforeMonth date.parts.year date.parts.month : Int) +
    (date.parts.day : Int) - 1

/-- Proleptic-Gregorian day coordinate relative to 1970-01-01. -/
def unixEpochDay (date : CivilDate) : Int :=
  daysBeforeYear date.parts.year + date.dayOffset - 719162

namespace EpochInverse

/-- Locate a zero-based day inside one Gregorian year, scanning at most one complete 400-year era. -/
private def locateYear : Nat → Int → Nat → Option (Int × Nat)
  | 0, _, _ => none
  | fuel + 1, year, remaining =>
      let yearLength := if DateParts.isLeapYear year then 366 else 365
      if remaining < yearLength then some (year, remaining)
      else locateYear fuel (year + 1) (remaining - yearLength)

/-- Locate a one-based month/day inside one already selected Gregorian year. -/
private def locateMonth : Nat → Int → Nat → Nat → Option (Nat × Nat)
  | 0, _, _, _ => none
  | fuel + 1, year, month, remaining =>
      match DateParts.daysInMonth? year month with
      | none => none
      | some monthLength =>
          if remaining < monthLength then some (month, remaining + 1)
          else locateMonth fuel year (month + 1) (remaining - monthLength)

end EpochInverse

/-- Invert the Gregorian day coordinate with at most 400 year steps and 12 month steps. Coordinates before the positive era fail closed. -/
def ofUnixEpochDay? (epochDay : Int) : Option CivilDate :=
  let absoluteDay := epochDay + 719162
  if absoluteDay < 0 then
    none
  else
    let era := absoluteDay / 146097
    let dayInEra := Int.toNat (absoluteDay % 146097)
    match EpochInverse.locateYear 400 (era * 400 + 1) dayInEra with
    | none => none
    | some (year, dayInYear) =>
        match EpochInverse.locateMonth 12 year 1 dayInYear with
        | none => none
        | some (month, day) => CivilDate.ofYmd? year month day

/-- The next real civil day. Returning `Option` keeps the executable constructor on the same checked boundary as `ofYmd?`; every `CivilDate` is proved to have a successor. -/
def next? (date : CivilDate) : Option CivilDate :=
  let parts := date.parts
  match DateParts.daysInMonth? parts.year parts.month with
  | none => none
  | some lastDay =>
      if parts.day < lastDay then
        CivilDate.ofYmd? parts.year parts.month (parts.day + 1)
      else if parts.month < 12 then
        CivilDate.ofYmd? parts.year (parts.month + 1) 1
      else
        CivilDate.ofYmd? (parts.year + 1) 1 1

end CivilDate

namespace FullDate

/-- Gregorian day coordinate of an admitted full Date value. -/
def unixEpochDay (date : FullDate) : Int :=
  date.civil.unixEpochDay

end FullDate

end A12Kernel
