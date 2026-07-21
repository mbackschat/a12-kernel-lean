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
