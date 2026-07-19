import A12Kernel.Semantics.FullDate
import A12Kernel.Document

/-! # Decoded UTC DateTime semantics

This is a selected post-parse, whole-second boundary for one clean full DateTime under UTC. A local wall label and scalar instant identity are different types even though UTC resolves each admitted label deterministically. The runtime core of `AddHours` operates only on the instant. This preserves the representation needed for a later zone where one local label can denote more than one instant.

The definitions are original clean-room semantics for the decoded time, value-admission, UTC, and instant-arithmetic clauses of `spec/05` §§2–5 and 9. Formats, numeric offset coercion, cells, non-UTC zones, rendering, and consumer-specific result admission belong to later capsules.
-/

namespace A12Kernel

/-- A decoded whole-second wall-clock time. -/
structure TimeOfDay where
  hour : Nat
  minute : Nat
  second : Nat
  valid : hour < 24 ∧ minute < 60 ∧ second < 60
  deriving Repr, DecidableEq

namespace TimeOfDay

/-- Construct a whole-second time exactly when every component is in range. -/
def ofHms? (hour minute second : Nat) : Option TimeOfDay :=
  if valid : hour < 24 ∧ minute < 60 ∧ second < 60 then
    some { hour, minute, second, valid }
  else
    none

/-- Elapsed whole seconds since local midnight. -/
def secondsSinceMidnight (time : TimeOfDay) : Nat :=
  time.hour * 3600 + time.minute * 60 + time.second

end TimeOfDay

namespace CivilDate

/-- Complete proleptic-Gregorian days preceding the supplied positive-era year. -/
private def daysBeforeYear (year : Int) : Int :=
  let previous := year - 1
  previous * 365 + previous.tdiv 4 - previous.tdiv 100 + previous.tdiv 400

/-- Complete days preceding the supplied month in its year. Civil-date reality guarantees that all visited month numbers exist. -/
private def daysBeforeMonth (year : Int) (month : Nat) : Nat :=
  (List.range (month - 1)).foldl (fun total offset =>
    total + (DateParts.daysInMonth? year (offset + 1)).getD 0) 0

/-- Proleptic-Gregorian day coordinate relative to 1970-01-01. The origin affects representation only, not elapsed-time semantics. -/
def unixEpochDay (date : CivilDate) : Int :=
  daysBeforeYear date.parts.year +
    (daysBeforeMonth date.parts.year date.parts.month : Int) +
    (date.parts.day : Int) - 1 - 719162

end CivilDate

namespace FullDate

/-- UTC day coordinate of an admitted full Date value. -/
def unixEpochDay (date : FullDate) : Int :=
  date.civil.unixEpochDay

end FullDate

/-- An admitted full local DateTime wall label, not yet an instant. -/
structure LocalDateTime where
  date : FullDate
  time : TimeOfDay
  deriving Repr, DecidableEq

namespace LocalDateTime

/-- Combine an admitted Date with decoded time components. -/
def ofDateHms? (date : FullDate) (hour minute second : Nat) :
    Option LocalDateTime :=
  (TimeOfDay.ofHms? hour minute second).map fun time =>
    { date, time }

/-- Construct a decoded local DateTime through the existing Date and whole-second time admission checks. -/
def ofYmdHms? (year : Int) (month day hour minute second : Nat) :
    Option LocalDateTime :=
  (FullDate.ofYmd? year month day).bind fun date =>
    ofDateHms? date hour minute second

/-- Resolve an admitted local DateTime in UTC. UTC has no gap, fold, or offset. -/
def resolveUtc (dateTime : LocalDateTime) : Instant :=
  {
    epochSecond :=
      dateTime.date.unixEpochDay * 86400 +
        (dateTime.time.secondsSinceMidnight : Int)
  }

end LocalDateTime

namespace Instant

/-- Shift an instant by an already-truncated whole-hour amount. This is the total runtime core after numeric conversion, not the complete authored `AddHours` operator. -/
def shiftHours (instant : Instant) (hours : Int) : Instant :=
  { epochSecond := instant.epochSecond + hours * 3600 }

end Instant

end A12Kernel
