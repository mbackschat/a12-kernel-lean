import A12Kernel.Semantics.FullDate
import A12Kernel.Document

/-! # Decoded DateTime and selected instant semantics

This module contains a post-parse, whole-second UTC baseline plus one exact Berlin autumn-transition slice. A local wall label and scalar instant identity are different types even though UTC resolves each admitted label deterministically. The runtime core of `AddHours` operates only on the instant, preserving the identity needed when two Berlin instants share one wall label.

The definitions are original clean-room semantics for the decoded time, value-admission, UTC, instant-arithmetic, and exact Berlin 2024 autumn-overlap clauses of `spec/05` §§2–5 and 9. Formats, numeric offset coercion, cells, general zone dispatch, rendering, and consumer-specific result admission belong to later capsules.
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

/-!
`BerlinAutumn2024` is a risk-isolation slice, not a general timezone implementation. It admits only the observed 2024 autumn transition date, chooses daylight time before 02:00 and standard time from 02:00 onward, and fails closed on every other date. A later general Berlin resolver should replace this slice rather than coexist with it as legacy behavior.
-/
namespace BerlinAutumn2024

/-- The exact local-date domain of the selected Berlin autumn-transition slice. -/
def Supported (dateTime : LocalDateTime) : Prop :=
  dateTime.date.civil.parts.year = 2024 ∧
    dateTime.date.civil.parts.month = 10 ∧
    dateTime.date.civil.parts.day = 27

instance (dateTime : LocalDateTime) : Decidable (Supported dateTime) := by
  unfold Supported
  infer_instance

/-- Resolve a freshly supplied local label on 2024-10-27 in Berlin. The repeated `02:xx` hour selects standard time; instant arithmetic does not call this function again. -/
def resolveLocal? (dateTime : LocalDateTime) : Option Instant :=
  if Supported dateTime then
    some (dateTime.resolveUtc.shiftHours
      (if dateTime.time.hour < 2 then -2 else -1))
  else
    none

end BerlinAutumn2024

end A12Kernel
