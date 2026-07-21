import A12Kernel.Semantics.FullDate
import A12Kernel.Document

/-! # Decoded DateTime and selected instant semantics

This module contains a post-parse, whole-second UTC baseline plus a finite Berlin 2024 transition profile. A local wall label and scalar instant identity are different types even though UTC resolves each admitted label deterministically. The runtime core of `AddHours` operates only on the instant, preserving the identity needed when two Berlin instants share one wall label.

The definitions are original clean-room semantics for the decoded time, value-admission, UTC, instant-arithmetic, and finite Berlin 2024 transition clauses of `spec/05` §§2–5 and 9. Formats, numeric offset coercion, cells, general zone dispatch, rendering, and consumer-specific result admission belong to later capsules.
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

/-- Proleptic-Gregorian day coordinate relative to 1970-01-01. The origin affects representation only, not elapsed-time semantics. -/
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

/-- Strict chronological order on admitted local wall labels, before any time-zone resolution. -/
def Before (left right : LocalDateTime) : Prop :=
  left.date.civil.Before right.date.civil ∨
    left.date.civil = right.date.civil ∧
      left.time.secondsSinceMidnight < right.time.secondsSinceMidnight

instance (left right : LocalDateTime) : Decidable (Before left right) := by
  unfold Before
  infer_instance

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
`Berlin2024Profile` is a finite risk-isolation profile, not a general timezone implementation. It admits only 2024-03-29 through 2024-04-01 and the observed autumn transition date. Fresh spring-gap labels fail, fresh autumn-overlap labels select the later standard-side instant, and calendar-day stepping is exposed only inside the consecutive spring slice. A later general Berlin resolver should replace this profile rather than coexist with it as legacy behavior.
-/
namespace Berlin2024Profile

/-- The consecutive local-date domain used by the selected spring-transition and calendar-day slice. -/
def SpringSupported (dateTime : LocalDateTime) : Prop :=
  dateTime.date.civil.parts.year = 2024 ∧
    ((dateTime.date.civil.parts.month = 3 ∧
        29 ≤ dateTime.date.civil.parts.day ∧
        dateTime.date.civil.parts.day ≤ 31) ∨
      (dateTime.date.civil.parts.month = 4 ∧
        dateTime.date.civil.parts.day = 1))

/-- The exact local-date domain of the selected autumn-overlap slice. -/
def AutumnSupported (dateTime : LocalDateTime) : Prop :=
  dateTime.date.civil.parts.year = 2024 ∧
    dateTime.date.civil.parts.month = 10 ∧
    dateTime.date.civil.parts.day = 27

/-- The complete fresh-label domain of the finite profile. -/
def Supported (dateTime : LocalDateTime) : Prop :=
  SpringSupported dateTime ∨ AutumnSupported dateTime

/-- The missing local hour on the selected 2024 spring-transition date. -/
def SpringGap (dateTime : LocalDateTime) : Prop :=
  dateTime.date.civil.parts.year = 2024 ∧
    dateTime.date.civil.parts.month = 3 ∧
    dateTime.date.civil.parts.day = 31 ∧
    dateTime.time.hour = 2

instance (dateTime : LocalDateTime) : Decidable (SpringSupported dateTime) := by
  unfold SpringSupported
  infer_instance

instance (dateTime : LocalDateTime) : Decidable (AutumnSupported dateTime) := by
  unfold AutumnSupported
  infer_instance

instance (dateTime : LocalDateTime) : Decidable (Supported dateTime) := by
  unfold Supported
  infer_instance

instance (dateTime : LocalDateTime) : Decidable (SpringGap dateTime) := by
  unfold SpringGap
  infer_instance

/-- UTC shift for a supported, non-gap fresh label. -/
def offsetHours (dateTime : LocalDateTime) : Int :=
  if dateTime.date.civil.parts.month = 10 then
    if dateTime.time.hour < 2 then -2 else -1
  else if dateTime.date.civil.parts.month = 4 ∨
      (dateTime.date.civil.parts.day = 31 ∧ 3 ≤ dateTime.time.hour) then
    -2
  else
    -1

/-- Resolve a freshly supplied local label in the finite Berlin profile. Spring `02:xx` labels fail; repeated autumn `02:xx` labels select standard time. Instant arithmetic and calendar stepping do not reparse their results. -/
def resolveLocal? (dateTime : LocalDateTime) : Option Instant :=
  if Supported dateTime ∧ ¬SpringGap dateTime then
    some (dateTime.resolveUtc.shiftHours (offsetHours dateTime))
  else
    none

/-- Rebuild a supported spring label on another profile date while retaining its current clock. -/
private def onSpringDate? (dateTime : LocalDateTime)
    (month day hour : Nat) : Option LocalDateTime :=
  LocalDateTime.ofYmdHms? 2024 month day hour
    dateTime.time.minute dateTime.time.second

/-- Add one stateful calendar day inside the finite spring slice. A landing in the missing `02:xx` hour moves to `01:xx`, and later steps retain that adjusted clock. -/
def nextCalendarDay? (dateTime : LocalDateTime) : Option LocalDateTime :=
  if SpringSupported dateTime ∧ ¬SpringGap dateTime then
    match dateTime.date.civil.parts.month,
        dateTime.date.civil.parts.day with
    | 3, 29 => onSpringDate? dateTime 3 30 dateTime.time.hour
    | 3, 30 =>
        onSpringDate? dateTime 3 31
          (if dateTime.time.hour = 2 then 1 else dateTime.time.hour)
    | 3, 31 => onSpringDate? dateTime 4 1 dateTime.time.hour
    | _, _ => none
  else
    none

end Berlin2024Profile

end A12Kernel
