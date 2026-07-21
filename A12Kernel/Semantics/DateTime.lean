import A12Kernel.Semantics.CivilDateCoordinate
import A12Kernel.Document

/-! # Decoded DateTime and selected instant semantics

This module contains a post-parse, whole-second UTC baseline plus the local DateTime types used by timezone profiles. A local wall label and scalar instant identity are different types even though UTC resolves each admitted label deterministically. The runtime core of `AddHours` operates only on the instant, preserving the identity needed when two Berlin instants share one wall label.

The definitions are original clean-room semantics for the decoded time, value-admission, UTC, instant-arithmetic, and finite Berlin 2024 calendar-stepping clauses of `spec/05` §§2–5 and 9. Formats, numeric offset coercion, cells, general zone dispatch, rendering, and consumer-specific result admission belong to later capsules.
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
`Berlin2024Profile` now owns only the finite calendar-day stepping risk slice over 2024-03-29 through 2024-04-01. Fresh-label resolution belongs to the versioned general Berlin profile; this namespace must not grow a parallel resolver.
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

/-- The missing local hour on the selected 2024 spring-transition date. -/
def SpringGap (dateTime : LocalDateTime) : Prop :=
  dateTime.date.civil.parts.year = 2024 ∧
    dateTime.date.civil.parts.month = 3 ∧
    dateTime.date.civil.parts.day = 31 ∧
    dateTime.time.hour = 2

instance (dateTime : LocalDateTime) : Decidable (SpringSupported dateTime) := by
  unfold SpringSupported
  infer_instance

instance (dateTime : LocalDateTime) : Decidable (SpringGap dateTime) := by
  unfold SpringGap
  infer_instance

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
