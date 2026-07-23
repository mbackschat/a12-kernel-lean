import A12Kernel.Semantics.CivilDateCoordinate
import A12Kernel.Document

/-! # Decoded DateTime and selected instant semantics

This module contains a post-parse, whole-second UTC baseline plus the local DateTime types used by timezone profiles. A local wall label and scalar instant identity are different types even though UTC resolves each admitted label deterministically. The runtime core of `AddHours` operates only on the instant, preserving the identity needed when two Berlin instants share one wall label.

The definitions are original clean-room semantics for the decoded time, value-admission, UTC, and instant-arithmetic clauses of `spec/05` §§2–5 and 9. Formats, numeric offset coercion, cells, general zone dispatch, rendering, and consumer-specific result admission belong to later capsules.
-/

namespace A12Kernel

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

/-- Resolve an admitted whole-second local DateTime in UTC. UTC has no gap, fold, or offset. -/
def resolveUtc (dateTime : LocalDateTime) : Instant :=
  Instant.ofEpochSecond
    (dateTime.date.unixEpochDay * 86400 +
      (dateTime.time.secondsSinceMidnight : Int))

/-- Decode an exact instant under an already selected whole-second offset. This is the inverse boundary used by concrete zone profiles after they choose the offset at the instant. -/
def atOffset? (instant : Instant) (offsetSeconds : Int) :
    Option LocalDateTime := do
  let localEpochSecond := instant.epochMillis / 1000 + offsetSeconds
  let civil ← CivilDate.ofUnixEpochDay? (localEpochSecond / 86400)
  let date ← FullDate.ofCivil? civil
  let secondOfDay := Int.toNat (localEpochSecond % 86400)
  let time ← TimeOfDay.ofHms?
    (secondOfDay / 3600)
    ((secondOfDay % 3600) / 60)
    (secondOfDay % 60)
  pure { date, time }

end LocalDateTime

namespace Instant

/-- Shift an instant by an already-truncated whole-hour amount. This is the total runtime core after numeric conversion, not the complete authored `AddHours` operator. -/
def shiftHours (instant : Instant) (hours : Int) : Instant :=
  { epochMillis := instant.epochMillis + hours * 3600000 }

end Instant

end A12Kernel
