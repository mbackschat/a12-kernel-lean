import A12Kernel.Semantics.DateShift
import A12Kernel.Semantics.LegacyCalendarExpression

/-! # Berlin legacy calendar arithmetic

This capsule owns the versioned Europe/Berlin legacy profile's three `GregorianCalendar` field mutations and completed month/year qualification over already decoded hybrid-calendar labels plus exact instants, so a label before the 1582 cutover steps on its Julian calendar as the Kernel's clock does (2026-10-21 letter §1.12, KF588). Month and year mutation use the calendar's sign-independent compute-time resolver. Day mutation instead carries the source instant's offset into the nominal target and re-fits only when doing so preserves the target civil date. Every field mutation preserves source milliseconds unless the legacy February-28 rule clears the clock.

The stateful residual day-count algorithm, profile dispatch, parsing, Date-versus-DateTime admission, empty and malformed operands, calendar identity outside the concrete profiles, numeric result storage, validation polarity, and a general model-zone interface remain separate.
-/

namespace A12Kernel.EuropeBerlinLegacyProfile

private def landing? (unit : DateShiftUnit) (instant : Instant) (offset : Int) :
    Option (LegacyCalendarLabel × Instant) :=
  ModelZone.ConcreteProfile.europeBerlin.shiftCalendar? unit instant offset

/-- Day target selection uses the same source-relative calendar mutation as expression shifts. -/
def calendarDayTargetLanding? (current : LegacyCalendarLabel)
    (currentInstant : Instant) (nextDate : DateParts) : Option (TimeOfDay × Instant) := do
  let days := (← DateParts.LegacyHybrid.epochDay? nextDate) - (← DateParts.LegacyHybrid.epochDay? current.parts)
  let (label, landing) ← landing? .days currentInstant days
  if label.parts == nextDate then pure (label.time, landing) else none

def calendarDayLanding? (current : LegacyCalendarLabel) (currentInstant : Instant) (days : Int) :
    Option (LegacyCalendarLabel × Instant) := do
  if days = 0 then pure (current, currentInstant) else do
    let nextDate ← DateParts.LegacyHybrid.addDays? current.parts days
    let (time, landing) ← calendarDayTargetLanding? current currentInstant nextDate
    pure ({ parts := nextDate, time }, landing)

def calendarMonthLanding? (current : LegacyCalendarLabel) (currentInstant : Instant) (months : Int) :
    Option (LegacyCalendarLabel × Instant) :=
  if months = 0 then some (current, currentInstant) else landing? .months currentInstant months

def calendarYearLanding? (current : LegacyCalendarLabel) (currentInstant : Instant) (years : Int) :
    Option (LegacyCalendarLabel × Instant) :=
  if years = 0 then some (current, currentInstant) else landing? .years currentInstant years

/-- Whole completed years between ordered exact instants, using the same final-landing rule as legacy calendar year addition. -/
def wholeYearsForward? (earlier : LegacyCalendarLabel) (earlierInstant : Instant)
    (later : LegacyCalendarLabel) (laterInstant : Instant) : Option Nat := do
  let candidate :=
    Int.toNat
      (later.parts.year - earlier.parts.year)
  let (_, landing) ←
    calendarYearLanding? earlier earlierInstant (candidate : Int)
  pure (if laterInstant.epochMillis < landing.epochMillis then
    candidate - 1 else candidate)

/-- Test fresh source-relative month candidates until the first landing passes the later instant. Each candidate is independent: an intermediate gap normalization must not be skipped by jumping to the final year/month coordinate. -/
private def firstOvershootingMonth? (source : LegacyCalendarLabel)
    (sourceInstant laterInstant : Instant) :
    Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, candidate => do
      let (_, landing) ←
        calendarMonthLanding? source sourceInstant (candidate : Int)
      if laterInstant.epochMillis < landing.epochMillis then
        some (candidate - 1)
      else
        firstOvershootingMonth? source sourceInstant laterInstant
          fuel (candidate + 1)

/-- Whole completed months between ordered exact instants. Search starts at twelve times the completed-year lower bound and applies every candidate to a fresh source value. The civil month coordinate bounds the remaining search; profile or fuel failure stays explicit. -/
def wholeMonthsForward? (earlier : LegacyCalendarLabel) (earlierInstant : Instant)
    (later : LegacyCalendarLabel) (laterInstant : Instant) : Option Nat := do
  let years ←
    wholeYearsForward? earlier earlierInstant later laterInstant
  let firstCandidate := 12 * years
  let coordinateCandidate :=
    Int.toNat
      (later.parts.monthCoordinate -
        earlier.parts.monthCoordinate)
  let lastCandidate := max firstCandidate coordinateCandidate + 1
  firstOvershootingMonth? earlier earlierInstant laterInstant
    (lastCandidate - firstCandidate + 1) firstCandidate

/-- Restore authored sign around one nonnegative completed-period calculation, ordering by exact instants rather than possibly repeated wall labels. -/
def signedWholePeriods?
    (forward :
      LegacyCalendarLabel → Instant → LegacyCalendarLabel → Instant → Option Nat)
    (first : LegacyCalendarLabel) (firstInstant : Instant)
    (second : LegacyCalendarLabel) (secondInstant : Instant) : Option Int :=
  if firstInstant.epochMillis < secondInstant.epochMillis then
    (forward first firstInstant second secondInstant).map
      (fun amount => (amount : Int))
  else if secondInstant.epochMillis < firstInstant.epochMillis then
    (forward second secondInstant first firstInstant).map
      (fun amount => -(amount : Int))
  else
    some 0

/-- Signed completed-month count for two already resolved Berlin values. Exact instants establish order before the fresh candidate landing is tested. -/
def differenceResolvedInMonths? (first : LegacyCalendarLabel)
    (firstInstant : Instant) (second : LegacyCalendarLabel)
    (secondInstant : Instant) : Option Int :=
  signedWholePeriods? wholeMonthsForward?
    first firstInstant second secondInstant

/-- Signed completed-year count for two already resolved Berlin values. Exact instants establish order before the nonnegative candidate is qualified. -/
def differenceResolvedInYears? (first : LegacyCalendarLabel) (firstInstant : Instant)
    (second : LegacyCalendarLabel) (secondInstant : Instant) : Option Int :=
  signedWholePeriods? wholeYearsForward?
    first firstInstant second secondInstant

end A12Kernel.EuropeBerlinLegacyProfile
