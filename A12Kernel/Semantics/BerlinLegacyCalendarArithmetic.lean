import A12Kernel.Semantics.DateShift
import A12Kernel.Semantics.LegacyCalendarExpression

/-! # Berlin legacy calendar arithmetic

This capsule owns the versioned Europe/Berlin legacy profile's three `GregorianCalendar` field mutations and completed month/year qualification over already decoded labels plus exact instants. Month and year mutation use the calendar's sign-independent compute-time resolver. Day mutation instead carries the source instant's offset into the nominal target and re-fits only when doing so preserves the target civil date. Every field mutation preserves source milliseconds unless the legacy February-28 rule clears the clock.

The stateful residual day-count algorithm, profile dispatch, parsing, Date-versus-DateTime admission, empty and malformed operands, calendar identity outside the concrete profiles, numeric result storage, validation polarity, and a general model-zone interface remain separate.
-/

namespace A12Kernel.EuropeBerlinLegacyProfile

/-- Adapt calendar arithmetic to consumers whose contract requires a stored-Date-admitted
label. The expression mechanism itself retains pre-floor results for its target to check. -/
private def admittedLanding? (unit : DateShiftUnit) (instant : Instant) (offset : Int) :
    Option (LocalDateTime × Instant) := do
  let (label, landing) ← ModelZone.ConcreteProfile.europeBerlin.shiftCalendar? unit instant offset
  pure (← label.toLocal?, landing)

/-- Day target selection uses the same source-relative calendar mutation as expression shifts. -/
def calendarDayTargetLanding? (current : LocalDateTime)
    (currentInstant : Instant) (nextDate : FullDate) : Option (TimeOfDay × Instant) := do
  let days := nextDate.unixEpochDay - current.date.unixEpochDay
  let (label, landing) ← admittedLanding? .days currentInstant days
  if label.date == nextDate then pure (label.time, landing) else none

def calendarDayLanding? (current : LocalDateTime) (currentInstant : Instant) (days : Int) :
    Option (LocalDateTime × Instant) := do
  if days = 0 then pure (current, currentInstant) else do
    let nextDate ← current.date.addDays? days
    let (time, landing) ← calendarDayTargetLanding? current currentInstant nextDate
    pure ({ date := nextDate, time }, landing)

def calendarMonthLanding? (current : LocalDateTime) (currentInstant : Instant) (months : Int) :
    Option (LocalDateTime × Instant) :=
  if months = 0 then some (current, currentInstant) else admittedLanding? .months currentInstant months

def calendarYearLanding? (current : LocalDateTime) (currentInstant : Instant) (years : Int) :
    Option (LocalDateTime × Instant) :=
  if years = 0 then some (current, currentInstant) else admittedLanding? .years currentInstant years

/-- Whole completed years between ordered exact instants, using the same final-landing rule as legacy calendar year addition. -/
def wholeYearsForward? (earlier : LocalDateTime) (earlierInstant : Instant)
    (later : LocalDateTime) (laterInstant : Instant) : Option Nat := do
  let candidate :=
    Int.toNat
      (later.date.civil.parts.year - earlier.date.civil.parts.year)
  let (_, landing) ←
    calendarYearLanding? earlier earlierInstant (candidate : Int)
  pure (if laterInstant.epochMillis < landing.epochMillis then
    candidate - 1 else candidate)

/-- Test fresh source-relative month candidates until the first landing passes the later instant. Each candidate is independent: an intermediate gap normalization must not be skipped by jumping to the final year/month coordinate. -/
private def firstOvershootingMonth? (source : LocalDateTime)
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
def wholeMonthsForward? (earlier : LocalDateTime) (earlierInstant : Instant)
    (later : LocalDateTime) (laterInstant : Instant) : Option Nat := do
  let years ←
    wholeYearsForward? earlier earlierInstant later laterInstant
  let firstCandidate := 12 * years
  let coordinateCandidate :=
    Int.toNat
      (later.date.civil.parts.monthCoordinate -
        earlier.date.civil.parts.monthCoordinate)
  let lastCandidate := max firstCandidate coordinateCandidate + 1
  firstOvershootingMonth? earlier earlierInstant laterInstant
    (lastCandidate - firstCandidate + 1) firstCandidate

/-- Restore authored sign around one nonnegative completed-period calculation, ordering by exact instants rather than possibly repeated wall labels. -/
def signedWholePeriods?
    (forward :
      LocalDateTime → Instant → LocalDateTime → Instant → Option Nat)
    (first : LocalDateTime) (firstInstant : Instant)
    (second : LocalDateTime) (secondInstant : Instant) : Option Int :=
  if firstInstant.epochMillis < secondInstant.epochMillis then
    (forward first firstInstant second secondInstant).map
      (fun amount => (amount : Int))
  else if secondInstant.epochMillis < firstInstant.epochMillis then
    (forward second secondInstant first firstInstant).map
      (fun amount => -(amount : Int))
  else
    some 0

/-- Signed completed-month count for two already resolved Berlin values. Exact instants establish order before the fresh candidate landing is tested. -/
def differenceResolvedInMonths? (first : LocalDateTime)
    (firstInstant : Instant) (second : LocalDateTime)
    (secondInstant : Instant) : Option Int :=
  signedWholePeriods? wholeMonthsForward?
    first firstInstant second secondInstant

/-- Signed completed-year count for two already resolved Berlin values. Exact instants establish order before the nonnegative candidate is qualified. -/
def differenceResolvedInYears? (first : LocalDateTime) (firstInstant : Instant)
    (second : LocalDateTime) (secondInstant : Instant) : Option Int :=
  signedWholePeriods? wholeYearsForward?
    first firstInstant second secondInstant

end A12Kernel.EuropeBerlinLegacyProfile
