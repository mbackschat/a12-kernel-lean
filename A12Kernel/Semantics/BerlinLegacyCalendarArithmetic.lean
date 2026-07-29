import A12Kernel.Semantics.DateShift
import A12Kernel.Semantics.ModelZone

/-! # Berlin legacy calendar arithmetic

This capsule owns the versioned Europe/Berlin legacy profile's three `GregorianCalendar` field mutations and completed month/year qualification over already decoded labels plus exact instants. Month and year mutation use the calendar's sign-independent compute-time resolver. Day mutation instead carries the source instant's offset into the nominal target and re-fits only when doing so preserves the target civil date. Every field mutation preserves source milliseconds unless the legacy February-28 rule clears the clock.

The stateful residual day-count algorithm, profile dispatch, parsing, Date-versus-DateTime admission, empty and malformed operands, calendar identity outside the concrete profiles, numeric result storage, validation polarity, and a general model-zone interface remain separate.
-/

namespace A12Kernel.EuropeBerlinLegacyProfile

/-- Millisecond component retained by a calendar field mutation. Lean's integer remainder is nonnegative, including before the Unix epoch. -/
private def millisecondPart (instant : Instant) : Int :=
  instant.epochMillis % 1000

/-- Interpret a whole-second wall label under one assumed offset without dropping the source calendar's millisecond field. -/
private def candidateInstantWithMillisecond (dateTime : LocalDateTime)
    (offsetSeconds millisecond : Int) : Instant :=
  { epochMillis :=
      (candidateInstant dateTime offsetSeconds).epochMillis + millisecond }

/-- Offset used when `GregorianCalendar.computeTime` resolves a month or year field mutation. Valid overlaps choose the smaller offset and therefore the later instant. In a gap, the largest candidate below the actual offset produces the post-gap wall label. -/
private def computeTimeOffset? (dateTime : LocalDateTime)
    (millisecond : Int) : Option Int :=
  match candidateOffsets.find? fun offsetSeconds =>
      offsetSecondsAt?
          (candidateInstantWithMillisecond
            dateTime offsetSeconds millisecond) ==
        some offsetSeconds with
  | some offsetSeconds => some offsetSeconds
  | none =>
      candidateOffsets.reverse.find? fun offsetSeconds =>
        match offsetSecondsAt?
            (candidateInstantWithMillisecond
              dateTime offsetSeconds millisecond) with
        | some actualOffset => offsetSeconds < actualOffset
        | none => false

/-- Decode one selected calendar instant under the offset actually in force there. The exact instant retains milliseconds even though the decoded wall label is whole-second. -/
private def decodeLanding? (landing : Instant) :
    Option (LocalDateTime × Instant) := do
  let actualOffset ← offsetSecondsAt? landing
  let next ← LocalDateTime.atOffset? landing actualOffset
  pure (next, landing)

/-- Resolve one month or year field mutation through `GregorianCalendar.computeTime`. This policy is independent of the signed amount; a gap may decode to a different wall label. -/
private def computeTimeLanding? (date : FullDate) (time : TimeOfDay)
    (millisecond : Int) : Option (LocalDateTime × Instant) := do
  let nominal : LocalDateTime := { date, time }
  let offset ← computeTimeOffset? nominal millisecond
  decodeLanding?
    (candidateInstantWithMillisecond nominal offset millisecond)

/-- Resolve the clock and exact instant for one already selected day-mutation target. The nominal target first keeps the source instant's own offset. When the offset actually in force there differs, the target is re-fitted to that offset only if the decoded civil date is preserved; otherwise the first candidate remains authoritative. -/
def calendarDayTargetLanding? (current : LocalDateTime)
    (currentInstant : Instant) (nextDate : FullDate) :
    Option (TimeOfDay × Instant) := do
  let sourceOffset ← offsetSecondsAt? currentInstant
  let millisecond := millisecondPart currentInstant
  let nominal : LocalDateTime := { date := nextDate, time := current.time }
  let first :=
    candidateInstantWithMillisecond
      nominal sourceOffset millisecond
  let firstActualOffset ← offsetSecondsAt? first
  let landing ←
    if firstActualOffset == sourceOffset then
      some first
    else
      let refitted :=
        candidateInstantWithMillisecond
          nominal firstActualOffset millisecond
      let refittedActualOffset ← offsetSecondsAt? refitted
      let refittedLabel ←
        LocalDateTime.atOffset? refitted refittedActualOffset
      pure (if refittedLabel.date == nextDate then refitted else first)
  let result ← decodeLanding? landing
  if result.1.date == nextDate then
    pure (result.1.time, result.2)
  else
    none

/-- Apply signed `Calendar.DAY_OF_MONTH` mutation. Travel direction selects the target date but not the landing offset. -/
def calendarDayLanding? (current : LocalDateTime)
    (currentInstant : Instant) (days : Int) :
    Option (LocalDateTime × Instant) := do
  if days = 0 then
    pure (current, currentInstant)
  else
    let nextDate ← current.date.addDays? days
    let (time, landing) ←
      calendarDayTargetLanding? current currentInstant nextDate
    pure ({ date := nextDate, time }, landing)

/-- Apply signed `Calendar.MONTH` mutation, including the leap-to-nonleap February-28 clock reset. Month mutation has no nonleap-to-leap promotion. -/
def calendarMonthLanding? (current : LocalDateTime)
    (currentInstant : Instant) (months : Int) :
    Option (LocalDateTime × Instant) := do
  if months = 0 then
    pure (current, currentInstant)
  else
    let nextDate ← current.date.addMonths? months
    let source := current.date.civil.parts
    let target := nextDate.civil.parts
    let clearClock :=
      source.month == 2 && source.day == 28 &&
        DateParts.isLeapYear source.year &&
        target.month == 2 && target.day == 28 &&
        !DateParts.isLeapYear target.year
    let time ← if clearClock then TimeOfDay.ofHms? 0 0 0 else some current.time
    let millisecond :=
      if clearClock then 0 else millisecondPart currentInstant
    computeTimeLanding? nextDate time millisecond

/-- Apply signed `Calendar.YEAR` mutation with both legacy February-28 corrections. `FullDate.addYears?` folds the nonleap-to-leap extra-day mutation into its target date; the explicit branch below clears the clock for leap-to-nonleap February 28. Compute-time resolution selects the later overlap instant and post-gap wall label independently of sign. -/
def calendarYearLanding? (current : LocalDateTime)
    (currentInstant : Instant) (years : Int) :
    Option (LocalDateTime × Instant) := do
  if years = 0 then
    pure (current, currentInstant)
  else
    let nextDate ← current.date.addYears? years
    let source := current.date.civil.parts
    let target := nextDate.civil.parts
    let clearClock :=
      source.month == 2 && source.day == 28 &&
        DateParts.isLeapYear source.year &&
        target.month == 2 && target.day == 28 &&
        !DateParts.isLeapYear target.year
    let time ← if clearClock then TimeOfDay.ofHms? 0 0 0 else some current.time
    let millisecond :=
      if clearClock then 0 else millisecondPart currentInstant
    computeTimeLanding? nextDate time millisecond

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
