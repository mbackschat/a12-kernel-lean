import A12Kernel.Semantics.DateShift
import A12Kernel.Semantics.ModelZone

/-! # Concrete model-zone calendar-day differences

This capsule implements the resolved `DifferenceInDays` core for UTC and the versioned Europe/Berlin legacy profile. Berlin qualifies the kernel's whole-year candidate through the distinct `Calendar.YEAR` mutation, makes the `365 × whole-years` lower-bound day landing, then counts stateful residual day landings in authored operand order. Month and year mutation use the calendar's sign-independent compute-time resolver. Day mutation instead carries the source instant's offset into the nominal target and re-fits only when doing so preserves the target civil date. Every field mutation preserves source milliseconds unless the legacy February-28 rule clears the clock.

Parsing, Date-versus-DateTime admission, empty and malformed operands, calendar identity outside the concrete profiles, numeric result storage, validation polarity, and a general model-zone interface remain separate.
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

/-- Count consecutive profile landings that do not pass the later instant. Fuel is derived from the civil-date distance; exhaustion or an unresolved landing remains explicit absence rather than collapsing to the legitimate result zero. -/
private def countResidualLandings :
    Nat → LocalDateTime → Instant → Instant → Option Int
  | 0, _, _, _ => none
  | fuel + 1, current, currentInstant, later =>
      match calendarDayLanding? current currentInstant 1 with
      | none => none
      | some (next, landing) =>
          if landing.epochMillis ≤ later.epochMillis then
            (countResidualLandings fuel next landing later).map (1 + ·)
          else
            some 0

/-- Unsigned kernel day count over ordered operands: make one `365 × whole-years` calendar jump, then count stateful residual day landings. -/
private def forwardDifferenceInDays? (earlier : LocalDateTime)
    (earlierInstant : Instant) (later : LocalDateTime)
    (laterInstant : Instant) : Option Int := do
  let years ← wholeYearsForward? earlier earlierInstant later laterInstant
  let seedDays := years * 365
  let (seeded, seededInstant) ←
    calendarDayLanding? earlier earlierInstant (seedDays : Int)
  let fuel :=
    Int.toNat
      (later.date.unixEpochDay - seeded.date.unixEpochDay) + 1
  let residual ←
    countResidualLandings fuel seeded seededInstant laterInstant
  pure (seedDays + residual)

/-- Signed stateful calendar-day count for two already resolved Berlin values. The exact instants are authoritative in overlaps; their decoded local labels drive calendar landings. -/
def differenceResolvedInDays? (first : LocalDateTime) (firstInstant : Instant)
    (second : LocalDateTime) (secondInstant : Instant) : Option Int :=
  if firstInstant.epochMillis < secondInstant.epochMillis then
    forwardDifferenceInDays? first firstInstant second secondInstant
  else if secondInstant.epochMillis < firstInstant.epochMillis then
    (forwardDifferenceInDays? second secondInstant first firstInstant).map (-·)
  else
    some 0

/-- Signed stateful calendar-day count after both fresh labels resolve under the pinned Berlin profile. -/
def differenceInDays? (first second : LocalDateTime) : Option Int := do
  let firstInstant ← resolveLocal? first
  let secondInstant ← resolveLocal? second
  differenceResolvedInDays? first firstInstant second secondInstant

end A12Kernel.EuropeBerlinLegacyProfile

namespace A12Kernel.ModelZone

/-- Signed UTC calendar-day count. With no offset transitions, this is exact whole-day truncation in authored operand order. -/
def utcDifferenceInDays (first second : LocalDateTime) : Int :=
  (second.resolveUtc.epochMillis - first.resolveUtc.epochMillis).tdiv 86400000

namespace ConcreteProfile

/-- Evaluate day difference from exact instants plus their already decoded local labels. UTC needs only instant identity; Berlin preserves the local state required by calendar stepping. -/
def differenceResolvedInDays? (profile : ConcreteProfile)
    (first : LocalDateTime) (firstInstant : Instant)
    (second : LocalDateTime) (secondInstant : Instant) : Option Int :=
  match profile with
  | .utc =>
      some ((secondInstant.epochMillis - firstInstant.epochMillis).tdiv 86400000)
  | .europeBerlin =>
      EuropeBerlinLegacyProfile.differenceResolvedInDays?
        first firstInstant second secondInstant

/-- Evaluate day difference after the caller has selected one of the concrete profiles. Fresh-label or internal profile failure remains distinct from unsupported id selection. -/
def differenceInDays? (profile : ConcreteProfile)
    (first second : LocalDateTime) : Option Int := do
  let firstInstant ← profile.resolveLocal? first
  let secondInstant ← profile.resolveLocal? second
  profile.differenceResolvedInDays? first firstInstant second secondInstant

end ConcreteProfile

/-- Compatibility String dispatch for the currently implemented model-zone profiles. Unselected ids return `none`; Berlin behavior is never extrapolated to them. -/
def concreteDifferenceInDays? (zoneId : String)
    (first second : LocalDateTime) : Option Int :=
  (ConcreteProfile.ofId? zoneId).bind
    (·.differenceInDays? first second)

end A12Kernel.ModelZone
