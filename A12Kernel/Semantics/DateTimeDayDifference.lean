import A12Kernel.Semantics.BerlinLegacyCalendarArithmetic

/-! # Concrete model-zone calendar-day differences

This capsule implements the resolved `DifferenceInDays` core for UTC and the versioned Europe/Berlin legacy profile. Berlin qualifies the kernel's whole-year candidate through the distinct `Calendar.YEAR` mutation, makes the `365 × whole-years` lower-bound day landing, then counts stateful residual day landings in authored operand order.

The field mutations and completed month/year qualification are owned by `BerlinLegacyCalendarArithmetic`. Parsing, Date-versus-DateTime admission, empty and malformed operands, calendar identity outside the concrete profiles, numeric result storage, validation polarity, and a general model-zone interface remain separate.
-/

namespace A12Kernel.EuropeBerlinLegacyProfile

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
