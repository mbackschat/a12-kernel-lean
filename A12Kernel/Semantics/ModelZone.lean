import A12Kernel.Semantics.BerlinLegacyTimeZone

/-! # Versioned model-zone capability

This capsule derives the local civil date of an injected exact instant and independently resolves that date's midnight through the selected zone profile. The two steps must remain separate because the offset at midnight can differ from the offset at the current instant. It also adapts complete local labels to the same UTC and pinned Europe/Berlin resolvers, providing the first shared `ModelZoneRules` implementation for `Today`, Base Year, and later zone consumers.

The concrete date reconstruction uses the existing positive-era proleptic-Gregorian coordinate and A12 full-Date floor. A wider consumer supplies another `ModelZoneRules` value for other kernel-legal ids or pre-floor legacy-calendar behavior rather than treating these two profiles as the canonical zone ceiling.
-/

namespace A12Kernel.ModelZone

/-- Recover the admitted local civil date at one instant using the profile's offset at that instant. -/
def localDateAtOffset? (instant : Instant) (offsetSeconds : Int) : Option FullDate :=
  let localEpochDay :=
    (instant.epochMillis + offsetSeconds * 1000) / 86400000
  (CivilDate.ofUnixEpochDay? localEpochDay).bind FullDate.ofCivil?

/-- Resolve `Today` for an arbitrary already-selected zone profile. Offset selection at `instant` chooses the local date; fresh-label resolution separately chooses the offset at that date's midnight. -/
def resolve? (offsetSecondsAt? : Instant → Option Int)
    (resolveLocal? : LocalDateTime → Option Instant) (instant : Instant) : Option Instant := do
  let offsetSeconds ← offsetSecondsAt? instant
  let localDate ← localDateAtOffset? instant offsetSeconds
  let midnight ← LocalDateTime.ofDateHms? localDate 0 0 0
  resolveLocal? midnight

/-- `Today` under the model's default UTC profile. -/
def utcToday? (instant : Instant) : Option Instant :=
  resolve? (fun _ => some 0) (some ∘ LocalDateTime.resolveUtc) instant

/-- `Today` under the pinned Europe/Berlin legacy profile. -/
def europeBerlinToday? (instant : Instant) : Option Instant :=
  resolve? EuropeBerlinLegacyProfile.offsetSecondsAt?
    EuropeBerlinLegacyProfile.resolveLocal? instant

def concreteToday? (zoneId : String) (instant : Instant) : Option Instant :=
  if zoneId == "UTC" || zoneId == "GMT" then utcToday? instant
  else if zoneId == "Europe/Berlin" then europeBerlinToday? instant else none

def concreteResolveLocal? (zoneId : String) (year : Int)
    (month day hour minute second : Nat) : Option Instant := do
  let dateTime ← LocalDateTime.ofYmdHms? year month day hour minute second
  if zoneId == "UTC" || zoneId == "GMT" then some dateTime.resolveUtc
  else if zoneId == "Europe/Berlin" then EuropeBerlinLegacyProfile.resolveLocal? dateTime
  else none

def concreteRules : ModelZoneRules where
  today? := concreteToday?
  resolveLocal? := concreteResolveLocal?

end A12Kernel.ModelZone
