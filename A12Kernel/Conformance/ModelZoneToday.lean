import A12Kernel.Semantics.ModelZoneToday

/-! # Model-zone `Today` locks

These cases start from an injected exact validation instant and an already-selected model-zone profile. They distinguish UTC from Berlin local dates and require midnight to be resolved independently of the offset at the current instant. Arbitrary zone-id dispatch and legacy-calendar dates before the admitted positive-era Gregorian boundary remain outside the concrete profiles.
-/

namespace A12Kernel.Conformance.ModelZoneToday

private def utcInstant? (year : Int) (month day hour minute second : Nat) : Option Instant :=
  (LocalDateTime.ofYmdHms? year month day hour minute second).map
    LocalDateTime.resolveUtc

example : (do
    let now ← utcInstant? 2024 3 31 12 34 56
    let expected ← utcInstant? 2024 3 31 0 0 0
    pure (ModelZoneToday.utc? now = some expected)) = some true := by
  native_decide

example : (do
    let now ← utcInstant? 2024 3 30 23 30 0
    let expected ← utcInstant? 2024 3 30 23 0 0
    pure (ModelZoneToday.europeBerlin? now = some expected)) = some true := by
  native_decide

/- Berlin midnight on the spring-transition date still uses CET even when the current instant uses CEST. Reusing the current offset would incorrectly produce 22:00 UTC. -/
example : (do
    let now ← utcInstant? 2024 3 31 12 0 0
    let expected ← utcInstant? 2024 3 30 23 0 0
    let wrongCurrentOffsetProjection ← utcInstant? 2024 3 30 22 0 0
    pure (ModelZoneToday.europeBerlin? now = some expected ∧
      ModelZoneToday.europeBerlin? now ≠ some wrongCurrentOffsetProjection)) = some true := by
  native_decide

end A12Kernel.Conformance.ModelZoneToday
