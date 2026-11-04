import A12Kernel.Semantics.ModelZone
import A12Kernel.Semantics.FlatValidation

/-! # Model-zone capability locks

These cases cover `Today` from an injected exact validation instant and Base Year from a complete local label under an already-selected model-zone profile. They distinguish UTC from Berlin local dates and require midnight to be resolved independently of the offset at the current instant. Arbitrary zone-id dispatch and legacy-calendar dates before the admitted positive-era Gregorian boundary remain outside the concrete profiles.
-/

namespace A12Kernel.Conformance.ModelZone

private def utcInstant? (year : Int) (month day hour minute second : Nat) : Option Instant :=
  (LocalDateTime.ofYmdHms? year month day hour minute second).map
    LocalDateTime.resolveUtc

example : (do
    let now ← utcInstant? 2024 3 31 12 34 56
    let expected ← utcInstant? 2024 3 31 0 0 0
    pure (ModelZone.utcToday? now = some expected)) = some true := by
  native_decide

example : (do
    let expected ← utcInstant? 2019 12 31 23 0 0
    pure (ModelZone.concreteResolveLocal? "Europe/Berlin" 2020 1 1 0 0 0 =
      some expected)) = some true := by
  native_decide

/- The injected capability receives the selected endpoint label directly, including a pre-floor configured year that the concrete stored-Date profile does not support. -/
example :
    let expected : Instant := { epochMillis := 15001231 }
    let world : World :=
      { now := { epochMillis := 0 },
        modelZoneRules :=
          { ModelZoneRules.unavailable with
            resolveLocal? := fun zoneId year month day hour minute second =>
              if zoneId == "Legacy" && year == 1500 && month == 12 && day == 31 &&
                  hour == 0 && minute == 0 && second == 0 then
                some expected
              else none } }
    (FlatTemporalOperand.baseYearRangeValue "Legacy" 1500 .finish).resolve
      (({ read := fun _ =>
          { rawPresent := false, parsed := none, findings := [] } } : FlatContext).withWorld world) =
        .value expected true := by
  native_decide

example : (do
    let now ← utcInstant? 2024 3 30 23 30 0
    let expected ← utcInstant? 2024 3 30 23 0 0
    pure (ModelZone.europeBerlinToday? now = some expected)) = some true := by
  native_decide

/- Berlin midnight on the spring-transition date still uses CET even when the current instant uses CEST. Reusing the current offset would incorrectly produce 22:00 UTC. -/
example : (do
    let now ← utcInstant? 2024 3 31 12 0 0
    let expected ← utcInstant? 2024 3 30 23 0 0
    let wrongCurrentOffsetProjection ← utcInstant? 2024 3 30 22 0 0
    pure (ModelZone.europeBerlinToday? now = some expected ∧
      ModelZone.europeBerlinToday? now ≠ some wrongCurrentOffsetProjection)) = some true := by
  native_decide

/- Stored-text reality is proleptic with one zone-dependent exception (spec/05 §4, a12-dmkits `StoredDateCalendarDiffTest`): a Julian-only leap day is real under UTC and unreal under Berlin, while a proleptic common-year leap day after the cutover and the former cutover labels behave alike in both zones. -/
example :
    let parts (year : Int) (month day : Nat) : DateParts := { year, month, day }
    [ModelZone.ConcreteProfile.utc, .europeBerlin].map (fun profile =>
      [parts 1500 2 29, parts 1300 2 29, parts 1700 2 29, parts 1582 10 4, parts 1582 10 5,
        parts 1582 10 14].map profile.storedLabelReal) =
      [[true, true, false, true, true, true], [false, false, false, true, true, true]] := by
  native_decide

/- A Julian-only label resolves under UTC to its Julian instant, proleptic 1500-03-10 (spec/05 §1); under Berlin it names no instant. A proleptic label resolves as a fresh label in both. -/
example :
    let label (year : Int) (month day : Nat) : CalendarLabel := CalendarLabel.midnight { year, month, day }
    (ModelZone.ConcreteProfile.utc.resolveStoredLabel? (label 1500 2 29),
      ModelZone.ConcreteProfile.utc.resolveCalendarLabel? (label 1500 3 10),
      ModelZone.ConcreteProfile.europeBerlin.resolveStoredLabel? (label 1500 2 29),
      ModelZone.ConcreteProfile.europeBerlin.resolveStoredLabel? (label 1500 3 10) ==
        ModelZone.ConcreteProfile.europeBerlin.resolveCalendarLabel? (label 1500 3 10)) =
    (ModelZone.ConcreteProfile.utc.resolveCalendarLabel? (label 1500 3 10),
      some { epochMillis := -14825894400000 }, none, true) := by
  native_decide

end A12Kernel.Conformance.ModelZone
