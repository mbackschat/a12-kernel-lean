import A12Kernel.Elaboration.ConstructedDateEvaluation

/-! # Dynamic checked constructed-Date execution locks -/

namespace A12Kernel.Conformance.ConstructedDateDynamic

open A12Kernel

private def model : FlatModel := { fields := [], timeZoneId := "UTC" }

private def todaySources : SurfaceConstructedDateComponents := {
  day := .todayExtractor .day, month := .todayExtractor .month
  year := .complete (.todayExtractor .year)
}

private def nowSources : SurfaceConstructedDateComponents := {
  day := .nowExtractor .day, month := .nowExtractor .month
  year := .complete (.nowExtractor .year)
}

private def document? : Option (CheckedDocument model) := do
  let prepared ←
    (prepareFlatStringContext { now := { epochMillis := 0 } }
      builtinStringPatternCompiler model).toOption
  checkDocument prepared "en_US"
    { instantiatedRows := [], cells := [] } |>.toOption

private def instant? (year : Int) (month day hour minute : Nat) :
    Option Instant :=
  (LocalDateTime.ofYmdHms? year month day hour minute 0).map (·.resolveUtc)

private def worldAt? (year : Int) (month day hour minute : Nat) :
    Option World := do
  let now ← instant? year month day hour minute
  pure { now, modelZoneRules := ModelZone.concreteRules }

private def evaluateSources? (sources : SurfaceConstructedDateComponents)
    (world : Option World) := do
  let checked ← (elaborateConstructedDateSources model sources).toOption
  let input ← document?
  some (checked.evaluate .computation input world)

private def realParts? (sources : SurfaceConstructedDateComponents)
    (world : Option World) : Option DateParts := do
  let result ← evaluateSources? sources world
  match result with
  | .ok (.resolved (.real parts)) => some parts
  | _ => none

private def shift? (sources : SurfaceConstructedDateComponents)
    (world : World) := do
  let source ← (elaborateConstructedDateSources model sources).toOption
  let input ← document?
  let shift : CheckedConstructedDateShift model :=
    { source, unit := .days, amount := .literal 1 }
  some (shift.evaluate
    .computation input (some world))

private def shiftedParts? (sources : SurfaceConstructedDateComponents)
    (world : World) : Option DateParts := do
  let result ← shift? sources world
  match result with
  | .ok (.value parts false) => some parts
  | _ => none

private def missingAndUnavailable? (now : Instant) : Option (Bool × Bool) := do
  let missing ← evaluateSources? todaySources none
  let unavailable ← evaluateSources? todaySources (some { now })
  pure (
    (match missing with | .error .todayWorldRequired => true | _ => false),
    (match unavailable with | .error (.todayUnavailable "UTC") => true | _ => false))

private def nowMissingWorld? : Option Bool := do
  let result ← evaluateSources? nowSources none
  pure (match result with | .error .nowWorldRequired => true | _ => false)

/- Changing only the explicit world across UTC midnight changes all three components. -/
example : (do
    let first ← worldAt? 2024 6 30 23 59
    let second ← worldAt? 2024 7 1 0 0
    let firstResult ← realParts? todaySources (some first)
    let secondResult ← realParts? todaySources (some second)
    pure (firstResult, secondResult)) =
    some (
      { year := 2024, month := 6, day := 30 },
      { year := 2024, month := 7, day := 1 }) := by
  native_decide

/- Missing world and missing model-zone capability remain distinct structural faults. -/
example : (do
    let now ← instant? 2024 7 1 0 0
    missingAndUnavailable? now) = some (true, true) := by
  native_decide

/- The composed shift receives the same world as its constructed source. -/
example : (do
    let world ← worldAt? 2024 7 1 0 0
    shiftedParts? todaySources world) =
    some { year := 2024, month := 7, day := 2 } := by
  native_decide

/- `Now` retains the exact world instant and does not consult `Today`'s zone-rule oracle. -/
example : (do
    let first ← worldAt? 2024 6 30 23 59
    let second ← worldAt? 2024 7 1 0 0
    let firstResult ← realParts? nowSources (some first)
    let secondResult ← realParts? nowSources (some second)
    let withoutRules ← realParts? nowSources (some { now := second.now })
    pure (firstResult, secondResult, withoutRules)) =
    some (
      { year := 2024, month := 6, day := 30 },
      { year := 2024, month := 7, day := 1 },
      { year := 2024, month := 7, day := 1 }) := by
  native_decide

/- `Now` still requires the caller's execution world; no ambient clock is sampled. -/
example : nowMissingWorld? = some true := by
  native_decide

/- A composed consumer receives the same exact `Now` world as its constructed source. -/
example : (do
    let world ← worldAt? 2024 7 1 0 0
    shiftedParts? nowSources world) =
    some { year := 2024, month := 7, day := 2 } := by
  native_decide

end A12Kernel.Conformance.ConstructedDateDynamic
