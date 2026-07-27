import A12Kernel.Elaboration.ConstructedDateEvaluation

/-! # Dynamic checked constructed-Date execution locks -/

namespace A12Kernel.Conformance.ConstructedDateDynamic

open A12Kernel

private def model : FlatModel := { fields := [], timeZoneId := "UTC" }

private def sources : SurfaceConstructedDateComponents := {
  day := .todayExtractor .day, month := .todayExtractor .month
  year := .complete (.todayExtractor .year)
}

private def checked? : Option (CheckedConstructedDateComponents model) :=
  (elaborateConstructedDateSources model sources).toOption

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

private def evaluate? (world : Option World) := do
  let checked ← checked?
  let input ← document?
  some (checked.evaluate .computation input world)

private def realParts? (world : Option World) : Option DateParts := do
  let result ← evaluate? world
  match result with
  | .ok (.resolved (.real parts)) => some parts
  | _ => none

private def shift? (world : World) := do
  let source ← checked?
  let input ← document?
  let shift : CheckedConstructedDateShift model :=
    { source, unit := .days, amount := .literal 1 }
  some (shift.evaluate
    .computation input (some world))

private def shiftedParts? (world : World) : Option DateParts := do
  let result ← shift? world
  match result with
  | .ok (.value parts false) => some parts
  | _ => none

private def missingAndUnavailable? (now : Instant) : Option (Bool × Bool) := do
  let missing ← evaluate? none
  let unavailable ← evaluate? (some { now })
  pure (
    (match missing with | .error .todayWorldRequired => true | _ => false),
    (match unavailable with | .error (.todayUnavailable "UTC") => true | _ => false))

/- Changing only the explicit world across UTC midnight changes all three components. -/
example : (do
    let first ← worldAt? 2024 6 30 23 59
    let second ← worldAt? 2024 7 1 0 0
    let firstResult ← realParts? (some first)
    let secondResult ← realParts? (some second)
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
    shiftedParts? world) =
    some { year := 2024, month := 7, day := 2 } := by
  native_decide

end A12Kernel.Conformance.ConstructedDateDynamic
