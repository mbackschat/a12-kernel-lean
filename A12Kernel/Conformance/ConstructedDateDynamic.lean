import A12Kernel.Elaboration.ConstructedDateEvaluation

/-! # Dynamic checked constructed-Date execution locks -/

namespace A12Kernel.Conformance.ConstructedDateDynamic

open A12Kernel

private def model : FlatModel := { fields := [], timeZoneId := "UTC" }
private def berlinModel : FlatModel :=
  { fields := [], timeZoneId := "Europe/Berlin", baseYear := some 1583 }

private def todaySources : SurfaceConstructedDateComponents := {
  day := .todayExtractor .day, month := .todayExtractor .month
  year := .complete (.todayExtractor .year)
}

private def nowSources : SurfaceConstructedDateComponents := {
  day := .nowExtractor .day, month := .nowExtractor .month
  year := .complete (.nowExtractor .year)
}

private def preFloorSources : SurfaceConstructedDateComponents := {
  day := .constant "15", month := .constant "10"
  year := .baseYear
}

private def berlinBeforeOverlapSources : SurfaceConstructedDateComponents := {
  day := .constant "30", month := .constant "9"
  year := .baseYear
}

private def berlinAfterOverlapSources : SurfaceConstructedDateComponents := {
  day := .constant "2", month := .constant "10"
  year := .baseYear
}

private def berlinSeptemberFirstSources : SurfaceConstructedDateComponents := {
  day := .constant "1", month := .constant "9"
  year := .baseYear
}

private def berlinMarchFirstSources : SurfaceConstructedDateComponents := {
  day := .constant "1", month := .constant "3"
  year := .baseYear
}

private def berlinNovemberFirstSources : SurfaceConstructedDateComponents := {
  day := .constant "1", month := .constant "11"
  year := .baseYear
}

private def berlinJanuaryEndSources : SurfaceConstructedDateComponents := {
  day := .constant "31", month := .constant "1"
  year := .baseYear
}

private def berlinMarchEndSources : SurfaceConstructedDateComponents := {
  day := .constant "31", month := .constant "3"
  year := .baseYear
}

private def berlinNormalSources : SurfaceConstructedDateComponents := {
  day := .constant "29", month := .constant "9"
  year := .baseYear
}

private def berlinOctoberFirstSources : SurfaceConstructedDateComponents := {
  day := .constant "1", month := .constant "10"
  year := .baseYear
}

private def berlinFebruaryEndSources : SurfaceConstructedDateComponents := {
  day := .constant "28", month := .constant "2"
  year := .baseYear
}

private def documentFor? (checkedModel : FlatModel) :
    Option (CheckedDocument checkedModel) := do
  let prepared ←
    (prepareFlatStringContext { now := { epochMillis := 0 } }
      builtinStringPatternCompiler checkedModel).toOption
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
  let input ← documentFor? model
  some (checked.evaluate .computation input world)

private def evaluateBerlinSources?
    (sources : SurfaceConstructedDateComponents) (world : Option World) := do
  let checked ←
    (elaborateConstructedDateSources berlinModel sources).toOption
  let input ← documentFor? berlinModel
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
  let input ← documentFor? model
  let shift : CheckedConstructedDateShift model :=
    { source, unit := .days, amount := .literal 1 }
  some (shift.evaluate
    .computation input (some world))

private def shiftedParts? (sources : SurfaceConstructedDateComponents)
    (world : World) : Option DateParts := do
  let result ← shift? sources world
  match result with
  | .ok (.value _ parts false) => some parts
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

private def berlinPreFloorUnsupported? : Option Bool := do
  let result ← evaluateBerlinSources? preFloorSources none
  pure (match result with
    | .error (.profileDateUnsupported "Europe/Berlin"
        { year := 1583, month := 10, day := 15 }) => true
    | _ => false)

private def berlinShift?
    (year : Int)
    (sources : SurfaceConstructedDateComponents)
    (unit : DateShiftUnit) (amount : Rat) :
    Option (Except ConstructedDateShiftFault ConstructedDateShiftResult) := do
  let checkedModel : FlatModel :=
    { fields := [], timeZoneId := "Europe/Berlin", baseYear := some year }
  let source ←
    (elaborateConstructedDateSources
      checkedModel sources).toOption
  let input ← documentFor? checkedModel
  let shift : CheckedConstructedDateShift checkedModel := {
    source
    unit
    amount := .literal amount
  }
  some (shift.evaluate .computation input none)

private def berlinShiftSeparators? : Option Bool := do
  let forward ← berlinShift? 1916 berlinBeforeOverlapSources .days 1
  let longForward ←
    berlinShift? 1916 berlinMarchFirstSources .days 214
  let normal ← berlinShift? 1916 berlinNormalSources .days 1
  let reverse ← berlinShift? 1916 berlinAfterOverlapSources .days (-1)
  let ordinaryReverse ←
    berlinShift? 1916 berlinBeforeOverlapSources .days (-1)
  let overlapLabel ← LocalDateTime.ofYmdHms? 1916 10 1 0 0 0
  let normalLabel ← LocalDateTime.ofYmdHms? 1916 9 30 0 0 0
  let freshOverlap ←
    ModelZone.ConcreteProfile.europeBerlin.resolveLocal? overlapLabel
  let freshNormal ←
    ModelZone.ConcreteProfile.europeBerlin.resolveLocal? normalLabel
  pure (match
      forward, longForward, freshOverlap, normal, freshNormal, reverse,
      ordinaryReverse with
    | .ok (.value { epochMillis := -1680487200000 }
          { year := 1916, month := 10, day := 1 } false),
        .ok (.value { epochMillis := -1680483600000 }
          { year := 1916, month := 10, day := 1 } false),
        { epochMillis := -1680483600000 },
        .ok (.value { epochMillis := -1680573600000 }
          { year := 1916, month := 9, day := 30 } false),
        { epochMillis := -1680573600000 },
        .ok (.value { epochMillis := -1680483600000 }
          { year := 1916, month := 10, day := 1 } false),
        .ok (.value { epochMillis := -1680660000000 }
          { year := 1916, month := 9, day := 29 } false) => true
    | _, _, _, _, _, _, _ => false)

private def berlinMonthShiftSeparators? : Option Bool := do
  let forward ←
    berlinShift? 1916 berlinSeptemberFirstSources .months 1
  let reverse ←
    berlinShift? 1916 berlinNovemberFirstSources .months (-1)
  let clampForward ←
    berlinShift? 1916 berlinJanuaryEndSources .months 1
  let clampReverse ←
    berlinShift? 1916 berlinMarchEndSources .months (-1)
  let ordinary ←
    berlinShift? 1916 berlinNormalSources .months 1
  pure (match forward, reverse, clampForward, clampReverse, ordinary with
    | .ok (.value { epochMillis := -1680483600000 }
          { year := 1916, month := 10, day := 1 } false),
        .ok (.value { epochMillis := -1680483600000 }
          { year := 1916, month := 10, day := 1 } false),
        .ok (.value { epochMillis := -1699059600000 }
          { year := 1916, month := 2, day := 29 } false),
        .ok (.value { epochMillis := -1699059600000 }
          { year := 1916, month := 2, day := 29 } false),
        .ok (.value { epochMillis := -1678064400000 }
          { year := 1916, month := 10, day := 29 } false) => true
    | _, _, _, _, _ => false)

private def berlinYearShiftSeparators? : Option Bool := do
  let forwardOverlap ←
    berlinShift? 1915 berlinOctoberFirstSources .years 1
  let reverseOverlap ←
    berlinShift? 1917 berlinOctoberFirstSources .years (-1)
  let leapForward ←
    berlinShift? 1915 berlinFebruaryEndSources .years 1
  let leapReverse ←
    berlinShift? 1917 berlinFebruaryEndSources .years (-1)
  let ordinary ←
    berlinShift? 1915 berlinNormalSources .years 1
  pure (match
      forwardOverlap, reverseOverlap, leapForward, leapReverse, ordinary with
    | .ok (.value { epochMillis := -1680483600000 }
          { year := 1916, month := 10, day := 1 } false),
        .ok (.value { epochMillis := -1680483600000 }
          { year := 1916, month := 10, day := 1 } false),
        .ok (.value { epochMillis := -1699059600000 }
          { year := 1916, month := 2, day := 29 } false),
        .ok (.value { epochMillis := -1699059600000 }
          { year := 1916, month := 2, day := 29 } false),
        .ok (.value { epochMillis := -1680660000000 }
          { year := 1916, month := 9, day := 29 } false) => true
    | _, _, _, _, _ => false)

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

/- UTC and Berlin read the same retained instant on opposite sides of local midnight. -/
example : (do
    let world ← worldAt? 2024 6 30 22 30
    let utcToday ← realParts? todaySources (some world)
    let utcNow ← realParts? nowSources (some world)
    let berlinTodayResult ← evaluateBerlinSources? todaySources (some world)
    let berlinNowResult ← evaluateBerlinSources? nowSources (some world)
    let berlinToday ← match berlinTodayResult with
      | .ok (.resolved (.real parts)) => some parts
      | _ => none
    let berlinNow ← match berlinNowResult with
      | .ok (.resolved (.real parts)) => some parts
      | _ => none
    pure (utcToday, utcNow, berlinToday, berlinNow)) =
    some (
      { year := 2024, month := 6, day := 30 },
      { year := 2024, month := 6, day := 30 },
      { year := 2024, month := 7, day := 1 },
      { year := 2024, month := 7, day := 1 }) := by
  native_decide

/- Berlin stays explicitly bounded at the stored-Date floor; UTC's separate Julian-side
   account is not silently reused. -/
example : berlinPreFloorUnsupported? = some true := by
  native_decide

/- Day addition carries the source offset: adjacent CEST selects the earlier overlap instant, while a long addition from CET selects the later instant at the same wall label. -/
example : berlinShiftSeparators? = some true := by
  native_decide

/- Month mutation instead selects the later CET instant in both directions and clamps both end-of-month directions to the same leap-day target. Its compute-time policy is not the source-offset day mechanism. -/
example : berlinMonthShiftSeparators? = some true := by
  native_decide

/- Year mutation also selects the later CET instant at the repeated midnight in both
   directions. Its separate February rule promotes the non-leap 28th to the target leap
   day; neither behavior can be inferred from day mutation. -/
example : berlinYearShiftSeparators? = some true := by
  native_decide

end A12Kernel.Conformance.ConstructedDateDynamic
