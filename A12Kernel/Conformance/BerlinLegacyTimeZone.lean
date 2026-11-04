import A12Kernel.Semantics.BerlinLegacyTimeZone

/-! # Versioned Europe/Berlin timezone locks

These cases separate historical table lookup, local mean time before 1893, post-1997 recurrence, gap resolution one gap later, earlier-offset overlap selection, and exact instant preservation (spec/05 §5, §5.1, kernel 31.1.1). General model-zone dispatch, parsing, cells, and wall-day landing remain outside.
-/

namespace A12Kernel.Conformance.BerlinLegacyTimeZone

open A12Kernel

private def dateTime (year : Int) (month day hour minute second : Nat)
    (admissible :
      (LocalDateTime.ofYmdHms? year month day hour minute second).isSome) :
    LocalDateTime :=
  (LocalDateTime.ofYmdHms? year month day hour minute second).get admissible

private def matchingOffsetCount (dateTime : LocalDateTime) : Nat :=
  (EuropeBerlinLegacyProfile.validOffsets dateTime.resolveUtc.epochMillis).length

private def midnightMatchingOffsetCount? (date : CivilDate) : Option Nat := do
  let fullDate ← FullDate.ofCivil? date
  let midnight ← LocalDateTime.ofDateHms? fullDate 0 0 0
  pure (matchingOffsetCount midnight)

private def midnightsUnique : Nat → CivilDate → Bool
  | 0, _ => true
  | fuel + 1, date =>
      midnightMatchingOffsetCount? date == some 1 &&
        match date.next? with
        | some next => midnightsUnique fuel next
        | none => false

private def recurrenceMidnightsUnique? : Option Bool := do
  let first ← CivilDate.ofYmd? 1998 1 1
  let afterLast ← CivilDate.ofYmd? 2101 1 1
  let count := Int.toNat (afterLast.unixEpochDay - first.unixEpochDay)
  pure (midnightsUnique count first)

private def intervalContainsMidnight (start width : Int) : Bool :=
  let secondOfDay := start % 86400
  decide (0 < width ∧
    (secondOfDay = 0 ∨ 86400 < secondOfDay + width))

private def historicalMidnightDiscontinuities? :
    List EuropeBerlinLegacyProfile.Transition → Int →
      Option (Nat × Nat)
  | [], _ => some (0, 0)
  | item :: rest, beforeOffset => do
      let boundary ← item.epochSecond?
      let afterOffset := item.offsetSecondsAfter
      let gap :=
        if beforeOffset < afterOffset &&
            intervalContainsMidnight
              (boundary + beforeOffset) (afterOffset - beforeOffset)
        then 1 else 0
      let overlap :=
        if afterOffset < beforeOffset &&
            intervalContainsMidnight
              (boundary + afterOffset) (beforeOffset - afterOffset)
        then 1 else 0
      let (laterGaps, laterOverlaps) ←
        historicalMidnightDiscontinuities? rest afterOffset
      pure (gap + laterGaps, overlap + laterOverlaps)

/- The pinned table holds the end of local mean time and the 62 transitions from 1916; before 1893-04-01 local midnight the offset is LMT `+3208` (a12-dmkits `BerlinHistoricalTzDiffTest`, kernel 31.1.1). -/
example :
    EuropeBerlinLegacyProfile.transitions.length = 63 ∧
      EuropeBerlinLegacyProfile.offsetSecondsAt?
          (dateTime 1893 3 31 23 6 31 (by native_decide)).resolveUtc = some 3208 ∧
      EuropeBerlinLegacyProfile.offsetSecondsAt?
          (dateTime 1893 3 31 23 6 32 (by native_decide)).resolveUtc = some 3600 ∧
      EuropeBerlinLegacyProfile.offsetSecondsAt?
          (dateTime 1900 1 1 0 0 0 (by native_decide)).resolveUtc = some 3600 ∧
      EuropeBerlinLegacyProfile.offsetSecondsAt?
          (dateTime 1916 4 30 21 59 59 (by native_decide)).resolveUtc = some 3600 ∧
      EuropeBerlinLegacyProfile.offsetSecondsAt?
          (dateTime 1916 4 30 22 0 0 (by native_decide)).resolveUtc = some 7200 := by
  native_decide

/- The historical table retains CEMT and the different pre-1996 autumn schedule. -/
example :
    EuropeBerlinLegacyProfile.offsetSecondsAt?
        (dateTime 1945 5 24 0 0 0 (by native_decide)).resolveUtc =
      some 10800 ∧
    EuropeBerlinLegacyProfile.offsetSecondsAt?
        (dateTime 1995 9 24 1 0 0 (by native_decide)).resolveUtc = some 3600 := by
  native_decide

/- The 1997 table boundary and 1998 recurrence are non-overlapping. -/
example :
    EuropeBerlinLegacyProfile.offsetSecondsAt?
        (dateTime 1997 10 26 0 59 59 (by native_decide)).resolveUtc =
      some 7200 ∧
    EuropeBerlinLegacyProfile.offsetSecondsAt?
        (dateTime 1997 10 26 1 0 0 (by native_decide)).resolveUtc = some 3600 ∧
    EuropeBerlinLegacyProfile.offsetSecondsAt?
        (dateTime 1998 3 29 1 0 0 (by native_decide)).resolveUtc = some 7200 := by
  native_decide

/- A modern gap label resolves one gap later, read at the offset in force before the gap, and an overlap label takes the earlier, summer offset. -/
example :
    EuropeBerlinLegacyProfile.resolveLocal?
        (dateTime 2025 3 30 2 30 0 (by native_decide)) =
      some ((dateTime 2025 3 30 2 30 0 (by native_decide)).resolveUtc.shiftHours (-1)) := by
  native_decide
example :
    EuropeBerlinLegacyProfile.resolveLocal?
        (dateTime 2025 10 26 2 30 0 (by native_decide)) =
      some ((dateTime 2025 10 26 2 30 0 (by native_decide)).resolveUtc.shiftHours (-2)) := by
  native_decide

/- The 1945 CEST-to-CEMT gap resolves one gap later, measured on kernel 31.1.1. The CEMT-to-CEST overlap row applies the general earlier-offset rule; no lock measures that historical overlap. -/
example :
    EuropeBerlinLegacyProfile.resolveLocal?
        (dateTime 1945 5 24 2 30 0 (by native_decide)) =
      some ((dateTime 1945 5 24 2 30 0 (by native_decide)).resolveUtc.shiftHours (-2)) := by
  native_decide
example :
    EuropeBerlinLegacyProfile.resolveLocal?
        (dateTime 1945 9 24 2 30 0 (by native_decide)) =
      some ((dateTime 1945 9 24 2 30 0 (by native_decide)).resolveUtc.shiftHours (-3)) := by
  native_decide

/- The pinned table has exactly one midnight gap, the end of local mean time, which skips 1893-04-01 00:00:00 to 00:06:31, and one midnight overlap, witnessed by both valid offsets at 1916-10-01. Every midnight in a bounded post-table recurrence span has exactly one valid offset. -/
example :
    historicalMidnightDiscontinuities?
        EuropeBerlinLegacyProfile.transitions 3208 = some (1, 1) ∧
      matchingOffsetCount
        (dateTime 1916 10 1 0 0 0 (by native_decide)) = 2 ∧
      recurrenceMidnightsUnique? = some true := by
  native_decide

/- One hour after `01:30` CEST is the daylight `02:30`, which a fresh `02:30` label now resolves to as well (a12-dmkits `OverlapInstantInComputationDiffTest`); two hours after is the standard-time `02:30`, which no label reaches. -/
example :
    (EuropeBerlinLegacyProfile.resolveLocal?
        (dateTime 2024 10 27 1 30 0 (by native_decide))).map
          (fun instant => instant.shiftHours 1) =
      EuropeBerlinLegacyProfile.resolveLocal?
        (dateTime 2024 10 27 2 30 0 (by native_decide)) := by
  native_decide
example :
    (EuropeBerlinLegacyProfile.resolveLocal?
        (dateTime 2024 10 27 1 30 0 (by native_decide))).map
          (fun instant => instant.shiftHours 2) ≠
      EuropeBerlinLegacyProfile.resolveLocal?
        (dateTime 2024 10 27 2 30 0 (by native_decide)) := by
  native_decide

/- **The overlap's second instant is not label-reachable.** The fall-back label `02:15` denotes two instants an hour apart, and fresh resolution selects the earlier, CEST one (a12-dmkits `DstTimeZoneDiffTest`). The later CET instant decodes back to that same label, so the two are label-identical and instant-distinct: a value carrying the later one can only have obtained it by retaining an instant or by a shift preferring its source's CET offset, never by resolving text. -/
example :
    let label := dateTime 2024 10 27 2 15 0 (by native_decide)
    let selected : Instant := { epochMillis := 1729988100000 }
    let later : Instant := { epochMillis := 1729991700000 }
    EuropeBerlinLegacyProfile.resolveLocal? label = some selected ∧
      selected.epochMillis + 3600000 = later.epochMillis ∧
      (EuropeBerlinLegacyProfile.offsetSecondsAt? selected,
        EuropeBerlinLegacyProfile.offsetSecondsAt? later) =
        (some 7200, some 3600) := by
  native_decide

/- A preferred offset decides an overlap when it is valid there: preferring CET selects the later instant, and preferring an offset the label cannot take falls back to the earlier one. -/
example :
    let label := dateTime 2024 10 27 2 15 0 (by native_decide)
    EuropeBerlinLegacyProfile.resolvePreferring? label (some 3600) =
        some { epochMillis := 1729991700000 } ∧
      EuropeBerlinLegacyProfile.resolvePreferring? label (some 10800) =
        some { epochMillis := 1729988100000 } := by
  native_decide

/- A spring-forward gap label resolves one gap later, to the same instant as the label `03:30` after it (a12-dmkits `DstTimeZoneDiffTest`), so two labels share one instant; its neighbour before the gap stays an hour earlier. -/
example :
    let gap := dateTime 2024 3 31 2 30 0 (by native_decide)
    let before := dateTime 2024 3 31 1 30 0 (by native_decide)
    let after := dateTime 2024 3 31 3 30 0 (by native_decide)
    (EuropeBerlinLegacyProfile.resolveLocal? gap).map (·.epochMillis) =
        some 1711848600000 ∧
      (EuropeBerlinLegacyProfile.resolveLocal? before).map (·.epochMillis) =
        some 1711845000000 ∧
      (EuropeBerlinLegacyProfile.resolveLocal? after).map (·.epochMillis) =
        some 1711848600000 := by
  native_decide

end A12Kernel.Conformance.BerlinLegacyTimeZone
