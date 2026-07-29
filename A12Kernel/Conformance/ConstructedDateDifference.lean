import A12Kernel.Elaboration.ConstructedDateEvaluation

/-! # Constructed-Date legacy-hybrid completed-period locks -/

namespace A12Kernel.Conformance.ConstructedDateDifference

open A12Kernel

private def constructed (year : Int) (month day : Nat) : DateConstructionResult :=
  .real { year, month, day }

private def model (zoneId : String) : FlatModel := {
  fields := []
  timeZoneId := zoneId
}

private def sources (parts : DateParts) : SurfaceConstructedDateComponents := {
  day := .constant s!"{parts.day}"
  month := .constant s!"{parts.month}"
  year := .complete (.constant s!"{parts.year}")
}

private def documentFor? (checkedModel : FlatModel) :
    Option (CheckedDocument checkedModel) := do
  let prepared ←
    (prepareFlatStringContext { now := { epochMillis := 0 } }
      builtinStringPatternCompiler checkedModel).toOption
  checkDocument prepared "en_US"
    { instantiatedRows := [], cells := [] } |>.toOption

private def checkedDifference? (zoneId : String)
    (unit : DateShiftUnit) (firstParts secondParts : DateParts) :
    Option ConstructedDateNumericResult := do
  let checkedModel := model zoneId
  let first ←
    (elaborateConstructedDateSources
      checkedModel (sources firstParts)).toOption
  let second ←
    (elaborateConstructedDateSources
      checkedModel (sources secondParts)).toOption
  let input ← documentFor? checkedModel
  if unitAdmitted :
      first.profile.admitsConstructedDateDifference unit = true then
    let checked : CheckedConstructedDateDifference checkedModel := {
      first, second, unit, unitAdmitted
    }
    match checked.evaluate .validation input none with
    | .ok (.ok result) => some result
    | _ => none
  else
    none

/- The cutover-hole landing makes 15 October incomplete and 20 October complete from 10 September. -/
example :
    (constructed 1582 9 10).differenceLegacy? .months
        (constructed 1582 10 15) = some (.value 0 false) ∧
      (constructed 1582 9 10).differenceLegacy? .months
        (constructed 1582 10 20) = some (.value 1 false) := by
  native_decide

/- The same landing separates complete years and months from the preceding October. -/
example :
    (constructed 1581 10 10).differenceLegacy? .years
        (constructed 1582 10 15) = some (.value 0 false) ∧
      (constructed 1581 10 10).differenceLegacy? .months
        (constructed 1582 10 15) = some (.value 11 false) ∧
      (constructed 1581 10 10).differenceLegacy? .years
        (constructed 1582 10 20) = some (.value 1 false) ∧
      (constructed 1581 10 10).differenceLegacy? .months
        (constructed 1582 10 20) = some (.value 12 false) := by
  native_decide

/- Authored operand order is restored only after the nonnegative completed-period count. -/
example :
    (constructed 1582 10 20).differenceLegacy? .months
        (constructed 1582 9 10) = some (.value (-1) false) ∧
      (constructed 1582 10 20).differenceLegacy? .years
        (constructed 1582 10 20) = some (.value 0 false) := by
  native_decide

/- Formal unavailability dominates missingness; otherwise incomplete and unreal both yield zero with distinct provenance. -/
example :
    DateConstructionResult.incomplete.differenceLegacy? .months
        (constructed 1582 10 20) = some (.value 0 true) ∧
      DateConstructionResult.unreal.differenceLegacy? .months
        (constructed 1582 10 20) = some (.value 0 false) ∧
      DateConstructionResult.incomplete.differenceLegacy? .years
        .unknown = some .unavailable := by
  native_decide

/- The decoded proleptic counter says one month at the first cutover-side label; the constructed calendar says zero. -/
example :
    DateDifferenceUnit.months.between
        { year := 1582, month := 9, day := 10 }
        { year := 1582, month := 10, day := 15 } = 1 ∧
      (constructed 1582 9 10).differenceLegacy? .months
        (constructed 1582 10 15) = some (.value 0 false) := by
  native_decide

/- Widening the checked profile certificate leaves all three UTC/GMT legacy-hybrid branches unchanged. -/
example :
    checkedDifference? "UTC" .days
        { year := 2024, month := 1, day := 1 }
        { year := 2024, month := 1, day := 2 } =
      some (.value 1 false) ∧
    checkedDifference? "UTC" .months
        { year := 2024, month := 1, day := 31 }
        { year := 2024, month := 2, day := 28 } =
      some (.value 0 false) ∧
    checkedDifference? "UTC" .years
        { year := 2023, month := 1, day := 1 }
        { year := 2024, month := 1, day := 1 } =
      some (.value 1 false) := by
  native_decide

/- Berlin constructed Dates reuse the exact resolved calendar-day account, including the repeated-midnight source-offset landing. -/
example :
    checkedDifference? "Europe/Berlin" .days
        { year := 1916, month := 9, day := 30 }
        { year := 1916, month := 10, day := 1 } =
      some (.value 1 false) := by
  native_decide

/- Berlin completed years use the February-promoted candidate rather than plain year subtraction. -/
example :
    checkedDifference? "Europe/Berlin" .years
        { year := 1999, month := 2, day := 28 }
        { year := 2000, month := 2, day := 28 } =
      some (.value 0 false) ∧
    checkedDifference? "Europe/Berlin" .years
        { year := 1999, month := 2, day := 28 }
        { year := 2000, month := 2, day := 29 } =
      some (.value 1 false) := by
  native_decide

/- The 365-times-years seed remains a lower bound: the leap day contributes one residual day, and authored order restores sign. -/
example :
    checkedDifference? "Europe/Berlin" .days
        { year := 2000, month := 2, day := 28 }
        { year := 2001, month := 2, day := 28 } =
      some (.value 366 false) ∧
    checkedDifference? "Europe/Berlin" .days
        { year := 2001, month := 2, day := 28 }
        { year := 2000, month := 2, day := 28 } =
      some (.value (-366) false) := by
  native_decide

/- Berlin months use their independently closed candidate loop; UTC keeps all three legacy-hybrid units. -/
example :
    ModelZone.ConcreteProfile.admitsConstructedDateDifference
        .europeBerlin .months = true ∧
      ModelZone.ConcreteProfile.admitsConstructedDateDifference
        .europeBerlin .days = true ∧
      ModelZone.ConcreteProfile.admitsConstructedDateDifference
        .europeBerlin .years = true ∧
      ModelZone.ConcreteProfile.admitsConstructedDateDifference
        .utc .months = true := by
  native_decide

/- Month completion tests one fresh source-relative landing: end-of-month clamping, reverse sign, and the February year-seed boundary remain observable. -/
example :
    checkedDifference? "Europe/Berlin" .months
        { year := 2024, month := 1, day := 31 }
        { year := 2024, month := 2, day := 28 } =
      some (.value 0 false) ∧
    checkedDifference? "Europe/Berlin" .months
        { year := 2024, month := 1, day := 31 }
        { year := 2024, month := 2, day := 29 } =
      some (.value 1 false) ∧
    checkedDifference? "Europe/Berlin" .months
        { year := 2024, month := 2, day := 29 }
        { year := 2024, month := 1, day := 31 } =
      some (.value (-1) false) ∧
    checkedDifference? "Europe/Berlin" .months
        { year := 1999, month := 2, day := 28 }
        { year := 2000, month := 2, day := 28 } =
      some (.value 12 false) ∧
    checkedDifference? "Europe/Berlin" .years
        { year := 1999, month := 2, day := 28 }
        { year := 2000, month := 2, day := 28 } =
      some (.value 0 false) := by
  native_decide

/- The repeated 1916 midnight and non-value precedence both flow through the same checked Berlin month branch. -/
example :
    CheckedConstructedDateDifference.differenceResolved?
        .europeBerlin .days .incomplete (constructed 2000 2 29) =
      some (.value 0 true) ∧
    CheckedConstructedDateDifference.differenceResolved?
        .europeBerlin .years .unreal (constructed 2000 2 29) =
      some (.value 0 false) ∧
    CheckedConstructedDateDifference.differenceResolved?
        .europeBerlin .months (constructed 1916 9 1)
          (constructed 1916 10 1) = some (.value 1 false) := by
  native_decide

end A12Kernel.Conformance.ConstructedDateDifference
