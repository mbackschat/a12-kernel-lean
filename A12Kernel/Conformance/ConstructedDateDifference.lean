import A12Kernel.Semantics.ConstructedDateDifference

/-! # Constructed-Date legacy-hybrid completed-period locks -/

namespace A12Kernel.Conformance.ConstructedDateDifference

open A12Kernel

private def constructed (year : Int) (month day : Nat) : DateConstructionResult :=
  .real { year, month, day }

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

end A12Kernel.Conformance.ConstructedDateDifference
