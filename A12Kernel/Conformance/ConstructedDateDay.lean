import A12Kernel.Semantics.ConstructedDateDay

/-! # Constructed-Date legacy-hybrid day locks -/

namespace A12Kernel.Conformance.ConstructedDateDay

open A12Kernel

private def constructed (year : Int) (month day : Nat) : DateConstructionResult :=
  .real { year, month, day }

/- One calendar day crosses the ten-label default cutover hole in either direction. -/
example :
    (constructed 1582 10 4).addLegacyDays? 1 =
        some (constructed 1582 10 15) ∧
      (constructed 1582 10 15).addLegacyDays? (-1) =
        some (constructed 1582 10 4) := by
  native_decide

/- The signed difference counts calendar steps rather than missing civil labels. -/
example :
    (constructed 1582 10 4).differenceLegacyDays?
        (constructed 1582 10 15) = some (.value 1 false) ∧
      (constructed 1582 10 15).differenceLegacyDays?
        (constructed 1582 10 4) = some (.value (-1) false) := by
  native_decide

/- Julian-side leap reality remains visible to day shifting and difference. -/
example :
    (constructed 1500 2 29).addLegacyDays? 1 =
        some (constructed 1500 3 1) ∧
      (constructed 1500 2 29).differenceLegacyDays?
        (constructed 1500 3 1) = some (.value 1 false) := by
  native_decide

/- Day shifting and difference retain the construction's distinct no-value reasons. -/
example :
    DateConstructionResult.incomplete.addLegacyDays? 1 = some .incomplete ∧
      DateConstructionResult.unreal.addLegacyDays? 1 = some .unreal ∧
      DateConstructionResult.incomplete.differenceLegacyDays?
        (constructed 1582 10 15) = some (.value 0 true) ∧
      DateConstructionResult.unreal.differenceLegacyDays?
        (constructed 1582 10 15) = some (.value 0 false) ∧
      DateConstructionResult.unknown.differenceLegacyDays?
        .incomplete = some .unavailable := by
  native_decide

/- Proleptic day arithmetic enters the missing label; constructed-Date arithmetic skips it. -/
example :
    (CivilDate.ofYmd? 1582 10 4).bind (fun date => date.addDays? 1) =
        CivilDate.ofYmd? 1582 10 5 ∧
      (constructed 1582 10 4).addLegacyDays? 1 =
        some (constructed 1582 10 15) := by
  native_decide

end A12Kernel.Conformance.ConstructedDateDay
