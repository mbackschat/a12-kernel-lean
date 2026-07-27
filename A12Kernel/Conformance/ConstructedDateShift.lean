import A12Kernel.Semantics.ConstructedDateShift
import A12Kernel.Semantics.DateShift

/-! # Constructed-Date legacy-hybrid month/year shift locks -/

namespace A12Kernel.Conformance.ConstructedDateShift

open A12Kernel

private def parts (year : Int) (month day : Nat) : DateParts :=
  { year, month, day }

private def constructed (year : Int) (month day : Nat) : DateConstructionResult :=
  .real (parts year month day)

/- A nominal landing in the default cutover hole normalizes ten labels forward. -/
example :
    (constructed 1582 9 10).addLegacyMonths? 1 =
        some (constructed 1582 10 20) ∧
      (constructed 1581 10 10).addLegacyYears? 1 =
        some (constructed 1582 10 20) := by
  native_decide

/- Constructed-Date arithmetic retains Julian-side February reality. -/
example :
    (constructed 1500 2 29).addLegacyMonths? 1 =
        some (constructed 1500 3 29) ∧
      (constructed 1500 2 29).addLegacyYears? 1 =
        some (constructed 1501 2 28) := by
  native_decide

/- The explicit February-28 correction tests Gregorian leap status even on the Julian side. -/
example :
    (constructed 1499 2 28).addLegacyYears? 1 =
      some (constructed 1500 2 28) := by
  native_decide

/- Calendar shifting preserves each reason-bearing constructed no-value. -/
example :
    DateConstructionResult.incomplete.addLegacyMonths? 1 = some .incomplete ∧
      DateConstructionResult.unreal.addLegacyMonths? 1 = some .unreal ∧
      DateConstructionResult.unknown.addLegacyYears? 1 = some .unknown := by
  native_decide

/- A proleptic Gregorian month shift chooses the missing label, so it cannot implement constructed-Date cutover arithmetic. -/
example :
    (CivilDate.ofYmd? 1582 9 10).bind (fun date => date.addMonths? 1) =
        CivilDate.ofYmd? 1582 10 10 ∧
      (constructed 1582 9 10).addLegacyMonths? 1 =
        some (constructed 1582 10 20) := by
  native_decide

end A12Kernel.Conformance.ConstructedDateShift
