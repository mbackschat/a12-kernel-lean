import A12Kernel.Semantics.DateConstructionNumeric

/-! # Constructed-Date numeric component executable locks

These cases start with an already-classified three-part `Date(...)` result. They lock only the resolved `DayFromDate`, `MonthFromDate`, `QuarterFromDate`, and `YearFromDate` numeric projection and its fixed-literal validation behavior. Calendar resolution, DateTime composition, date differences, authored lowering, and target application remain outside this boundary.
-/

namespace A12Kernel.Conformance.DateConstructionNumeric

open A12Kernel

private def realParts : DateParts :=
  { year := 2024, month := 6, day := 15 }

/- A real construction exposes each supplied component as a fixed Number. -/
example :
    (DateConstructionResult.real realParts).numericPart .day =
        .value 15 false ∧
      (DateConstructionResult.real realParts).numericPart .month =
        .value 6 false ∧
      (DateConstructionResult.real realParts).numericPart .quarter =
        .value 2 false ∧
      (DateConstructionResult.real realParts).numericPart .year =
        .value 2024 false := by
  native_decide

/- Every direct component of an incomplete construction is the same not-given zero. -/
example :
    DateConstructionResult.incomplete.numericPart .day =
        .value 0 true ∧
      DateConstructionResult.incomplete.numericPart .month =
        .value 0 true ∧
      DateConstructionResult.incomplete.numericPart .quarter =
        .value 0 true ∧
      DateConstructionResult.incomplete.numericPart .year =
        .value 0 true := by
  native_decide

/- An unreal construction also projects to zero, but as a present/fixed result. -/
example :
    DateConstructionResult.unreal.numericPart .day =
        .value 0 false ∧
      DateConstructionResult.unreal.numericPart .month =
        .value 0 false ∧
      DateConstructionResult.unreal.numericPart .quarter =
        .value 0 false ∧
      DateConstructionResult.unreal.numericPart .year =
        .value 0 false := by
  native_decide

/- Formal unavailability remains UNKNOWN rather than becoming numeric zero. -/
example :
    DateConstructionResult.unknown.numericPart .year =
        .unavailable ∧
      (DateConstructionResult.unknown.numericPart .year).evalFixedRight
        .equal 0 = .unknown := by
  native_decide

/- Equal amounts do not imply equal verdict polarity: incomplete zero is OMISSION, unreal zero is VALUE. -/
example :
    (DateConstructionResult.incomplete.numericPart .year).evalFixedRight
        .equal 0 = .fired .omission ∧
      (DateConstructionResult.unreal.numericPart .year).evalFixedRight
        .equal 0 = .fired .value := by
  native_decide

/- Symmetric not-given provenance does not make incomplete zero equal a different fixed literal. -/
example :
    (DateConstructionResult.incomplete.numericPart .day).evalFixedRight
        .equal 1 = .notFired := by
  native_decide

/- Date missingness is symmetric: both upward and downward breaking directions remain fillable. -/
example :
    (DateConstructionResult.incomplete.numericPart .day).evalFixedRight
        .less 1 = .fired .omission ∧
      (DateConstructionResult.incomplete.numericPart .day).evalFixedRight
        .greaterEqual 0 = .fired .omission ∧
      (DateConstructionResult.unreal.numericPart .day).evalFixedRight
        .less 1 = .fired .value ∧
      (DateConstructionResult.unreal.numericPart .day).evalFixedRight
        .greaterEqual 0 = .fired .value := by
  native_decide

end A12Kernel.Conformance.DateConstructionNumeric
