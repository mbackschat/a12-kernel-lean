import A12Kernel.Semantics.DateConstructionNumeric

/-! # Constructed-Date numeric component laws

These laws characterize the cause-free numeric projection of an already-classified three-part `Date(...)` result and its fixed-literal validation consumer. They do not prove calendar resolution, component bounds, exact formal-cause transport, DateTime composition, date differences, authored lowering, or external kernel equivalence.
-/

namespace A12Kernel

/-- The closed selector exposes exactly the supplied direct components, including the month-derived quarter. -/
theorem dateNumericPart_extracts_components (parts : DateParts) :
    DateNumericPart.day.extract parts = parts.day ∧
      DateNumericPart.month.extract parts = parts.month ∧
      DateNumericPart.quarter.extract parts =
        (if parts.month = 0 then 0
          else (((parts.month - 1) / 3 + 1 : Nat) : Rat)) ∧
      DateNumericPart.year.extract parts = parts.year := by
  simp [DateNumericPart.extract]

/-- A calendar-resolved real construction projects the selected component with present provenance. -/
theorem dateConstruction_numericPart_real
    (parts : DateParts) (part : DateNumericPart) :
    (DateConstructionResult.real parts).numericPart part =
      .value (part.extract parts) false := by
  rfl

/-- Incomplete and unreal constructions have the same numeric amount but distinct not-given provenance. This is the nearest non-law against collapsing the projection to an amount alone. -/
theorem dateConstruction_numericPart_same_zero_distinct_provenance
    (part : DateNumericPart) :
    DateConstructionResult.incomplete.numericPart part =
        .value 0 true ∧
      DateConstructionResult.unreal.numericPart part =
        .value 0 false ∧
      DateConstructionResult.incomplete.numericPart part ≠
        DateConstructionResult.unreal.numericPart part := by
  simp [DateConstructionResult.numericPart]

/-- Cause-free formal unavailability remains UNKNOWN for every operator and fixed literal. -/
theorem dateConstruction_numericPart_unavailable_comparison
    (part : DateNumericPart) (op : NumericComparisonOp) (expected : Rat) :
    (DateConstructionResult.unknown.numericPart part).evalFixedRight
      op expected = .unknown := by
  rfl

/-- Incomplete Date missingness is symmetric rather than unsigned grow-only: every true fixed-literal comparison is OMISSION-typed, while the same true fixed-literal comparison over unreal fixed zero is VALUE-typed. -/
theorem dateConstruction_numericPart_true_comparison_polarity
    (part : DateNumericPart) (op : NumericComparisonOp) (expected : Rat)
    (holds : op.holds 0 expected = true) :
    (DateConstructionResult.incomplete.numericPart part).evalFixedRight
        op expected = .fired .omission ∧
      (DateConstructionResult.unreal.numericPart part).evalFixedRight
        op expected = .fired .value := by
  cases op <;>
    simp_all [DateConstructionResult.numericPart,
      ConstructedDateNumericResult.evalFixedRight,
      NumericComparisonOp.evalFixedRight, NumericComparisonOp.eval,
      NumericComparisonOp.fillCanBreak, numericDifferenceFillCanClose,
      NumericFillability.both, NumericFillability.fixed]

end A12Kernel
