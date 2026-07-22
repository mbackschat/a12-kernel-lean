import A12Kernel.Semantics.DateNumeric

/-! # Typed Date and DateTime numeric-component laws -/

namespace A12Kernel

/-- Every empty typed Date source becomes the same symmetric fillable zero, independently of the selected component. -/
theorem dateNumericPart_fullDate_empty (part : DateNumericPart) :
    part.fromFullDateObservation .empty = .value 0 .both := by
  rfl

/-- A present full Date exposes exactly the selected decoded calendar component. -/
theorem dateNumericPart_fullDate_value
    (part : DateNumericPart) (date : FullDate) :
    part.fromFullDateObservation (.value date) =
      .value (part.extract date.civil.parts) .fixed := by
  rfl

/-- Date extraction over DateTime is extensionally the same projection as extraction over its Date component; the clock is irrelevant. -/
theorem dateNumericPart_dateTime_uses_date
    (part : DateNumericPart) (dateTime : LocalDateTime) :
    part.fromDateTimeObservation (.value dateTime) =
      part.fromFullDateObservation (.value dateTime.date) := by
  rfl

/-- Formal unavailability retains its exact cause through both typed source families. -/
theorem dateNumericPart_unavailable
    (part : DateNumericPart) (cause : FormalCause) :
    part.fromFullDateObservation (.unknown cause) = .unknown cause ∧
      part.fromDateTimeObservation (.unknown cause) = .unknown cause := by
  constructor <;> rfl

/-- Whenever the substituted empty-source zero satisfies a comparison, symmetric date fillability makes the verdict omission-typed for both Date and DateTime. -/
theorem dateNumericPart_empty_true_comparison_omission
    (part : DateNumericPart) (op : NumericComparisonOp) (expected : Rat)
    (holds : op.holds 0 expected = true) :
    op.evalFixedRight (part.fromFullDateObservation .empty) expected =
        .fired .omission ∧
      op.evalFixedRight (part.fromDateTimeObservation .empty) expected =
        .fired .omission := by
  cases op <;>
    simp_all [DateNumericPart.fromFullDateObservation,
      DateNumericPart.fromDateTimeObservation,
      DateNumericPart.fromObservation,
      NumericComparisonOp.evalFixedRight, NumericComparisonOp.eval,
      NumericComparisonOp.fillCanBreak, numericDifferenceFillCanClose,
      NumericFillability.both]

end A12Kernel
