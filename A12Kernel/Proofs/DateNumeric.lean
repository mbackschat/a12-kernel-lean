import A12Kernel.Semantics.DateNumeric

/-! # Typed Date and DateTime numeric-component laws -/

namespace A12Kernel

/-- Every empty source becomes the same symmetric fillable zero, whatever calendar-part view the
caller supplies. The typed full-Date, DateTime, and DateRange-endpoint reads are its instances. -/
@[simp] theorem dateNumericPart_fromObservation_empty
    (part : DateNumericPart) (partsOf : α → DateParts) :
    part.fromObservation partsOf .empty = .value 0 .both := rfl

/-- A present source exposes exactly the selected component of the supplied calendar parts, as
fixed rather than fillable. -/
@[simp] theorem dateNumericPart_fromObservation_value
    (part : DateNumericPart) (partsOf : α → DateParts) (value : α) :
    part.fromObservation partsOf (.value value) =
      .value (part.extract (partsOf value)) .fixed := rfl

/-- Validation unavailability retains its exact cause through every calendar-part view. -/
@[simp] theorem dateNumericPart_fromObservation_unknown
    (part : DateNumericPart) (partsOf : α → DateParts) (cause : FormalCause) :
    part.fromObservation partsOf (.unknown cause) = .unknown cause := rfl

/-- A poisoned source is read as validation-unavailable with the same cause, never as a zero. -/
@[simp] theorem dateNumericPart_fromObservation_poison
    (part : DateNumericPart) (partsOf : α → DateParts) (cause : FormalCause) :
    part.fromObservation partsOf (.poison cause) = .unknown cause := rfl

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

end A12Kernel
