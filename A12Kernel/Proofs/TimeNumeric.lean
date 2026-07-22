import A12Kernel.Proofs.NumericComparison
import A12Kernel.Semantics.TimeNumeric

/-! # Typed Time and DateTime numeric-component laws -/

namespace A12Kernel

/-- The closed selector exposes exactly the three decoded clock components. -/
theorem timeNumericPart_extracts_components (time : TimeOfDay) :
    TimeNumericPart.hour.extract time = time.hour ∧
      TimeNumericPart.minute.extract time = time.minute ∧
      TimeNumericPart.second.extract time = time.second := by
  simp [TimeNumericPart.extract]

/-- A present Time exposes exactly the selected decoded clock component. -/
theorem timeNumericPart_time_value
    (part : TimeNumericPart) (time : TimeOfDay) :
    part.fromTimeObservation (.value time) =
      .value (part.extract time) .fixed := by
  rfl

/-- Time extraction over DateTime is extensionally the same projection as extraction over its Time component; the date is irrelevant. -/
theorem timeNumericPart_dateTime_uses_time
    (part : TimeNumericPart) (dateTime : LocalDateTime) :
    part.fromDateTimeObservation (.value dateTime) =
      part.fromTimeObservation (.value dateTime.time) := by
  rfl

/-- Formal unavailability retains its exact cause through both typed source families. -/
theorem timeNumericPart_unavailable
    (part : TimeNumericPart) (cause : FormalCause) :
    part.fromTimeObservation (.unknown cause) = .unknown cause ∧
      part.fromDateTimeObservation (.unknown cause) = .unknown cause := by
  constructor <;> rfl

end A12Kernel
