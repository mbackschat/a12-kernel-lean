import A12Kernel.Semantics.TimeNumeric

/-! # Typed Time and DateTime numeric-component locks -/

namespace A12Kernel.Conformance.TimeNumeric

open A12Kernel

private def time (hour minute second : Nat)
    (valid : (TimeOfDay.ofHms? hour minute second).isSome) : TimeOfDay :=
  (TimeOfDay.ofHms? hour minute second).get valid

private def dateTime (year : Int) (month day hour minute second : Nat)
    (admitted : (LocalDateTime.ofYmdHms? year month day hour minute second).isSome) :
    LocalDateTime :=
  (LocalDateTime.ofYmdHms? year month day hour minute second).get admitted

private def clock : TimeOfDay := time 5 21 7 (by native_decide)

private def juneMorning : LocalDateTime :=
  dateTime 2024 6 25 5 21 7 (by native_decide)

private def decemberMorning : LocalDateTime :=
  dateTime 2025 12 31 5 21 7 (by native_decide)

/- A checked Time exposes all three fixed numeric clock components. -/
example :
    TimeNumericPart.hour.fromTimeObservation (.value clock) =
        .value 5 .fixed ∧
      TimeNumericPart.minute.fromTimeObservation (.value clock) =
        .value 21 .fixed ∧
      TimeNumericPart.second.fromTimeObservation (.value clock) =
        .value 7 .fixed := by
  native_decide

/- Time extraction over DateTime uses its clock and ignores the date. -/
example :
    TimeNumericPart.hour.fromDateTimeObservation (.value juneMorning) =
        .value 5 .fixed ∧
      TimeNumericPart.hour.fromDateTimeObservation (.value decemberMorning) =
        .value 5 .fixed ∧
      TimeNumericPart.second.fromDateTimeObservation (.value juneMorning) =
        .value 7 .fixed := by
  native_decide

/- Empty Time and DateTime sources both become symmetric fillable numeric zero. -/
example :
    TimeNumericPart.minute.fromTimeObservation .empty =
        .value 0 .both ∧
      TimeNumericPart.second.fromDateTimeObservation .empty =
        .value 0 .both := by
  native_decide

/- A true comparison over the empty-source zero is omission-typed in both directions. -/
example :
    NumericComparisonOp.less.evalFixedRight
        (TimeNumericPart.hour.fromTimeObservation .empty) 3 =
        .fired .omission ∧
      NumericComparisonOp.greaterEqual.evalFixedRight
        (TimeNumericPart.hour.fromDateTimeObservation .empty) 0 =
        .fired .omission := by
  native_decide

/- Formal unavailability preserves its exact cause. -/
example :
    TimeNumericPart.second.fromTimeObservation (.unknown .malformed) =
        .unknown .malformed ∧
      TimeNumericPart.second.fromDateTimeObservation
          (.unknown .declaredConstraint) =
        .unknown .declaredConstraint := by
  native_decide

end A12Kernel.Conformance.TimeNumeric
