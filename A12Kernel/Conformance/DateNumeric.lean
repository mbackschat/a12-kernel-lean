import A12Kernel.Semantics.DateNumeric

/-! # Typed Date and DateTime numeric-component locks -/

namespace A12Kernel.Conformance.DateNumeric

open A12Kernel

private def fullDate (year : Int) (month day : Nat)
    (admitted : (FullDate.ofYmd? year month day).isSome) : FullDate :=
  (FullDate.ofYmd? year month day).get admitted

private def dateTime (year : Int) (month day hour minute second : Nat)
    (admitted : (LocalDateTime.ofYmdHms? year month day hour minute second).isSome) :
    LocalDateTime :=
  (LocalDateTime.ofYmdHms? year month day hour minute second).get admitted

private def juneDate : FullDate := fullDate 2024 6 25 (by native_decide)

private def morning : LocalDateTime :=
  dateTime 2024 6 25 5 21 7 (by native_decide)

private def evening : LocalDateTime :=
  dateTime 2024 6 25 23 59 59 (by native_decide)

/- A checked full Date exposes all four fixed numeric components. -/
example :
    DateNumericPart.day.fromFullDateObservation (.value juneDate) =
        .value 25 .fixed ∧
      DateNumericPart.month.fromFullDateObservation (.value juneDate) =
        .value 6 .fixed ∧
      DateNumericPart.quarter.fromFullDateObservation (.value juneDate) =
        .value 2 .fixed ∧
      DateNumericPart.year.fromFullDateObservation (.value juneDate) =
        .value 2024 .fixed := by
  native_decide

/- Date extractors over DateTime use its Date part and ignore the clock. -/
example :
    DateNumericPart.day.fromDateTimeObservation (.value morning) =
        .value 25 .fixed ∧
      DateNumericPart.day.fromDateTimeObservation (.value evening) =
        .value 25 .fixed ∧
      DateNumericPart.quarter.fromDateTimeObservation (.value morning) =
        .value 2 .fixed := by
  native_decide

/- Empty Date and DateTime sources both become symmetric fillable numeric zero. -/
example :
    DateNumericPart.year.fromFullDateObservation .empty =
        .value 0 .both ∧
      DateNumericPart.day.fromDateTimeObservation .empty =
        .value 0 .both := by
  native_decide

/- A true comparison over the empty-source zero is omission-typed in both directions. -/
example :
    NumericComparisonOp.less.evalFixedRight
        (DateNumericPart.month.fromFullDateObservation .empty) 3 =
        .fired .omission ∧
      NumericComparisonOp.greaterEqual.evalFixedRight
        (DateNumericPart.month.fromDateTimeObservation .empty) 0 =
        .fired .omission := by
  native_decide

/- Formal unavailability preserves its exact cause until verdict projection. -/
example :
    DateNumericPart.year.fromFullDateObservation (.unknown .malformed) =
        .unknown .malformed ∧
      DateNumericPart.year.fromDateTimeObservation
          (.unknown .declaredConstraint) =
        .unknown .declaredConstraint := by
  native_decide

/- Already-admitted typed parser results reach the same DateTime projection without a second cell representation. -/
example :
    DateNumericPart.year.fromDateTimeObservation
        (observeAdmittedRawCell .validation (.parsed morning)) =
        .value 2024 .fixed ∧
      DateNumericPart.year.fromDateTimeObservation
        (observeAdmittedRawCell .validation
          (.empty : RawCell LocalDateTime)) =
        .value 0 .both := by
  native_decide

end A12Kernel.Conformance.DateNumeric
