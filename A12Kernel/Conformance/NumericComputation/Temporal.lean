import A12Kernel.Conformance.NumericComputation.Support

/-! # Numeric-computation temporal locks -/

namespace A12Kernel.Conformance.NumericComputation.Temporal

open A12Kernel
open A12Kernel.Conformance.NumericComputation.Support

/- Checked computation shares the temporal component source seam and admits both direct operation-form wrappers. -/
example :
    checkedResultOf (surfaceDateFieldPart "DateTime" .day)
        (context (dateTime := checkedTemporal .dateTime dateTimeComponents
          (.parsed dateTimeValue))) = some (.value 25) ∧
      checkedResultOf (.abs (surfaceDateFieldPart "DateTime" .day))
        (context (dateTime := checkedTemporal .dateTime dateTimeComponents
          (.parsed dateTimeValue))) = some (.value 25) ∧
      checkedResultOf
        (.round .floor omittedRoundingPlaces
          (surfaceTimeFieldPart "DateTime" .second))
        (context (dateTime := checkedTemporal .dateTime dateTimeComponents
          (.parsed dateTimeValue))) = some (.value 7) ∧
      checkedResultOf (surfaceTimeFieldPart "DateTime" .second)
        (context (dateTime := checkedTemporal .dateTime dateTimeComponents
          (.parsed dateTimeValue))) = some (.value 7) ∧
      checkedResultOf (surfaceTimeFieldPart "Time" .hour) = some (.value 0) ∧
      checkedResultOf (.abs (surfaceTimeFieldPart "Time" .hour)) =
        some (.value 0) ∧
      checkedResultOf (.round .halfUp omittedRoundingPlaces
        (surfaceDateFieldPart "DateTime" .year))
        (context (dateTime := checkedTemporal .dateTime dateTimeComponents
          (.rejected .malformed))) = some (.poison .malformed) := by
  native_decide

/- Checked computation consumes the same mixed date-difference source: filled fields produce scale-0 values, empty is zero, and formal invalidity remains poison. -/
example :
    let mixedMonths := surfaceDateDifference .months
      (.baseYear .direct) (surfaceDateOperand "Date")
    let reverseMonths := surfaceDateDifference .months
      (surfaceDateOperand "Date") (.baseYear .direct)
    checkedResultOf mixedMonths (context
        (date := checkedTemporal .date TemporalComponents.fullDate
          (.parsed (dateValue 2020 2 29)))) = some (.value 1) ∧
      checkedResultOf (.abs reverseMonths) (context
        (date := checkedTemporal .date TemporalComponents.fullDate
          (.parsed (dateValue 2020 2 29)))) = some (.value 1) ∧
      checkedResultOf (.round .halfUp omittedRoundingPlaces mixedMonths) (context
        (date := checkedTemporal .date TemporalComponents.fullDate
          (.parsed (dateValue 2020 2 29)))) = some (.value 1) ∧
      checkedResultOf mixedMonths = some (.value 0) ∧
      checkedResultOf (.abs mixedMonths) = some (.value 0) ∧
      checkedResultOf (.abs mixedMonths)
        (context (date := checkedTemporal .date TemporalComponents.fullDate
          (.rejected .malformed))) = some (.poison .malformed) := by
  native_decide

/- Month/year differences reject DateTime statically and a legacy-hybrid field payload dynamically instead of applying the proleptic decoded-parts core. -/
example :
    checkedErrorOf (surfaceDateDifference .years
      (surfaceDateOperand "DateTime") (.baseYear .direct)) =
        some (.incompatibleTemporalSource ["Root", "DateTime"]) ∧
      checkedFaultOf
        (surfaceDateDifference .months
          (.baseYear .direct) (surfaceDateOperand "Date"))
        (context (date := checkedTemporal .date TemporalComponents.fullDate
          (.parsed (dateValue 2020 2 29 .legacyHybrid)))) =
          some .unsupportedDateCalendar := by
  native_decide

/- Checked calendar-day computation preserves exact overlap identity and concrete model-zone selection through the shared numeric tree. -/
example :
    let spring := surfaceDayDifference
      (surfaceDateOperand "DateTime") (surfaceDateOperand "LaterDateTime")
    let springInput := context
      (dateTime := checkedTemporal .dateTime dateTimeComponents
        (.parsed (berlinDateTimeValue 2024 3 30 2 30 0
          (by native_decide) (by native_decide))))
      (laterDateTime := checkedTemporal .dateTime dateTimeComponents
        (.parsed (berlinDateTimeValue 2024 3 31 1 45 0
          (by native_decide) (by native_decide))))
    checkedResultOfIn berlinModel spring springInput = some (.value 1) ∧
      checkedResultOf spring springInput = some (.value 0) ∧
      checkedResultOfIn berlinModel spring
        (context
          (dateTime := checkedTemporal .dateTime dateTimeComponents
            (.parsed (berlinDateTimeValue 2024 10 26 2 30 0
              (by native_decide) (by native_decide))))
          (laterDateTime := checkedTemporal .dateTime dateTimeComponents
            (.parsed berlinDaylightFoldValue))) = some (.value 0) ∧
      checkedResultOfIn berlinModel spring
        (context
          (dateTime := checkedTemporal .dateTime dateTimeComponents .empty)
          (laterDateTime := checkedTemporal .dateTime dateTimeComponents
            (.parsed (berlinDateTimeValue 2024 3 31 1 45 0
              (by native_decide) (by native_decide))))) = some (.value 0) ∧
      checkedResultOfIn berlinModel spring
        (context
          (dateTime := checkedTemporal .dateTime dateTimeComponents
            (.rejected .malformed))
          (laterDateTime := checkedTemporal .dateTime dateTimeComponents
            (.parsed (berlinDateTimeValue 2024 3 31 1 45 0
              (by native_decide) (by native_decide))))) =
        some (.poison .malformed) := by
  native_decide

/- Checked computation consumes the same exact-instant sub-day source, including authored-order truncation, symmetric empty zero, and computation poison. -/
example :
    let elapsed := surfaceDateTimeDifference .hours
      (surfaceDateOperand "DateTime") (surfaceDateOperand "LaterDateTime")
    let input := context
      (dateTime := checkedTemporal .dateTime dateTimeComponents
        (.parsed (dateTimeValueAt 19815000)))
      (laterDateTime := checkedTemporal .dateTime dateTimeComponents
        (.parsed (dateTimeValueAt 0)))
    checkedResultOf elapsed input = some (.value (-5)) ∧
      checkedResultOf
        (surfaceDateTimeDifference .minutes
          (surfaceDateOperand "LaterDateTime")
          (surfaceDateOperand "DateTime")) input = some (.value 330) ∧
      checkedResultOf elapsed = some (.value 0) ∧
      checkedResultOf elapsed
        (context
          (dateTime := checkedTemporal .dateTime dateTimeComponents
            (.rejected .malformed))) = some (.poison .malformed) ∧
      checkedErrorOf
        (surfaceDateTimeDifference .seconds
          (surfaceDateOperand "Date") (surfaceDateOperand "DateTime")) =
          some (.incompatibleTemporalSource ["Root", "Date"]) ∧
      checkedErrorOf
        (surfaceDateTimeDifference .seconds
          (.baseYear .direct) (surfaceDateOperand "DateTime")) =
          some .incompatibleDateDifference := by
  native_decide

/- Day admission accepts Date/DateTime mixing, rejects Time, and reports unsupported profile selection before runtime. -/
example :
    let mixed := surfaceDayDifference
      (.baseYear .direct) (surfaceDateOperand "DateTime")
    checkedErrorOfIn berlinModel mixed = none ∧
      checkedErrorOfIn model
        (surfaceDayDifference
          (surfaceDateOperand "Time") (surfaceDateOperand "DateTime")) =
          some (.incompatibleTemporalSource ["Root", "Time"]) ∧
      checkedErrorOfIn unsupportedZoneModel
        (surfaceDayDifference
          (surfaceDateOperand "DateTime")
          (surfaceDateOperand "LaterDateTime")) =
          some (.unsupportedCalendarProfile "Pacific/Apia") := by
  native_decide

/- Checked source admission rejects the wrong temporal family while admitting numeric `BaseYear` under the ordinary wrappers. -/
example :
    checkedErrorOf (surfaceDateFieldPart "Time" .day) =
        some (.incompatibleTemporalSource ["Root", "Time"]) ∧
      checkedResultOf (.round .halfUp omittedRoundingPlaces surfaceBaseYear) =
        some (.value 2020) := by
  native_decide

example : resultOf (divide (literal 6) (literal 3)) = some (.value 2) := by
  native_decide


end A12Kernel.Conformance.NumericComputation.Temporal
