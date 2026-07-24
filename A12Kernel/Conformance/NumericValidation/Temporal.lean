import A12Kernel.Conformance.NumericValidation.Support

/-! # Checked numeric-validation temporal locks -/

namespace A12Kernel.Conformance.NumericValidation.Temporal

open A12Kernel
open A12Kernel.Conformance.NumericValidation.Support

/- Direct temporal component functions enter the same checked scale-0 numeric tree. DateTime supplies either half, while empty remains the symmetric numeric zero. -/
example :
    verdictOf (comparison .equal (dateFieldPart "DateTime" .day) 25)
        (temporalRaw 9 (.parsed dateTimeValue)) = some (.fired .value) ∧
      verdictOf (comparison .equal (dateFieldPart "DateTime" .quarter) 2)
        (temporalRaw 9 (.parsed dateTimeValue)) = some (.fired .value) ∧
      verdictOf (comparison .equal (timeFieldPart "DateTime" .minute) 21)
        (temporalRaw 9 (.parsed dateTimeValue)) = some (.fired .value) ∧
      verdictOf (comparison .less (timeFieldPart "Time" .hour) 3)
        (temporalRaw 8 .empty) = some (.fired .omission) := by
  native_decide

/- Component presence, family compatibility, and the Base-Year year supplement are checked before runtime reads. -/
example :
    errorOf (comparison .equal (dateFieldPart "Time" .day) 1) =
        some (.incompatibleTemporalSource ["Order", "Time"]) ∧
      errorOf (comparison .equal (timeFieldPart "NoYear" .hour) 1) =
        some (.incompatibleTemporalSource ["Order", "NoYear"]) ∧
      errorOf (comparison .equal (dateFieldPart "NoYear" .year) 2024) =
        some (.incompatibleTemporalSource ["Order", "NoYear"]) ∧
      errorOf (comparison .equal (dateFieldPart "NoYear" .year) 2024)
        baseYearModel = none := by
  native_decide

/- Direct temporal components admit both numeric operation-form wrappers. Rounding preserves symmetric missingness, while `Abs` makes missing zero unable to shrink. -/
example :
    verdictOf (comparison .equal (.abs (dateFieldPart "DateTime" .day)) 25)
        (temporalRaw 9 (.parsed dateTimeValue)) = some (.fired .value) ∧
      verdictOf (comparison .greaterEqual
        (.round .halfUp omittedRoundingPlaces
          (dateFieldPart "DateTime" .day)) 0)
        (temporalRaw 9 .empty) = some (.fired .omission) ∧
      verdictOf (comparison .greaterEqual
        (.abs (dateFieldPart "DateTime" .day)) 0)
        (temporalRaw 9 .empty) = some (.fired .value) ∧
      verdictOf (comparison .less
        (.round .floor omittedRoundingPlaces
          (dateFieldPart "DateTime" .day)) 1)
        (temporalRaw 9 (.rejected .malformed)) = some .unknown ∧
      (elaborateNumericComparison model ["Order"]
        (twoSided .equal
          (.round .halfUp ⟨2, by decide⟩
            (dateFieldPart "DateTime" .day))
          (atom "Scale2"))).isOk = true ∧
      verdictOf (comparison .equal
        (.binary .add (dateFieldPart "DateTime" .day) (atom "U")) 26)
        (let context := temporalRaw 9 (.parsed dateTimeValue)
         { read := fun id => if id == 0 then .parsed (.num 1) else context.read id }) =
        some (.fired .value) := by
  native_decide

/- Field/Base-Year differences reuse the decoded Date payload and admit both scale-0 wrappers. DateTime and legacy-hybrid payloads stay fail-closed. -/
example :
    let mixed := dateDifference .months (.baseYear .direct) (dateOperand "NoYear")
    let reverse := dateDifference .months (dateOperand "NoYear") (.baseYear .direct)
    errorOf (comparison .equal mixed 1) = some .baseYearNotDeclared ∧
      verdictOf (comparison .equal mixed 1)
        (temporalRaw 11 (.parsed (dateValue 2020 2 29))) true baseYearModel =
          some (.fired .value) ∧
      verdictOf (comparison .equal (.abs reverse) 1)
        (temporalRaw 11 (.parsed (dateValue 2020 2 29))) true baseYearModel =
          some (.fired .value) ∧
      verdictOf (comparison .less mixed 3)
        (temporalRaw 11 .empty) true baseYearModel = some (.fired .omission) ∧
      verdictOf (comparison .greaterEqual
        (.round .halfUp omittedRoundingPlaces mixed) 0)
        (temporalRaw 11 .empty) true baseYearModel = some (.fired .omission) ∧
      verdictOf (comparison .greaterEqual (.abs mixed) 0)
        (temporalRaw 11 .empty) true baseYearModel = some (.fired .value) ∧
      verdictOf (comparison .less mixed 3)
        (temporalRaw 11 (.rejected .malformed)) true baseYearModel = some .unknown ∧
      verdictOf (comparison .less (.abs mixed) 3)
        (temporalRaw 11 (.rejected .malformed)) true baseYearModel = some .unknown ∧
      errorOf (comparison .equal
        (dateDifference .years (dateOperand "DateTime") (.baseYear .direct)) 0)
        baseYearModel = some (.incompatibleTemporalSource ["Order", "DateTime"]) ∧
      verdictOf (comparison .equal mixed 1)
        (temporalRaw 11 (.parsed (dateValue 2020 2 29 .legacyHybrid))) true
        baseYearModel = some .unknown := by
  native_decide

/- Checked calendar-day differences retain exact instants and model-zone selection instead of reusing Date-only periods or elapsed-time division. -/
example :
    let spring := dayDifference
      (dateOperand "DateTime") (dateOperand "LaterDateTime")
    let springInput := temporalPairRaw
      (.parsed (berlinDateTimeValue 2024 3 30 2 30 0
        (by native_decide) (by native_decide)))
      (.parsed (berlinDateTimeValue 2024 3 31 1 45 0
        (by native_decide) (by native_decide)))
    verdictOf (comparison .equal spring 1) springInput true berlinModel =
        some (.fired .value) ∧
      verdictOf (comparison .equal spring 0) springInput =
        some (.fired .value) ∧
      verdictOf (comparison .equal spring 0)
        (temporalPairRaw
          (.parsed (berlinDateTimeValue 2024 10 26 2 30 0
            (by native_decide) (by native_decide)))
          (.parsed berlinDaylightFoldValue))
        true berlinModel = some (.fired .value) ∧
      verdictOf (comparison .less spring 2)
        (temporalPairRaw .empty
          (.parsed (berlinDateTimeValue 2024 3 31 1 45 0
            (by native_decide) (by native_decide))))
        true berlinModel = some (.fired .omission) ∧
      verdictOf (comparison .equal spring 0)
        (temporalPairRaw (.rejected .malformed)
          (.parsed (berlinDateTimeValue 2024 3 31 1 45 0
            (by native_decide) (by native_decide))))
        true berlinModel = some .unknown := by
  native_decide

/- Checked sub-day differences admit only two DateTime fields, preserve authored order, and reuse the exact-millisecond operand boundary. -/
example :
    let elapsed := dateTimeDifference .hours
      (dateOperand "DateTime") (dateOperand "LaterDateTime")
    let reverse := dateTimeDifference .hours
      (dateOperand "LaterDateTime") (dateOperand "DateTime")
    let input := temporalPairRaw
      (.parsed (dateTimeValueAt 19815000))
      (.parsed (dateTimeValueAt 0))
    verdictOf (comparison .equal elapsed (-5)) input =
        some (.fired .value) ∧
      verdictOf (comparison .equal reverse 5) input =
        some (.fired .value) ∧
      verdictOf (comparison .less elapsed 1)
        (temporalPairRaw .empty (.parsed (dateTimeValueAt 0))) =
          some (.fired .omission) ∧
      verdictOf (comparison .equal elapsed 0)
        (temporalPairRaw (.rejected .malformed)
          (.parsed (dateTimeValueAt 0))) = some .unknown ∧
      errorOf (comparison .equal
        (dateTimeDifference .hours
          (dateOperand "NoYear") (dateOperand "DateTime")) 0) =
          some (.incompatibleTemporalSource ["Order", "NoYear"]) ∧
      errorOf (comparison .equal
        (dateTimeDifference .seconds
          (.baseYear .direct) (dateOperand "DateTime")) 0) =
          some .incompatibleDateDifference := by
  native_decide

/- Day admission permits mixed Date/DateTime and rejects Time or an unavailable concrete profile before evaluation. -/
example :
    let mixed := dayDifference (.baseYear .direct) (dateOperand "DateTime")
    errorOf (comparison .equal mixed 0) baseYearModel = none ∧
      errorOf (comparison .equal
        (dayDifference (dateOperand "Time") (dateOperand "DateTime")) 0) =
          some (.incompatibleTemporalSource ["Order", "Time"]) ∧
      errorOf (comparison .equal
        (dayDifference (dateOperand "DateTime")
          (dateOperand "LaterDateTime")) 0) unsupportedZoneModel =
          some (.unsupportedCalendarProfile "Pacific/Apia") := by
  native_decide

example : errorOf
    (comparison .equal (.atom (.field (path ["Order", "Items"] "Item"))) 0) =
      some (.resolve (.repeatableReference ["Order", "Items", "Item"])) := by
  native_decide

example : errorOf
    (comparison .equal (.atom (.field (path ["Reference"] "Other"))) 0) =
      some (.fieldOutsideRowGroup ["Reference", "Other"] ["Order"]) := by
  native_decide


end A12Kernel.Conformance.NumericValidation.Temporal
