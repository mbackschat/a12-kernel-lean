import A12Kernel.Elaboration.ValueAsDate

/-! # Partial-Date `ValueAsDate` locks -/

namespace A12Kernel.Conformance.ValueAsDate

open A12Kernel

private def date? (year : Int) (month day : Nat) : Option FullDate :=
  FullDate.ofYmd? year month day

private def civil? (year : Int) (month day : Nat) : Option CivilDate :=
  CivilDate.ofYmd? year month day

private def time? (hour minute second : Nat) : Option TimeOfDay :=
  TimeOfDay.ofHms? hour minute second

private def dateDifferenceOperand?
    (year : Int) (month day : Nat) : Option DateDifferenceOperand :=
  (date? year month day).map
    (fun date => DateDifferenceOperand.value date.civil.parts)

private def dayOptionalSource
    (partialMode : TemporalPartialMode := .dayOptional)
    (format : String := "dd.MM.yyyy")
    (youngerThan1900Check : Bool := false) : FlatFieldDecl := {
  id := 0
  groupPath := ["Order"]
  name := "ApproxDate"
  policy := {
    kind := .temporal .date TemporalComponents.fullDate }
  temporalTargetPolicy := some {
    format
    partialMode
    youngerThan1900Check } }

private def modelWith
    (source : FlatFieldDecl := dayOptionalSource) : FlatModel := {
  fields := [source]
  timeZoneId := "Europe/Berlin" }

private def checked? (endpoint : ValueAsDateEndpoint)
    (comparison : TemporalComparisonOp) (expected : FullDate) :
    Option (CheckedValueAsDateComparison (modelWith)) :=
  (elaborateValueAsDateComparison
    (modelWith) 0 endpoint comparison expected).toOption

/- The literal omitted-day state is resolved only after the endpoint is selected. -/
example :
    let omitted :=
      AdmittedPartiallyKnownDate.ofOmittedDay? .dayOptional 2024 6
    omitted.map (·.resolve .firstDay) =
        (date? 2024 6 1).map .date ∧
      omitted.map (·.resolve .lastDay) =
        (date? 2024 6 30).map .date := by
  native_decide

/- Month-end completion is leap-aware, while a full value ignores the endpoint. -/
example :
    (AdmittedPartiallyKnownDate.ofOmittedDay?
        .dayOptional 2024 2).map (·.resolve .lastDay) =
        (date? 2024 2 29).map .date ∧
      (date? 2024 6 15).map (fun date =>
        ((AdmittedPartiallyKnownDate.ofFull? .dayOptional date).map
            (·.resolve .firstDay),
          (AdmittedPartiallyKnownDate.ofFull? .dayOptional date).map
            (·.resolve .lastDay))) =
        (date? 2024 6 15).map (fun date =>
          (some (.date date), some (.date date))) := by
  native_decide

/- Formal admission completes the omitted day before applying the universal Date floor. -/
example :
    AdmittedPartiallyKnownDate.ofOmittedDay?
        .dayOptional 1583 10 = none ∧
      (AdmittedPartiallyKnownDate.ofOmittedDay?
        .dayOptional 1583 11).isSome := by
  native_decide

/- First/last selection reaches the existing Date comparison and produces different verdicts. -/
example :
    let expected := (date? 2024 6 15).get (by native_decide)
    let first := (checked? .firstDay .before expected).get (by native_decide)
    let last := (checked? .lastDay .before expected).get (by native_decide)
    let firstSource := (AdmittedPartiallyKnownDate.ofOmittedDay?
      first.source.policy.partialMode 2024 6).get (by native_decide)
    let lastSource := (AdmittedPartiallyKnownDate.ofOmittedDay?
      last.source.policy.partialMode 2024 6).get (by native_decide)
    let firstCell : CheckedCell
        (AdmittedPartiallyKnownDate first.source.policy.partialMode) := {
      rawPresent := true
      parsed := some firstSource
      findings := [] }
    let lastCell : CheckedCell
        (AdmittedPartiallyKnownDate last.source.policy.partialMode) := {
      rawPresent := true
      parsed := some lastSource
      findings := [] }
    first.evaluate firstCell = .fired .value ∧
      last.evaluate lastCell = .notFired := by
  native_decide

/- Empty and formally unavailable sources retain the established direct-Date verdicts. -/
example :
    let expected := (date? 2024 6 15).get (by native_decide)
    let first := (checked? .firstDay .equal expected).get (by native_decide)
    let last := (checked? .lastDay .equal expected).get (by native_decide)
    let firstEmpty : CheckedCell
        (AdmittedPartiallyKnownDate first.source.policy.partialMode) := {
      rawPresent := false
      parsed := none
      findings := [] }
    let lastEmpty : CheckedCell
        (AdmittedPartiallyKnownDate last.source.policy.partialMode) := {
      rawPresent := false
      parsed := none
      findings := [] }
    first.evaluate firstEmpty = .notFired ∧
      last.evaluate (lastEmpty.withFinding .malformed) = .unknown := by
  native_decide

/- This checked consumer admits every partial Date precision and fails closed on the neighboring kind, placement, full-mode, and format axes. -/
example :
    let expected := (date? 2024 6 15).get (by native_decide)
    let dateTime := {
      dayOptionalSource .full "dd.MM.yyyy'T'HH:mm:ss" with
      policy := { kind := .temporal .dateTime TemporalComponents.now } }
    let repeated := {
      dayOptionalSource with
      groupPath := ["Order", "Rows"]
      repeatableScope := [10] }
    let repeatedModel : FlatModel := {
      fields := [repeated]
      repeatableGroups := [{ level := 10, path := ["Order", "Rows"] }] }
    (elaborateValueAsDateComparison
        (modelWith) 0 .firstDay .equal expected).isOk = true ∧
      (elaborateValueAsDateComparison
        (modelWith dateTime) 0 .firstDay .equal expected).isOk = false ∧
      (elaborateValueAsDateComparison
        repeatedModel 0 .firstDay .equal expected).isOk = false ∧
      (elaborateValueAsDateComparison
        (modelWith (dayOptionalSource .full))
        0 .firstDay .equal expected).isOk = false ∧
      (elaborateValueAsDateComparison
        (modelWith (dayOptionalSource .monthOptional))
        0 .firstDay .equal expected).isOk = true ∧
      (elaborateValueAsDateComparison
        (modelWith (dayOptionalSource .yearOptional))
        0 .firstDay .equal expected).isOk = true ∧
      (elaborateValueAsDateComparison
        (modelWith (dayOptionalSource .dayOptional "yyyy/M/d"))
        0 .firstDay .equal expected).isOk = false := by
  native_decide

/- Month omission selects the complete year boundary, not the omitted-day boundary. -/
example :
    let omitted := AdmittedPartiallyKnownDate.ofOmittedMonth? .monthOptional 2024
    omitted.map (·.resolve .firstDay) =
        (date? 2024 1 1).map .date ∧
      omitted.map (·.resolve .lastDay) =
        (date? 2024 12 31).map .date := by
  native_decide

/- An unknown year is a distinct admitted value that resolves to non-relevant, never a fabricated year. -/
example :
    (AdmittedPartiallyKnownDate.unknownYear? .yearOptional).map
      (·.resolve .firstDay) = some .nonRelevant ∧
    AdmittedPartiallyKnownDate.unknownYear? .monthOptional = none := by
  native_decide

/- Declaration precision admits exactly the monotone suffix of omission shapes. -/
example :
    (AdmittedPartiallyKnownDate.ofOmittedDay?
      .monthOptional 2024 2).isSome ∧
    (AdmittedPartiallyKnownDate.ofOmittedDay?
      .yearOptional 2024 2).isSome ∧
    AdmittedPartiallyKnownDate.ofOmittedMonth?
      .dayOptional 2024 = none ∧
    (AdmittedPartiallyKnownDate.ofOmittedMonth?
      .yearOptional 2024).isSome ∧
    AdmittedPartiallyKnownDate.unknownYear? .dayOptional = none := by
  native_decide

/- Runtime unknown-year suppression is non-relevance, not ordinary emptiness. -/
example :
    let expected := (date? 2024 6 15).get (by native_decide)
    let checked := (elaborateValueAsDateComparison
      (modelWith (dayOptionalSource .yearOptional))
      0 .lastDay .equal expected).toOption.get (by native_decide)
    let source := (AdmittedPartiallyKnownDate.unknownYear?
      checked.source.policy.partialMode).get (by native_decide)
    let cell : CheckedCell
        (AdmittedPartiallyKnownDate checked.source.policy.partialMode) := {
      rawPresent := true
      parsed := some source
      findings := [] }
    checked.evaluate cell = .unknown := by
  native_decide

/- Exact stored text enters the same declaration-indexed value and endpoint evaluator. -/
example :
    let expected := (date? 2024 6 15).get (by native_decide)
    let checked := (elaborateValueAsDateComparison
      (modelWith (dayOptionalSource .monthOptional))
      0 .firstDay .before expected).toOption.get (by native_decide)
    checked.evaluateRaw (.parsed "00.00.2024") = .fired .value := by
  native_decide

/- Both exact component orders reach the same typed month interval. -/
example :
    let expected := (date? 2024 6 15).get (by native_decide)
    let german := (elaborateValueAsDateComparison
      (modelWith (dayOptionalSource .monthOptional))
      0 .lastDay .after expected).toOption.get (by native_decide)
    let iso := (elaborateValueAsDateComparison
      (modelWith (dayOptionalSource .monthOptional "yyyy-MM-dd"))
      0 .lastDay .after expected).toOption.get (by native_decide)
    german.evaluateRaw (.parsed "00.00.2024") = .fired .value ∧
      iso.evaluateRaw (.parsed "2024-00-00") = .fired .value := by
  native_decide

/- The exact floor and optional pre-1900 policy run after earliest completion; unknown year bypasses only the latter and remains non-relevant. -/
example :
    let floor := (date? 1583 11 1).get (by native_decide)
    let floorChecked := (elaborateValueAsDateComparison
      (modelWith) 0 .firstDay .equal floor).toOption.get (by native_decide)
    let modern := (date? 1900 1 1).get (by native_decide)
    let additional := (elaborateValueAsDateComparison
      (modelWith (dayOptionalSource .yearOptional
        "dd.MM.yyyy" true))
      0 .firstDay .before modern).toOption.get (by native_decide)
    floorChecked.evaluateRaw (.parsed "00.10.1583") = .unknown ∧
      floorChecked.evaluateRaw (.parsed "00.11.1583") = .fired .value ∧
      additional.evaluateRaw (.parsed "00.12.1899") = .unknown ∧
      additional.evaluateRaw (.parsed "00.00.0000") = .unknown := by
  native_decide

/- Width, separators, suffix legality, and calendar reality all fail before operation evaluation. -/
example :
    let expected := (date? 2024 1 1).get (by native_decide)
    let day := (elaborateValueAsDateComparison
      (modelWith) 0 .firstDay .equal expected).toOption.get (by native_decide)
    let month := (elaborateValueAsDateComparison
      (modelWith (dayOptionalSource .monthOptional))
      0 .firstDay .equal expected).toOption.get (by native_decide)
    let year := (elaborateValueAsDateComparison
      (modelWith (dayOptionalSource .yearOptional))
      0 .firstDay .equal expected).toOption.get (by native_decide)
    day.evaluateRaw (.parsed "0.01.2024") = .unknown ∧
      day.evaluateRaw (.parsed "00-01-2024") = .unknown ∧
      day.evaluateRaw (.parsed "00.00.2024") = .unknown ∧
      month.evaluateRaw (.parsed "15.00.2024") = .unknown ∧
      year.evaluateRaw (.parsed "00.06.0000") = .unknown ∧
      year.evaluateRaw (.parsed "31.02.2024") = .unknown := by
  native_decide

/- Physical absence and present-empty placement stay distinct checked cells but share the operation's non-evaluated result. -/
example :
    let expected := (date? 2024 1 1).get (by native_decide)
    let checked := (elaborateValueAsDateComparison
      (modelWith) 0 .firstDay .equal expected).toOption.get (by native_decide)
    checked.evaluateRaw .empty = .notFired ∧
      checked.evaluateRaw .presentEmpty = .notFired := by
  native_decide

/- Endpoint completion precedes fractional truncation and the existing month landing rule. -/
example :
    let first := (elaborateValueAsDateShift
      (modelWith) 0 .firstDay .months).toOption.get (by native_decide)
    let last := (elaborateValueAsDateShift
      (modelWith) 0 .lastDay .months).toOption.get (by native_decide)
    (first.evaluateRaw (.parsed "00.02.2024") (.value (19 / 10))).toOption =
        some (.value ((civil? 2024 3 1).get (by native_decide))) ∧
      (last.evaluateRaw (.parsed "00.02.2024") (.value (19 / 10))).toOption =
        some (.value ((civil? 2024 3 29).get (by native_decide))) := by
  native_decide

/- Numeric amounts use Java's truncate-toward-zero and low signed-32-bit conversion rather than rounding, saturation, or rejection. -/
example :
    ValueAsDateShiftUnit.amountToInt32 (19 / 10) = 1 ∧
      ValueAsDateShiftUnit.amountToInt32 (-19 / 10) = -1 ∧
      ValueAsDateShiftUnit.amountToInt32 2147483648 = -2147483648 ∧
      ValueAsDateShiftUnit.amountToInt32 (-2147483649) = 2147483647 := by
  native_decide

/- The year operation preserves a selected non-leap February end into a leap year. -/
example :
    let shift := (elaborateValueAsDateShift
      (modelWith) 0 .lastDay .years).toOption.get (by native_decide)
    (shift.evaluateRaw (.parsed "00.02.2023") (.value 1)).toOption =
      some (.value ((civil? 2024 2 29).get (by native_decide))) := by
  native_decide

/- The expression retains a real below-floor landing so the later target check can reject the attempted Date rather than clear it as no-value. -/
example :
    let shift := (elaborateValueAsDateShift
      (modelWith) 0 .firstDay .days).toOption.get (by native_decide)
    (shift.evaluateRaw (.parsed "16.10.1583") (.value (-1))).toOption =
      some (.value ((civil? 1583 10 15).get (by native_decide))) := by
  native_decide

/- Non-relevance and reached poison dominate no-value, while a numeric domain failure remains clean no-value. -/
example :
    let shift := (elaborateValueAsDateShift
      (modelWith (dayOptionalSource .yearOptional))
      0 .firstDay .days).toOption.get (by native_decide)
    (shift.evaluateRaw (.parsed "00.00.0000") (.value 1)).toOption =
        some .nonRelevant ∧
      (shift.evaluateRaw .empty .domainFailure).toOption =
        some .noValue ∧
      (shift.evaluateRaw .empty (.poison .computedDependency)).toOption =
        some (.poison .computedDependency) ∧
      (shift.evaluateRaw (.rejected .malformed) (.value 1)).toOption =
        some (.poison .malformed) := by
  native_decide

/- Endpoint completion precedes the established whole-month boundary. -/
example :
    let other := (dateDifferenceOperand? 2024 3 28).get (by native_decide)
    let first := (elaborateValueAsDateDifference
      (modelWith) 0 .firstDay .months .left).toOption.get (by native_decide)
    let last := (elaborateValueAsDateDifference
      (modelWith) 0 .lastDay .months .left).toOption.get (by native_decide)
    (first.evaluateRaw Phase.validation
        (.parsed "00.02.2024") other).toOption =
        some (.operand (.value 1 .fixed)) ∧
      (last.evaluateRaw Phase.validation
        (.parsed "00.02.2024") other).toOption =
        some (.operand (.value 0 .fixed)) := by
  native_decide

/- Authored operand placement changes the sign and the first reached formal cause. -/
example :
    let other := (dateDifferenceOperand? 2024 3 28).get (by native_decide)
    let left := (elaborateValueAsDateDifference
      (modelWith) 0 .firstDay .months .left).toOption.get (by native_decide)
    let right := (elaborateValueAsDateDifference
      (modelWith) 0 .firstDay .months .right).toOption.get (by native_decide)
    (left.evaluateRaw Phase.computation
        (.parsed "00.02.2024") other).toOption =
        some (.operand (.value 1 .fixed)) ∧
      (right.evaluateRaw Phase.computation
        (.parsed "00.02.2024") other).toOption =
        some (.operand (.value (-1) .fixed)) ∧
      (left.evaluateRaw Phase.computation
        (.rejected .malformed) (.unavailable .computedDependency)).toOption =
        some (.operand (.unknown .malformed)) ∧
      (right.evaluateRaw Phase.computation
        (.rejected .malformed) (.unavailable .computedDependency)).toOption =
        some (.operand (.unknown .computedDependency)) := by
  native_decide

/- Cause-free unknown-year non-relevance precedes empty substitution, while ordinary empty still masks an unsupported present calendar. -/
example :
    let checked := (elaborateValueAsDateDifference
      (modelWith (dayOptionalSource .yearOptional))
      0 .lastDay .years .left).toOption.get (by native_decide)
    (checked.evaluateRaw Phase.validation
        (.parsed "00.00.0000") .empty).toOption =
        some .nonRelevant ∧
      (checked.evaluateRaw Phase.validation
        .empty .unsupportedCalendar).toOption =
        some (.operand (.value 0 .both)) ∧
      ValueAsDateDifferenceResult.nonRelevant.evalFixedRight
        .equal 0 = .unknown ∧
      (ValueAsDateDifferenceResult.operand (.value 1 .fixed)).evalFixedRight
        .greater 0 = .fired .value := by
  native_decide

/- The selected partial-Date endpoint and a direct Time observation resolve through the checked model zone. -/
example :
    let clock := (time? 1 30 0).get (by native_decide)
    let checked := (elaborateValueAsDateTime
      (modelWith) 0 .lastDay).toOption.get (by native_decide)
    let expectedLocal := (LocalDateTime.ofYmdHms?
      2024 2 29 1 30 0).get (by native_decide)
    let expectedInstant := (checked.profile.resolveLocal?
      expectedLocal).get (by native_decide)
    let result := checked.evaluateRaw Phase.validation
      (.parsed "00.02.2024") (.value clock)
    result = .value expectedLocal expectedInstant ∧
      result.evalFixedRight .equal expectedInstant = .fired .value := by
  native_decide

/- Date is read before Time, but a reached Time failure still precedes helper-level non-relevance. -/
example :
    let checked := (elaborateValueAsDateTime
      (modelWith (dayOptionalSource .yearOptional))
      0 .firstDay).toOption.get (by native_decide)
    checked.evaluateRaw Phase.computation
        (.rejected .malformed) (.poison .computedDependency) =
        .unavailable .malformed ∧
      checked.evaluateRaw Phase.validation
        (.parsed "00.00.0000") (.unknown .computedDependency) =
        .unavailable .computedDependency ∧
      checked.evaluateRaw Phase.validation
        (.parsed "00.00.0000") .empty =
        .nonRelevant := by
  native_decide

/- Missing input and a present-but-unresolvable Berlin wall label remain different no-value reasons. -/
example :
    let gapClock := (time? 2 30 0).get (by native_decide)
    let checked := (elaborateValueAsDateTime
      (modelWith) 0 .firstDay).toOption.get (by native_decide)
    checked.evaluateRaw Phase.validation
        .empty (.value gapClock) = .noValue true ∧
      checked.evaluateRaw Phase.validation
        (.parsed "31.03.2024") (.value gapClock) = .noValue false ∧
      ValueAsDateTimeResult.nonRelevant.evalFixedRight
        .equal { epochMillis := 0 } = .unknown := by
  native_decide

end A12Kernel.Conformance.ValueAsDate
