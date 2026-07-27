import A12Kernel.Elaboration.ValueAsDate

/-! # Partial-Date `ValueAsDate` locks -/

namespace A12Kernel.Conformance.ValueAsDate

open A12Kernel

private def date? (year : Int) (month day : Nat) : Option FullDate :=
  FullDate.ofYmd? year month day

private def dayOptionalSource
    (partialMode : TemporalPartialMode := .dayOptional)
    (format : String := "dd.MM.yyyy") : FlatFieldDecl := {
  id := 0
  groupPath := ["Order"]
  name := "ApproxDate"
  policy := {
    kind := .temporal .date TemporalComponents.fullDate }
  temporalTargetPolicy := some { format, partialMode } }

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

/- Runtime unknown-year suppression reaches the ordinary non-evaluated comparison path. -/
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
    checked.evaluate cell = .notFired := by
  native_decide

end A12Kernel.Conformance.ValueAsDate
