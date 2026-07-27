import A12Kernel.Elaboration.ValueAsDate

/-! # Day-optional `ValueAsDate` locks -/

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

private def evaluate? (endpoint : ValueAsDateEndpoint)
    (comparison : TemporalComparisonOp) (expected : FullDate)
    (cell : CheckedCell DayOptionalDate) : Option Verdict :=
  (checked? endpoint comparison expected).map (·.evaluate cell)

/- The literal omitted-day state is resolved only after the endpoint is selected. -/
example :
    let omitted := DayOptionalDate.ofOmittedDay? 2024 6
    omitted.map (·.resolve .firstDay) = date? 2024 6 1 ∧
      omitted.map (·.resolve .lastDay) = date? 2024 6 30 := by
  native_decide

/- Month-end completion is leap-aware, while a full value ignores the endpoint. -/
example :
    (DayOptionalDate.ofOmittedDay? 2024 2).map (·.resolve .lastDay) =
        date? 2024 2 29 ∧
      (date? 2024 6 15).map (fun date =>
        ((DayOptionalDate.full date).resolve .firstDay,
          (DayOptionalDate.full date).resolve .lastDay)) =
        (date? 2024 6 15).map (fun date => (date, date)) := by
  native_decide

/- Formal admission completes the omitted day before applying the universal Date floor. -/
example :
    DayOptionalDate.ofOmittedDay? 1583 10 = none ∧
      (DayOptionalDate.ofOmittedDay? 1583 11).isSome := by
  native_decide

/- First/last selection reaches the existing Date comparison and produces different verdicts. -/
example :
    let expected := (date? 2024 6 15).get (by native_decide)
    let source := (DayOptionalDate.ofOmittedDay? 2024 6).get (by native_decide)
    let cell : CheckedCell DayOptionalDate := {
      rawPresent := true
      parsed := some source
      findings := [] }
    evaluate? .firstDay .before expected cell = some (.fired .value) ∧
      evaluate? .lastDay .before expected cell = some .notFired := by
  native_decide

/- Empty and formally unavailable sources retain the established direct-Date verdicts. -/
example :
    let expected := (date? 2024 6 15).get (by native_decide)
    let empty : CheckedCell DayOptionalDate := {
      rawPresent := false
      parsed := none
      findings := [] }
    evaluate? .firstDay .equal expected empty = some .notFired ∧
      evaluate? .lastDay .equal expected
        (empty.withFinding .malformed) = some .unknown := by
  native_decide

/- This first checked consumer admits exactly the day-optional Date slice and fails closed on every neighboring mode. -/
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
        0 .firstDay .equal expected).isOk = false ∧
      (elaborateValueAsDateComparison
        (modelWith (dayOptionalSource .yearOptional))
        0 .firstDay .equal expected).isOk = false ∧
      (elaborateValueAsDateComparison
        (modelWith (dayOptionalSource .dayOptional "yyyy/M/d"))
        0 .firstDay .equal expected).isOk = false := by
  native_decide

end A12Kernel.Conformance.ValueAsDate
