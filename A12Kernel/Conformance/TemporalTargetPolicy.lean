import A12Kernel.Elaboration.TemporalTargetPolicy

/-! # Checked temporal-target policy locks -/

namespace A12Kernel.Conformance.TemporalTargetPolicy

open A12Kernel

private def fullDate : TemporalComponents := TemporalComponents.fullDate

private def temporalTarget
    (id : FieldId) (name format : String)
    (kind : TemporalKind) (components : TemporalComponents)
    (partialMode : TemporalPartialMode := .full)
    (youngerThan1900Check : Bool := false) : FlatFieldDecl := {
  id
  groupPath := ["Order"]
  name
  policy := { kind := .temporal kind components }
  temporalTargetPolicy := some {
    format
    partialMode
    youngerThan1900Check } }

private def checkedPolicyOf
    (model : FlatModel) (target : FieldId) :
    Option (TemporalTargetPolicy × String) :=
  match elaborateTemporalTargetPolicy model target with
  | .ok checked => some (checked.policy, checked.timeZoneId)
  | .error _ => none

private def errorOf
    (result : Except TemporalTargetElabError value) :
    Option TemporalTargetElabError :=
  match result with
  | .ok _ => none
  | .error error => some error

/- The checked target exposes the exact declaration policy and the same model's zone. -/
example :
    let target := temporalTarget 0 "Date" "dd.MM.yyyy"
      .date fullDate .yearOptional true
    let model : FlatModel := {
      fields := [target]
      timeZoneId := "Europe/Berlin" }
    checkedPolicyOf model 0 =
        some ({
          format := "dd.MM.yyyy"
          partialMode := .yearOptional
          youngerThan1900Check := true },
          "Europe/Berlin") := by
  native_decide

/- A non-temporal target reaches a distinct shape error without target policy. -/
example :
    let target : FlatFieldDecl := {
      id := 0
      groupPath := ["Order"]
      name := "Amount"
      policy := { kind := .number { scale := 0, signed := true } } }
    errorOf (elaborateTemporalTargetPolicy { fields := [target] } 0) =
      some (.targetNotTemporal 0) := by
  native_decide

/- Time metadata is coherent but outside this first Date/DateTime target boundary. -/
example :
    let time : TemporalComponents :=
      { year := false, month := false, day := false,
        hour := true, minute := true, second := true }
    let target := temporalTarget 0 "Time" "HH:mm:ss" .time time
    errorOf (elaborateTemporalTargetPolicy { fields := [target] } 0) =
      some (.unsupportedTargetKind 0 .time) := by
  native_decide

/- Missing declaration policy is explicit insufficient information, never a guessed canonical format. -/
example :
    let target : FlatFieldDecl := {
      id := 0
      groupPath := ["Order"]
      name := "Date"
      policy := { kind := .temporal .date fullDate } }
    errorOf (elaborateTemporalTargetPolicy { fields := [target] } 0) =
      some (.targetPolicyUnavailable 0) := by
  native_decide

private def fullDateModel
    (format zoneId : String)
    (partialMode : TemporalPartialMode := .full)
    (youngerThan1900Check : Bool := false) : FlatModel := {
  fields := [temporalTarget 0 "Date" format .date fullDate
    partialMode youngerThan1900Check]
  timeZoneId := zoneId }

private def utcInstant?
    (year : Int) (month day hour minute second : Nat) : Option Instant :=
  (LocalDateTime.ofYmdHms? year month day hour minute second).map
    (·.resolveUtc)

private def evaluateAt?
    (model : FlatModel) (instant? : Option Instant) :
    Option FullDateTargetOutcome :=
  match elaborateFullDateTarget model 0, instant? with
  | .ok target, some instant =>
      match target.evaluate (.value instant) with
      | .ok outcome => some outcome
      | .error _ => none
  | _, _ => none

private def fullDateElabError?
    (model : FlatModel) : Option FullDateTargetElabError :=
  match elaborateFullDateTarget model 0 with
  | .ok _ => none
  | .error error => some error

/- The same local date renders differently under the two exact target formats. -/
example :
    (FullDate.ofYmd? 2024 4 7).map (fun date => (
      (FullDateTargetFormat.dayMonthYearDots.render date).text,
      (FullDateTargetFormat.yearMonthDayDashes.render date).text)) =
        some ("07.04.2024", "2024-04-07") := by
  native_decide

/- The model zone is observable at rendering: one instant can cross the local date boundary. -/
example :
    let instant := utcInstant? 2024 1 1 23 30 0
    evaluateAt? (fullDateModel "yyyy-MM-dd" "UTC") instant =
        some (.accepted {
          text := "2024-01-01"
          nonempty := by decide }) ∧
      evaluateAt? (fullDateModel "yyyy-MM-dd" "Europe/Berlin") instant =
        some (.accepted {
          text := "2024-01-02"
          nonempty := by decide }) := by
  native_decide

/- The optional pre-1900 check retains the exact attempted target text; disabling it accepts the same attempt. -/
example :
    let instant := utcInstant? 1899 12 31 0 0 0
    evaluateAt? (fullDateModel "dd.MM.yyyy" "UTC" .full true) instant =
        some (.errored {
          text := "31.12.1899"
          nonempty := by decide } .before1900) ∧
      evaluateAt? (fullDateModel "dd.MM.yyyy" "UTC") instant =
        some (.accepted {
          text := "31.12.1899"
          nonempty := by decide }) := by
  native_decide

/- Every excluded static axis fails explicitly before target execution. -/
example :
    let partialModel := fullDateModel "dd.MM.yyyy" "UTC" .dayOptional
    let unsupportedFormat := fullDateModel "yyyy/M/d" "UTC"
    let unsupportedZone := fullDateModel "dd.MM.yyyy" "Pacific/Apia"
    let dateTime : FlatModel := {
      fields := [temporalTarget 0 "At" "yyyy-MM-dd'T'HH:mm:ss"
        .dateTime TemporalComponents.now] }
    [ fullDateElabError? partialModel
    , fullDateElabError? unsupportedFormat
    , fullDateElabError? unsupportedZone
    , fullDateElabError? dateTime ] =
      [ some (.partialMode 0 .dayOptional)
      , some (.unsupportedFormat 0 "yyyy/M/d")
      , some (.unsupportedZone "Pacific/Apia")
      , some (.targetKind 0 .dateTime) ] := by
  native_decide

end A12Kernel.Conformance.TemporalTargetPolicy
