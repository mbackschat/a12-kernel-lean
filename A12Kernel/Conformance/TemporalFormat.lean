import A12Kernel.Elaboration.Flat.Model

/-! # Temporal format-admission executable locks -/

namespace A12Kernel.Conformance.TemporalFormat

open A12Kernel

private def yearMonth : TemporalComponents :=
  { year := true, month := true, day := false, hour := false, minute := false, second := false }

private def fullDate : TemporalComponents :=
  { year := true, month := true, day := true, hour := false, minute := false, second := false }

private def monthDay : TemporalComponents :=
  { year := false, month := true, day := true, hour := false, minute := false, second := false }

private def fullDateTime : TemporalComponents :=
  { year := true, month := true, day := true, hour := true, minute := true, second := true }

private def hoursMinutes : TemporalComponents :=
  { year := false, month := false, day := false, hour := true, minute := true, second := false }

private def hoursMinutesSeconds : TemporalComponents :=
  { year := false, month := false, day := false, hour := true, minute := true, second := true }

private def monthDayTime : TemporalComponents :=
  { year := false, month := true, day := true, hour := true, minute := true, second := true }

/- Direct ordering admits unequal date component sets; aggregate admission does not. -/
example :
    TemporalComparisonOp.before.admitsFormats false yearMonth fullDate = true ∧
      temporalAggregateFormatsCompatible false yearMonth fullDate = false := by
  decide

/- Date and DateTime may be ordered, but equality requires matching time presence. -/
example :
    TemporalComparisonOp.before.admitsFormats false fullDate fullDateTime = true ∧
      TemporalComparisonOp.equal.admitsFormats false fullDate fullDateTime = false := by
  decide

/- Time comparison ignores a seconds-display mismatch; aggregate admission retains it. -/
example :
    TemporalComparisonOp.equal.admitsFormats false hoursMinutes hoursMinutesSeconds = true ∧
      temporalAggregateFormatsCompatible false hoursMinutes hoursMinutesSeconds = false := by
  decide

/- Base Year supplies the only otherwise-missing year component. -/
example :
    TemporalComparisonOp.before.admitsFormats false monthDay fullDate = false ∧
      TemporalComparisonOp.before.admitsFormats true monthDay fullDate = true ∧
      temporalAggregateFormatsCompatible true monthDay fullDate = true := by
  decide

/- Time-only and date-containing formats remain different comparison classes even when Base Year supplies missing years to date fragments. -/
example :
    TemporalComparisonOp.before.admitsFormats false fullDate hoursMinutes = false ∧
      TemporalComparisonOp.before.admitsFormats true fullDate hoursMinutes = false := by
  decide

/- `Now` adds a time-component requirement beyond ordinary directional format admission. -/
example :
    TemporalComparisonOp.before.admitsFormats false fullDate TemporalComponents.now = true ∧
      TemporalComparisonOp.before.admitsNow false fullDate = false ∧
      TemporalComparisonOp.before.admitsNow false fullDateTime = true := by
  decide

/- Ordinary compatibility still rejects a time-only operand, and Base Year controls a yearless DateTime operand. -/
example :
    TemporalComparisonOp.before.admitsNow false hoursMinutesSeconds = false ∧
      TemporalComparisonOp.before.admitsNow false monthDayTime = false ∧
      TemporalComparisonOp.before.admitsNow true monthDayTime = true := by
  decide

/- Full DateTime aggregate admission requires all six components. -/
example :
    fullDateTime.isFullDateTime = true ∧
      hoursMinutesSeconds.isFullDateTime = false := by
  decide

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

private def validationError (model : FlatModel) : Option ResolveError :=
  match model.validate with
  | .ok () => none
  | .error error => some error

/- Exact source and four-valued partial-date mode survive independently of component shape. -/
example :
    let european := temporalTarget 0 "EuropeanDate" "dd.MM.yyyy"
      .date fullDate .dayOptional
    let iso := temporalTarget 1 "IsoDate" "yyyy-MM-dd"
      .date fullDate .monthOptional
    european.toTemporalTargetPolicy?.map (fun policy =>
        (policy.format, policy.partialMode)) =
        some ("dd.MM.yyyy", .dayOptional) ∧
      iso.toTemporalTargetPolicy?.map (fun policy =>
        (policy.format, policy.partialMode)) =
        some ("yyyy-MM-dd", .monthOptional) := by
  native_decide

/- A non-full partial-date mode requires a full Date declaration. -/
example :
    let target := temporalTarget 0 "ScheduledAt" "yyyy-MM-dd'T'HH:mm:ss"
      .dateTime fullDateTime .dayOptional
    validationError { fields := [target] } =
      some (.invalidTemporalTargetPolicy target.path
        .partialModeRequiresFullDate) := by
  native_decide

/- The opt-in pre-1900 check belongs only to Date declarations. -/
example :
    let target := temporalTarget 0 "ScheduledAt" "yyyy-MM-dd'T'HH:mm:ss"
      .dateTime fullDateTime .full true
    validationError { fields := [target] } =
      some (.invalidTemporalTargetPolicy target.path
        .youngerThan1900RequiresDate) := by
  native_decide

/- A retained exact format source cannot be empty. -/
example :
    let target := temporalTarget 0 "Date" "" .date fullDate
    validationError { fields := [target] } =
      some (.invalidTemporalTargetPolicy target.path .emptyFormat) := by
  native_decide

/- Temporal target policy cannot attach to a non-temporal declaration. -/
example :
    let target := temporalTarget 0 "Date" "dd.MM.yyyy" .date fullDate
    let numberTarget : FlatFieldDecl := {
      target with
      policy := { kind := .number { scale := 0, signed := true } } }
    validationError { fields := [numberTarget] } =
      some (.temporalTargetPolicyRequiresTemporal numberTarget.path) := by
  native_decide

end A12Kernel.Conformance.TemporalFormat
