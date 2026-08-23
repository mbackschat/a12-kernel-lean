import A12Kernel.Elaboration.Flat.Model

/-! # Temporal format-admission executable locks

**Three temporal format gates, measured to be genuinely different, with different codes.** They are kept
apart here because a reader who unified any two of them would reject legal models:

- *Direct comparison* tests **year presence** after optional Base-Year supplementation plus date-class
  agreement, and deliberately not component-set equality. Its refusal is `MVK_INVALID_COMPARE_TO_DATE`.
- *Aggregates* — `MaxValue`, `MinValue`, and `NumberOfDifferentValues` — require component sets to agree
  **exactly** after that supplementation. Their refusal is `MVK_DATEFORMATS_NOT_COMPATIBLE`. This is
  strictly stronger than comparison, which the trusted proof root states as a theorem rather than a case.
- *`FieldValuesNotUnique`* requires one identical declared **format string**, which no component-set rule
  can express. Its refusal is `MVK_ONLY_STRING_ENUM_NUMBER_DATE_ALLOWED`, and its own owner holds that
  gate; the cases below only fix that the aggregate rule does **not** reproduce it.
-/

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

private def dateRangeDeclaration
    (id : FieldId) (name format separator : String) : FlatFieldDecl := {
  id
  groupPath := ["Order"]
  name
  policy := { kind := .dateRange }
  dateRangePolicy := some { format, separator } }

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

/- DateRange retains its exact declaration-owned format and separator through the checked projections. -/
example :
    let declaration := dateRangeDeclaration 0 "Travel" "yyyy-MM-dd" "/"
    validationError { fields := [declaration] } = none ∧
      declaration.toDateRangeField?.map (·.id) = some declaration.id ∧
      declaration.toDateRangeDeclarationPolicy?.map (fun policy =>
        (policy.format, policy.separator)) = some ("yyyy-MM-dd", "/") ∧
      declaration.toPresenceField = .dateRange { id := declaration.id } := by
  native_decide

/- Every DateRange declaration requires its policy. -/
example :
    let declaration : FlatFieldDecl := {
      id := 0
      groupPath := ["Order"]
      name := "Travel"
      policy := { kind := .dateRange } }
    validationError { fields := [declaration] } =
      some (.dateRangeDeclarationPolicyRequired declaration.path) := by
  native_decide

/- A refusal separates an absent format, an illegal empty separator, and an unsupported pair whose sources are both present. Only the third cause is new to the allowlist, and none of the three claims a Kernel diagnostic class. -/
example :
    let emptyFormat := dateRangeDeclaration 0 "Travel" "" "/"
    let emptySeparator := dateRangeDeclaration 1 "Stay" "yyyy-MM-dd" ""
    let separatorSwap := dateRangeDeclaration 2 "Trip" "yyyy-MM-dd" "-"
    let unknownFormat := dateRangeDeclaration 3 "Leg" "yyyyMM" "/"
    validationError { fields := [emptyFormat] } =
        some (.invalidDateRangeDeclarationPolicy emptyFormat.path .emptyFormat) ∧
      validationError { fields := [emptySeparator] } =
        some (.invalidDateRangeDeclarationPolicy emptySeparator.path .emptySeparator) ∧
      validationError { fields := [separatorSwap] } =
        some (.invalidDateRangeDeclarationPolicy separatorSwap.path .unsupportedPair) ∧
      validationError { fields := [unknownFormat] } =
        some (.invalidDateRangeDeclarationPolicy unknownFormat.path .unsupportedPair) := by
  native_decide

/- The complete measured candidate grid admits exactly the eight Kernel-established DateRange pairs. Separator swaps, every dot separator, `yyyyMM`, and every empty separator other than month-only are refused. -/
example :
    let formats := ["dd.MM.yyyy", "yyyy-MM-dd", "yyyy", "yyyy-MM", "MM", "MM-dd",
      "dd.MM", "yyyyMM"]
    let separators := ["-", "/", ".", ""]
    ((formats.flatMap fun format => separators.map fun separator =>
        ((format, separator),
          (validationError
            { fields := [dateRangeDeclaration 0 "Travel" format separator] }).isNone)).filter
      (·.2)).map (·.1) =
      [("dd.MM.yyyy", "-"), ("yyyy-MM-dd", "/"), ("yyyy", "/"), ("yyyy-MM", "/"),
        ("MM", "/"), ("MM", ""), ("MM-dd", "/"), ("dd.MM", "-")] := by
  native_decide

/- DateRange policy cannot attach to another declaration kind. -/
example :
    let range := dateRangeDeclaration 0 "Travel" "yyyy-MM-dd" "/"
    let scalarDate : FlatFieldDecl := {
      range with
      policy := { kind := .temporal .date fullDate } }
    validationError { fields := [scalarDate] } =
      some (.dateRangeDeclarationPolicyRequiresDateRange scalarDate.path) := by
  native_decide

/-! ## The aggregate gate is component sets, not format spelling

Measured at kernel 30.8.1 through `rule add --dry-run`, on a model declaring every component-omitting
Date format beside two complete ones. The rows that matter are the ones where the two candidate readings
disagree: **two different spellings of the same component set**. -/

/- `yyyy-MM` beside `yyyyMM`, and `yyyy-MM-dd` beside `dd.MM.yyyy`: different declared format strings,
identical component sets, and the aggregate gate **admits** both — measured on `MaxValue`, `MinValue`, and
`NumberOfDifferentValues`, at an explicit field list, at explicit starred fields, and at a group operand's
expansion alike. So this gate cannot be reading the format spelling. -/
example :
    temporalAggregateFormatsCompatible false yearMonth yearMonth = true ∧
      temporalAggregateFormatsCompatible false fullDate fullDate = true := by
  native_decide

/- The same pair is **refused** by `FieldValuesNotUnique`, whose gate is the declared format string. That
carrier's rule is therefore not derivable from component sets, which is why the two live apart. -/
example :
    temporalAggregateFormatsCompatible false yearMonth fullDate = false ∧
      TemporalComparisonOp.admitsFormats .equal false yearMonth fullDate = true := by
  native_decide

/- **A Base Year lifts the aggregate gate for a yearless operand, but only when the remaining components
already agree.** Measured on four pairs: a yearless month aggregates with `yyyy-MM` and a yearless
month-day with a complete date, while both stay refused against a year-only operand whose other
components differ. This is the row that shows supplementation happens *before* the comparison, not
after. -/
example :
    temporalAggregateFormatsCompatible true monthDay fullDate = true ∧
      temporalAggregateFormatsCompatible false monthDay fullDate = false ∧
      temporalAggregateFormatsCompatible true monthDay yearMonth = false := by
  native_decide

end A12Kernel.Conformance.TemporalFormat
