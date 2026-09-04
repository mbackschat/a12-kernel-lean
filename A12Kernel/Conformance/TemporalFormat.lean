import A12Kernel.Elaboration.Flat.Model

/-! # Temporal format-admission executable locks

**Four temporal format gates, measured to be genuinely different, with different codes.** They are kept
apart here because a reader who unified any two of them would reject legal models:

- *Direct comparison* tests **year presence** after optional Base-Year supplementation plus date-class
  agreement, and deliberately not component-set equality. Its refusal is `MVK_INVALID_COMPARE_TO_DATE`.
- *Aggregates* — `MaxValue`, `MinValue`, and `NumberOfDifferentValues` — require component sets to agree
  **exactly** after that supplementation. Their refusal is `MVK_DATEFORMATS_NOT_COMPATIBLE`. This is
  strictly stronger than comparison, which the trusted proof root states as a theorem rather than a case.
- *`FieldValuesNotUnique`* requires one identical declared **format string**, which no component-set rule
  can express. Its refusal is `MVK_ONLY_STRING_ENUM_NUMBER_DATE_ALLOWED`, and its own owner holds that
  gate; the cases below only fix that the aggregate rule does **not** reproduce it.
- *A two-operand temporal operation* requires each operand to resolve the **one component its unit steps
  in**, and only then that the two agree about the year. The two grounds carry different codes —
  `MVK_WRONG_DATE_FORMAT_FOR_OP` and `MVK_DATE_WITH_AND_WITHOUT_YEAR` — and their order is measured, not
  chosen. This gate is neither weaker nor stronger than comparison: one input below is admitted by an
  ordering comparison and refused by a day difference, and another the reverse.
-/

namespace A12Kernel.Conformance.TemporalFormat

open A12Kernel

private def yearMonth : TemporalComponents :=
  { year := true, month := true, day := false, hour := false, minute := false, second := false }

private def yearOnly : TemporalComponents :=
  { year := true, month := false, day := false, hour := false, minute := false, second := false }

private def fullDate : TemporalComponents :=
  { year := true, month := true, day := true, hour := false, minute := false, second := false }

private def monthDay : TemporalComponents :=
  { year := false, month := true, day := true, hour := false, minute := false, second := false }

/-- `MM`: the one declared date format that resolves a month but no day, which is what makes it
the separator for an operation's granularity gate. -/
private def monthOnly : TemporalComponents :=
  { year := false, month := true, day := false, hour := false, minute := false, second := false }

private def fullDateTime : TemporalComponents :=
  { year := true, month := true, day := true, hour := true, minute := true, second := true }

/-- Hour and minute without second. **No declared format reaches this set**: the Kernel refuses
`HH:mm` on a Time, Date, and DateTime declaration alike, against an admitted `HH:mm:ss` control.
The fixture is kept because the gates below are total functions whose behaviour here is defined
and worth locking, not because a model can present it; the cases using it say so. -/
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

/- A year-only endpoint is incomplete but still compares with a full Date; year presence, not completeness, is the direct gate. -/
example :
    TemporalComparisonOp.equal.admitsFormats false yearOnly fullDate = true ∧
      TemporalComparisonOp.equal.admitsFormats false monthDay fullDate = false := by
  decide

/- Date and DateTime may be ordered, but equality requires matching time presence. -/
example :
    TemporalComparisonOp.before.admitsFormats false fullDate fullDateTime = true ∧
      TemporalComparisonOp.equal.admitsFormats false fullDate fullDateTime = false := by
  decide

/- Time comparison ignores a seconds-display mismatch; aggregate admission retains it. Both halves
lock the **total functions** on an input no legal model presents — `hoursMinutes` is unauthorable,
per its own note above — so read this as fixing the two gates' disagreement, never as a reachable
Time rule. -/
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

/- **A temporal operation's operand gate is granularity, not year-bearing-ness.** `MM` is refused
in `DifferenceInDays` because it resolves no day, while the yearless `MM-dd` is admitted against a
yearless counterpart — so the refusal follows the missing component rather than the missing year.
Measured at a12-dmkits `eded8263` on one model varying only the operand's declared format. A gate
that demanded a complete date would refuse the admitted row. -/
example :
    TemporalOperationUnit.admitsOperands .days false monthOnly monthDay = false ∧
      TemporalOperationUnit.admitsOperands .days false monthDay monthDay = true := by
  decide

/- **Granularity is decided before year agreement, and this pair is the only row that shows it.**
`MM` beside a complete date disagrees about the year *as well* as lacking a day, and the Kernel
reports `MVK_WRONG_DATE_FORMAT_FOR_OP` rather than `MVK_DATE_WITH_AND_WITHOUT_YEAR`. Checking
agreement first would return the other fault on the identical input. -/
example :
    TemporalOperationUnit.operandFault? .days false monthOnly fullDate = some .granularity := by
  decide

/- **Year agreement is the second gate and carries its own code.** A complete date beside a
yearless literal resolves the day on both sides and is still refused, which is the row a12-dmkits
could not see: both of its rows used a year-free field, where the granularity gate fires first and
masks this one. -/
example :
    TemporalOperationUnit.operandFault? .days false fullDate monthDay
        = some .yearDisagreement ∧
      TemporalOperationUnit.admitsOperands .days false fullDate fullDate = true := by
  decide

/- **A declared Base Year lifts the year-agreement gate here exactly as it does for a direct
comparison.** The mixed pair above is admitted once the model declares one. Measured rather than
inherited from the comparison carrier: the same reuse was wrong twice in this family already, and a
gate that read raw years would refuse this row. -/
example :
    TemporalOperationUnit.admitsOperands .days true fullDate monthDay = true ∧
      TemporalOperationUnit.admitsOperands .days false fullDate monthDay = false := by
  decide

/- **Supplementation feeds the granularity gate too, and supplies the year alone.** A yearless pair
is refused in `years` with no Base Year and admitted once one is declared — so the Base Year makes
an operand steppable in a unit it could not otherwise resolve. It never supplies a day, so the
month-only operand stays refused in `days` in the very same configured model. That second row is
what stops the first from being read as "a Base Year admits anything". -/
example :
    TemporalOperationUnit.admitsOperands .years false monthDay monthDay = false ∧
      TemporalOperationUnit.admitsOperands .years true monthDay monthDay = true ∧
      TemporalOperationUnit.admitsOperands .days true monthOnly monthDay = false := by
  decide

/- **The required component is the unit's own, separated on a single operand.** A `yyyy` field
resolves a year and no month, and against the same complete-date counterpart it is admitted in
`years` while `months` and `days` are both refused. A gate reading "the coarsest component
present" or "a complete date" refuses the admitted row, and one reading date class alone admits
all three. Measured at a12-dmkits `eded8263`, with all three complete-date controls admitted so
no unit's channel is dead. -/
example :
    TemporalOperationUnit.admitsOperands .years false yearOnly fullDate = true ∧
      TemporalOperationUnit.admitsOperands .months false yearOnly fullDate = false ∧
      TemporalOperationUnit.admitsOperands .days false yearOnly fullDate = false := by
  decide

/- The same three units on a complete-date pair, which is what keeps the row above a statement
about `yyyy` rather than about `months` and `days` being unreachable. -/
example :
    TemporalOperationUnit.admitsOperands .years false fullDate fullDate = true ∧
      TemporalOperationUnit.admitsOperands .months false fullDate fullDate = true ∧
      TemporalOperationUnit.admitsOperands .days false fullDate fullDate = true := by
  decide

/- **The clock units are implemented but have no separator on any legal model**, so this case
locks the total function rather than a reachable row: every admitted time-bearing format carries
hour, minute, and second together, and `HH:mm` is refused on every declaration kind. `hoursMinutes`
is therefore unauthorable, and a consumer must not read this as a Kernel-reachable distinction. -/
example :
    TemporalOperationUnit.admitsOperands .seconds false hoursMinutes hoursMinutesSeconds
        = false ∧
      TemporalOperationUnit.admitsOperands .minutes false hoursMinutes hoursMinutesSeconds
        = true := by
  decide

/- **The operation gate and the comparison gate are incomparable — neither implies the other**, which
is why no consumer may derive one from the other in either direction. A month-only pair is admitted by
an ordering comparison and refused by a day difference, because comparison never demands a particular
component. A month-day-time operand beside a time-only one is the converse: the day difference's
sibling `hours` unit admits it since both resolve an hour, while comparison refuses it for disagreeing
about date class. Weakening this to "the operation gate is stronger" would be wrong on the second row. -/
example :
    (TemporalComparisonOp.admitsFormats .before false monthOnly monthOnly = true ∧
        TemporalOperationUnit.admitsOperands .days false monthOnly monthOnly = false) ∧
      (TemporalComparisonOp.admitsFormats .before false monthDayTime hoursMinutes = false ∧
        TemporalOperationUnit.admitsOperands .hours false monthDayTime hoursMinutes = true) := by
  decide

end A12Kernel.Conformance.TemporalFormat
