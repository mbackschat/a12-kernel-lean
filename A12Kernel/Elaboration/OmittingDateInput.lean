import A12Kernel.Elaboration.PartialDateInput
import A12Kernel.Semantics.DateRangeOverlap
import A12Kernel.Semantics.LegacyCalendarExpression

/-! # Checked component-omitting Date input

A DATE declaration may carry a format that **omits components**: measured at kernel 30.8.1, `yyyy`,
`yyyy-MM`, `yyyyMM`, `MM`, `MM-dd`, `MMdd`, `ddMM`, and `dd.MM.` are legal DATE formats alongside the three complete
ones. Such a declaration's stored text is shorter than a complete date and its value denotes either an
interval or a yearless calendar position.

All eight are in this module's checked subset. `dd.MM.` is the German short date whose **trailing dot is
part of the format** — `dd.MM` without it stays refused as a declaration — and both of its directions are
measured rather than read off the string. Reading: `05.13.` is refused, which a month-then-day format would
accept as May 13th, so the order is day-then-month; `05.03` (no trailing dot), `5.3.` (short widths),
`05.03.2020` (an extra component) and `0503` (no separators) are each refused, and every one of them draws
the **same** format cause the rest of this family draws ([checkpoint](../../docs/sources/temporal-and-message-probes.md#src-dotted-short-date-format)).
Writing: a cross-spelling copy out of an `MM-dd` source stores `11.06.` and, in the row that settles it,
`31.01.` — a day of 31 cannot be read as a month, so this position renders into the target's declared
format rather than copying the source's text.

The three year-bearing formats classify into an existing `PartiallyKnownDateValue`: a year alone is the
omitted-month shape and a year-month is the omitted-day shape, so every existing `ValueAsDate` consumer
reads them through the endpoint resolver it already has.

The **yearless** formats cannot: a month without a year denotes no interval of concrete dates, so it
has no `PartiallyKnownDateValue` form. They classify into the `MonthDayValue` the DateRange family
already uses for exactly this, reached here through a local two-armed result rather than by widening the
partial-Date domain with a shape most of its consumers could not resolve.

Formal completion precedes the stored-Date position check. Year-bearing formats supply January and/or
day one; month-day formats append the Base Year (default 2000), while month-only formal checking uses
the parser's 1970 default. Runtime completion remains separate and uses the model's Base Year. The
calendar-expression fragment-limit matrix (2026-10-04) separates these stages and retains `dateInvalid`
for a completed label below the floor, alongside `dateFormat` for syntax and reality failures.

**The separator is exact in both directions.** `yyyy-MM` refuses `202006` and `yyyyMM` refuses
`2020-06`, so the two spellings are separate formats rather than one lenient parser.

**A yearless day's bound depends on whether the model declares a Base Year.** Without one no year is
available to decide leapness, so the bound is the month's greatest possible day with February at 29 —
the `yearlessLastDay` rule the overlap owner already states rather than a second account of it — locked
at the named April, January, and February boundaries. **With one, the bound is that month's length in
that year**, so `02-29` is admitted under a leap Base Year and refused under a common one, measured on
bytes differing in nothing else. February is the only month whose two answers differ. -/

namespace A12Kernel

namespace OmittingDateFormat

/-- One exact fixed-width digit run. Every width violation and every non-digit fails here, which is why
these failures share the format cause. -/
private def digitsOfWidth? (part : String) (width : Nat) : Option Nat :=
  if part.length == width && part.all Char.isDigit then part.toNat? else none

/-- Split stored text into the year and month a year-bearing format carries. Widths are fixed and the
separator is literal, so a short year, an extra component, and a wrong separator all fail here alike. -/
def parseYearComponents? (format : OmittingDateFormat) (text : String) :
    Option (Int × Option Nat) :=
  match format with
  | .year => (digitsOfWidth? text 4).map fun year => ((year : Int), none)
  | .yearMonthDashed =>
      match text.splitOn "-" with
      | [yearText, monthText] => do
          let year ← digitsOfWidth? yearText 4
          let month ← digitsOfWidth? monthText 2
          pure ((year : Int), some month)
      | _ => none
  | .yearMonthConcatenated =>
      if text.length == 6 then do
        let year ← digitsOfWidth? (text.take 4).toString 4
        let month ← digitsOfWidth? (text.drop 4).toString 2
        pure ((year : Int), some month)
      else none
  | .month | .monthDay | .monthDayConcatenated | .dayMonthConcatenated
  | .dayMonthDotted => none

/-- The day bound a yearless value is checked against.

    **A declared Base Year tightens it.** Without one no year is available to decide leapness, so the
    bound is the month's greatest possible day and February reaches 29; with one, the bound is that
    month's length *in that year*, so a February 29 is admitted under a leap Base Year and refused
    under a common one ([checkpoint](../../docs/SOURCES.md#src-yearless-day-bound-reads-the-base-year)).
    February is the only month whose two answers differ, which is why one witness settles the whole
    rule rather than one month of it. -/
def yearlessDayBound (baseYear : Option Int) (month : Nat) : Nat :=
  match baseYear with
  | none => YearlessInterval.yearlessLastDay month
  | some anchorYear => (DateParts.daysInMonth? anchorYear month).getD 0

/-- Split stored text into the yearless month and day a yearless format carries, with `MM` supplying day
one so both formats produce the same shape.

The day bound is `yearlessDayBound`, so it reads the model's Base Year when one is declared. `MM` is
bounded too even though it authors no day: its implied day one is still checked against a real month,
which is what refuses month `00` and month `13`. -/
def parseYearlessComponents? (format : OmittingDateFormat) (baseYear : Option Int)
    (text : String) : Option MonthDayValue :=
  let accept (month day : Nat) : Option MonthDayValue :=
    if 1 ≤ month && month ≤ 12 && 1 ≤ day &&
        day ≤ yearlessDayBound baseYear month then
      some { month, day }
    else none
  match format with
  | .month => (digitsOfWidth? text 2).bind fun month => accept month 1
  | .monthDay =>
      match text.splitOn "-" with
      | [monthText, dayText] => do
          let month ← digitsOfWidth? monthText 2
          let day ← digitsOfWidth? dayText 2
          accept month day
      | _ => none
  | .monthDayConcatenated =>
      if text.length == 4 then do
        let month ← digitsOfWidth? (text.take 2).toString 2
        let day ← digitsOfWidth? (text.drop 2).toString 2
        accept month day
      else none
  | .dayMonthConcatenated =>
      if text.length == 4 then do
        let day ← digitsOfWidth? (text.take 2).toString 2
        let month ← digitsOfWidth? (text.drop 2).toString 2
        accept month day
      else none
  | .dayMonthDotted =>
      -- The trailing dot makes the third part exist and be empty; `dd.MM` yields two parts and is
      -- refused here exactly as the Kernel refuses it as a *format*, while `dd.MM.yyyy` yields a
      -- nonempty third part. Both are measured rows rather than consequences of this spelling.
      match text.splitOn "." with
      | [dayText, monthText, ""] => do
          let day ← digitsOfWidth? dayText 2
          let month ← digitsOfWidth? monthText 2
          accept month day
      | _ => none
  | .year | .yearMonthDashed | .yearMonthConcatenated => none

end OmittingDateFormat

/-- Fail-closed reasons before a declaration can use the component-omitting Date classifier. -/
inductive CanonicalOmittingDateFieldError where
  | notDate (path : List String) (actual : FieldKind)
  | policyUnavailable (path : List String)
  /-- The declaration is a Date whose format is outside this component-omitting
  classifier, including a complete or otherwise unsupported spelling. -/
  | unsupportedFormat (path : List String) (format : String)
  deriving Repr, DecidableEq

/-- One Date declaration whose component-omitting format is model-owned. -/
structure CheckedOmittingDateInputField where
  private mk ::
  declaration : FlatFieldDecl
  field : FlatTemporalField
  policy : TemporalTargetPolicy
  format : OmittingDateFormat
  fieldOwned : declaration.toTemporalField? = some field
  policyOwned : declaration.toTemporalTargetPolicy? = some policy
  formatOwned : OmittingDateFormat.ofSource? policy.format = some format

/-- Certify one component-omitting Date declaration without imposing an addressing shape. -/
def certifyOmittingDateInputField (declaration : FlatFieldDecl) :
    Except CanonicalOmittingDateFieldError CheckedOmittingDateInputField :=
  match hField : declaration.toTemporalField? with
  | none => .error (.notDate declaration.path declaration.policy.kind)
  | some field =>
      match hPolicy : declaration.toTemporalTargetPolicy? with
      | none => .error (.policyUnavailable declaration.path)
      | some policy =>
          match hFormat : OmittingDateFormat.ofSource? policy.format with
          | none =>
              .error (.unsupportedFormat declaration.path policy.format)
          | some format => .ok {
              declaration
              field
              policy
              format
              fieldOwned := hField
              policyOwned := hPolicy
              formatOwned := hFormat }

/-- The value a component-omitting Date declaration stores. The two arms are not interchangeable: a
year-bearing value denotes an interval of concrete dates and resolves to endpoints, while a yearless one
denotes a calendar position with no year and therefore has no `FullDate` form at all. Keeping them
separate is what stops a consumer from silently completing a yearless value against some year: a
completion names its year, as `OmittingDateStoredValue.earliestCivil?` takes it. -/
inductive OmittingDateStoredValue where
  | yearBearing (value : PartiallyKnownDateValue)
  | yearless (value : MonthDayValue)
  deriving Repr, DecidableEq

/-- The earliest concrete date an admitted value denotes, which is how the Kernel completes a date
fragment where it needs one concrete date, a comparison or a computed fragment's read-back: an omitted
day is the 1st, an omitted month January, and a yearless value takes `year`, the caller's choice of Base
Year. A range's finish completes to the latest date instead, which this does not cover. A year-bearing
value with its year omitted completes to none; `classifyStoredForModel` never produces that arm. -/
def OmittingDateStoredValue.earliestCivil? (year : Int) : OmittingDateStoredValue → Option CivilDate
  | .yearBearing (.full date) => some date.civil
  | .yearBearing (.omittedDay date) => some date.first.civil
  | .yearBearing (.omittedMonth date) => some date.first.civil
  | .yearBearing .omittedYear => none
  | .yearless value => CivilDate.ofParts? { year, month := value.month, day := value.day }

/-- One classified component-omitting Date cell. -/
inductive OmittingDateInputCell where
  | presentEmpty
  | rejected (cause : BaseFormalCause)
  | admitted (value : OmittingDateStoredValue)
  deriving Repr, DecidableEq

/-- Classify the rendered or authored text, including the format-specific formal completion before
position checks. Kernel `DateUtil.completeDateAndFormat` appends the Base Year only when both day and
month are present; the fragment-limit grid (2026-10-04) separates that from runtime completion. -/
def OmittingDateFormat.classifyStored (format : OmittingDateFormat) (baseYear : Option Int)
    (youngerThan1900Check : Bool) (text : String) : Except FullDateTargetError OmittingDateStoredValue := do
  let formatError := FullDateTargetError.renderingRejected .dateFormat
  let (parts, value) ← if format.carriesYear then do
      let (parsedYear, parsedMonth) ← (format.parseYearComponents? text).getDM (throw formatError)
      pure (({ year := parsedYear, month := parsedMonth.getD 1, day := 1 } : DateParts), none)
    else do
      let value ← (format.parseYearlessComponents? baseYear text).getDM (throw formatError)
      let year := if format == .month then 1970 else baseYear.getD 2000
      pure (({ year, month := value.month, day := value.day } : DateParts), some value)
  if !DateParts.LegacyHybrid.isReal parts then throw formatError
  if youngerThan1900Check && parts.Before FullDate.year1900Start.civil.parts then
    throw .before1900
  if parts.Before CivilDate.gregorianFloor.parts then throw .beforeGregorianFloor
  match value with
  | some value => pure (.yearless value)
  | none =>
      if format == .year then
        pure (.yearBearing (.omittedMonth (← (OmittedMonthDate.ofYear? parts.year).getDM
          (throw formatError))))
      else
        pure (.yearBearing (.omittedDay (← (OmittedDayDate.ofYearMonth? parts.year parts.month).getDM
          (throw formatError))))

/-- Stored input and computed rendering use the same format-owned classifier. Empty input is handled
before formal checking, and position failures retain the distinct `dateInvalid` observation. -/
def CheckedOmittingDateInputField.classifyStoredForModel
    (checked : CheckedOmittingDateInputField) (baseYear : Option Int)
    (text : String) : OmittingDateInputCell :=
  if text.isEmpty then .presentEmpty
  else match checked.format.classifyStored baseYear checked.policy.youngerThan1900Check text with
    | .ok value => .admitted value
    | .error (.renderingRejected cause) => .rejected cause
    | .error .before1900 | .error .beforeGregorianFloor => .rejected .dateInvalid

end A12Kernel
