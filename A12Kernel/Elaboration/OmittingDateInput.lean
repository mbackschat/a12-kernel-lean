import A12Kernel.Elaboration.PartialDateInput
import A12Kernel.Semantics.DateRangeOverlap

/-! # Checked component-omitting Date input

A DATE declaration may carry a format that **omits components**: measured at kernel 30.8.1, `yyyy`,
`yyyy-MM`, `yyyyMM`, `MM`, `MM-dd`, `MMdd`, and `ddMM` are legal DATE formats alongside the three complete ones. Such a
declaration's stored text is shorter than a complete date and its value denotes either an interval or a
yearless calendar position.

The three year-bearing formats classify into an existing `PartiallyKnownDateValue`: a year alone is the
omitted-month shape and a year-month is the omitted-day shape, so every existing `ValueAsDate` consumer
reads them through the endpoint resolver it already has.

The four **yearless** formats cannot: a month without a year denotes no interval of concrete dates, so it
has no `PartiallyKnownDateValue` form. They classify into the `MonthDayValue` the DateRange family
already uses for exactly this, reached here through a local two-armed result rather than by widening the
partial-Date domain with a shape most of its consumers could not resolve.

**One executable rejection cause.** The classifier maps every parse or calendar failure to `dateFormat`
and has no `dateInvalid` constructor arm, because these formats carry no complete date whose position it
could compare with the Gregorian floor. The retained Kernel matrix establishes the named width,
extra-component, separator, component-order, month-range, and greatest-day rows; other stored texts remain
external evidence pending.

**The separator is exact in both directions.** `yyyy-MM` refuses `202006` and `yyyyMM` refuses
`2020-06`, so the two spellings are separate formats rather than one lenient parser.

**A yearless day is validated against its month's greatest possible day, with February at 29**, locked at
the named April, January, and February boundaries: `04-31` is refused where `04-30` is admitted,
`01-31` is admitted, and `02-29` is admitted where `02-30` is refused. No year is available to decide
leapness, so this is the
`yearlessLastDay` rule the overlap owner already states rather than a second account of it. -/

namespace A12Kernel

/-- A DATE declaration format that omits at least one component. -/
inductive OmittingDateFormat where
  /-- `yyyy` — the value is a whole calendar year. -/
  | year
  /-- `yyyy-MM` — the value is a whole calendar month. -/
  | yearMonthDashed
  /-- `yyyyMM` — the same value under a separator-free spelling, refused by the dashed format. -/
  | yearMonthConcatenated
  /-- `MM` — a yearless month, denoting no interval of concrete dates. -/
  | month
  /-- `MM-dd` — a yearless month and day, whose day is bounded by the month's greatest possible. -/
  | monthDay
  /-- `MMdd` — the same month-day value without a separator. -/
  | monthDayConcatenated
  /-- `ddMM` — the same yearless components in day-month order. -/
  | dayMonthConcatenated
  deriving Repr, DecidableEq

namespace OmittingDateFormat

/-- Admit the seven measured component-omitting formats. The three complete formats belong to the full-Date
classifier and are refused here. -/
def ofSource? : String → Option OmittingDateFormat
  | "yyyy" => some .year
  | "yyyy-MM" => some .yearMonthDashed
  | "yyyyMM" => some .yearMonthConcatenated
  | "MM" => some .month
  | "MM-dd" => some .monthDay
  | "MMdd" => some .monthDayConcatenated
  | "ddMM" => some .dayMonthConcatenated
  | _ => none

/-- Whether this format's value carries a year, and therefore denotes an interval of concrete dates. -/
def carriesYear : OmittingDateFormat → Bool
  | .year | .yearMonthDashed | .yearMonthConcatenated => true
  | .month | .monthDay | .monthDayConcatenated | .dayMonthConcatenated => false

/-- The component set a declaration of this format exposes.

Derived from the format rather than declared beside it, because the two cannot disagree: the stored text
is what carries the components, so a `yyyy` field exposing a day would describe a value it has no way to
store. Feeding this to `TemporalComparisonOp.admitsFormats` reproduces the measured comparison matrix
exactly — any two year-bearing formats compare regardless of how many components they carry, and a
yearless one is refused against a year-bearing one without a Base Year. -/
def components : OmittingDateFormat → TemporalComponents
  | .year =>
      { year := true, month := false, day := false
        hour := false, minute := false, second := false }
  | .yearMonthDashed | .yearMonthConcatenated =>
      { year := true, month := true, day := false
        hour := false, minute := false, second := false }
  | .month =>
      { year := false, month := true, day := false
        hour := false, minute := false, second := false }
  | .monthDay | .monthDayConcatenated | .dayMonthConcatenated =>
      { year := false, month := true, day := true
        hour := false, minute := false, second := false }

/-- One exact fixed-width digit run. Every width violation and every non-digit fails here, which is why
one cause suffices for the whole family. -/
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
  | .month | .monthDay | .monthDayConcatenated | .dayMonthConcatenated => none

/-- Split stored text into the yearless month and day a yearless format carries, with `MM` supplying day
one so both formats produce the same shape.

The day bound is the month's **greatest possible** day, February included at 29, because no year is
available to decide leapness. `MM` is bounded too even though it authors no day: its implied day one is
still checked against a real month, which is what refuses month `00` and month `13`. -/
def parseYearlessComponents? (format : OmittingDateFormat) (text : String) :
    Option MonthDayValue :=
  let admit (month day : Nat) : Option MonthDayValue :=
    if 1 ≤ month && month ≤ 12 && 1 ≤ day &&
        day ≤ YearlessInterval.yearlessLastDay month then
      some { month, day }
    else none
  match format with
  | .month => (digitsOfWidth? text 2).bind fun month => admit month 1
  | .monthDay =>
      match text.splitOn "-" with
      | [monthText, dayText] => do
          let month ← digitsOfWidth? monthText 2
          let day ← digitsOfWidth? dayText 2
          admit month day
      | _ => none
  | .monthDayConcatenated =>
      if text.length == 4 then do
        let month ← digitsOfWidth? (text.take 2).toString 2
        let day ← digitsOfWidth? (text.drop 2).toString 2
        admit month day
      else none
  | .dayMonthConcatenated =>
      if text.length == 4 then do
        let day ← digitsOfWidth? (text.take 2).toString 2
        let month ← digitsOfWidth? (text.drop 2).toString 2
        admit month day
      else none
  | .year | .yearMonthDashed | .yearMonthConcatenated => none

end OmittingDateFormat

/-- Fail-closed reasons before a declaration can use the component-omitting Date classifier. -/
inductive CanonicalOmittingDateFieldError where
  | notDate (path : List String) (actual : FieldKind)
  | policyUnavailable (path : List String)
  /-- The declaration is a Date whose format is outside this seven-format component-omitting
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
  kindOwned : field.kind = .date
  formatOwned : OmittingDateFormat.ofSource? policy.format = some format

/-- Certify one component-omitting Date declaration without imposing an addressing shape. -/
def certifyOmittingDateInputField (declaration : FlatFieldDecl) :
    Except CanonicalOmittingDateFieldError CheckedOmittingDateInputField :=
  match hField : declaration.toTemporalField? with
  | none => .error (.notDate declaration.path declaration.policy.kind)
  | some field =>
      if hKind : field.kind = .date then
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
                kindOwned := hKind
                formatOwned := hFormat }
      else
        .error (.notDate declaration.path declaration.policy.kind)

/-- The value a component-omitting Date declaration stores. The two arms are not interchangeable: a
year-bearing value denotes an interval of concrete dates and resolves to endpoints, while a yearless one
denotes a calendar position with no year and therefore has no `FullDate` form at all. Keeping them
separate is what stops a consumer from silently completing a yearless value against some year. -/
inductive OmittingDateStoredValue where
  | yearBearing (value : PartiallyKnownDateValue)
  | yearless (value : MonthDayValue)
  deriving Repr, DecidableEq

/-- One classified component-omitting Date cell. -/
inductive OmittingDateInputCell where
  | presentEmpty
  | rejected (cause : BaseFormalCause)
  | admitted (value : OmittingDateStoredValue)
  deriving Repr, DecidableEq

/-- Classify stored text under a certified component-omitting declaration. Every failure is the one
measured cause; an unreal completion is a spelling question here exactly as it is for a complete date. -/
def CheckedOmittingDateInputField.classifyStored
    (checked : CheckedOmittingDateInputField) (text : String) :
    OmittingDateInputCell :=
  if text.isEmpty then
    .presentEmpty
  else if checked.format.carriesYear then
    match checked.format.parseYearComponents? text with
    | none => .rejected .dateFormat
    | some (year, none) =>
        match OmittedMonthDate.ofYear? year with
        | none => .rejected .dateFormat
        | some value => .admitted (.yearBearing (.omittedMonth value))
    | some (year, some month) =>
        match OmittedDayDate.ofYearMonth? year month with
        | none => .rejected .dateFormat
        | some value => .admitted (.yearBearing (.omittedDay value))
  else
    match checked.format.parseYearlessComponents? text with
    | none => .rejected .dateFormat
    | some value => .admitted (.yearless value)

end A12Kernel
