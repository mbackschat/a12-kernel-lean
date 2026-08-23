import A12Kernel.Elaboration.PartialDateInput

/-! # Checked component-omitting Date input

A DATE declaration may carry a format that **omits components**: measured at kernel 30.8.1, `yyyy`,
`yyyy-MM`, `yyyyMM`, `MM`, and `MM-dd` are all legal DATE formats alongside the two complete ones. Such a
declaration's stored text is shorter than a complete date and its value denotes an interval rather than a
day.

This capsule owns the three that carry a year, because their value is already a
`PartiallyKnownDateValue`: a year alone is the omitted-month shape and a year-month is the omitted-day
shape. Nothing new enters the value domain, so every existing `ValueAsDate` consumer reads these values
through the endpoint resolver it already has.

**One cause, and no position-in-time cause at all.** Measured, every spelling failure reports
`dateFormat`: a wrong component width, a text carrying components the format omits, and an out-of-range
month alike. `dateInvalid` cannot arise, because these formats carry no complete date whose position
could fall below the Gregorian floor — which is the whole structural difference from complete-format
input, where two causes are needed.

**The separator is exact in both directions.** `yyyy-MM` refuses `202006` and `yyyyMM` refuses
`2020-06`, so the two spellings are separate formats rather than one lenient parser.

`MM` and `MM-dd` stay outside. Their canonical text is measured accepted, and `MM-dd` admits `02-29`
while refusing `02-30`, so a yearless month-day is leap-capable. Representing them needs a yearless value
shape this project holds only inside the DateRange family; joining those domains is its own unit. -/

namespace A12Kernel

/-- A DATE declaration format that omits components and carries a year. -/
inductive OmittingDateFormat where
  /-- `yyyy` — the value is a whole calendar year. -/
  | year
  /-- `yyyy-MM` — the value is a whole calendar month. -/
  | yearMonthDashed
  /-- `yyyyMM` — the same value under a separator-free spelling, refused by the dashed format. -/
  | yearMonthConcatenated
  deriving Repr, DecidableEq

namespace OmittingDateFormat

/-- Admit only the three measured component-omitting formats that carry a year. The two complete formats
belong to the full-Date classifier and the two yearless ones have no value shape here. -/
def ofSource? : String → Option OmittingDateFormat
  | "yyyy" => some .year
  | "yyyy-MM" => some .yearMonthDashed
  | "yyyyMM" => some .yearMonthConcatenated
  | _ => none

/-- Split stored text into its exact fixed-width components. Widths are fixed and the separator is
literal, so a short year, an extra component, and a wrong separator all fail here alike. -/
def parseComponents? (format : OmittingDateFormat) (text : String) :
    Option (Int × Option Nat) :=
  let digits (part : String) (width : Nat) : Option Nat :=
    if part.length == width && part.all Char.isDigit then part.toNat? else none
  match format with
  | .year => (digits text 4).map fun year => ((year : Int), none)
  | .yearMonthDashed =>
      match text.splitOn "-" with
      | [yearText, monthText] => do
          let year ← digits yearText 4
          let month ← digits monthText 2
          pure ((year : Int), some month)
      | _ => none
  | .yearMonthConcatenated =>
      if text.length == 6 then do
        let year ← digits (text.take 4).toString 4
        let month ← digits (text.drop 4).toString 2
        pure ((year : Int), some month)
      else none

end OmittingDateFormat

/-- Fail-closed reasons before a declaration can use the component-omitting Date classifier. -/
inductive CanonicalOmittingDateFieldError where
  | notDate (path : List String) (actual : FieldKind)
  | policyUnavailable (path : List String)
  /-- The declaration is a Date whose format is complete or yearless rather than year-bearing and
  component-omitting. Reachable rather than defensive: all five are legal declarations. -/
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

/-- One classified component-omitting Date cell. The admitted value is an ordinary partially known Date,
so no consumer needs a second value domain. -/
inductive OmittingDateInputCell where
  | presentEmpty
  | rejected (cause : BaseFormalCause)
  | admitted (value : PartiallyKnownDateValue)
  deriving Repr, DecidableEq

/-- Classify stored text under a certified component-omitting declaration. Every failure is the one
measured cause; an unreal completion is a spelling question here exactly as it is for a complete date. -/
def CheckedOmittingDateInputField.classifyStored
    (checked : CheckedOmittingDateInputField) (text : String) :
    OmittingDateInputCell :=
  if text.isEmpty then
    .presentEmpty
  else
    match checked.format.parseComponents? text with
    | none => .rejected .dateFormat
    | some (year, none) =>
        match OmittedMonthDate.ofYear? year with
        | none => .rejected .dateFormat
        | some value => .admitted (.omittedMonth value)
    | some (year, some month) =>
        match OmittedDayDate.ofYearMonth? year month with
        | none => .rejected .dateFormat
        | some value => .admitted (.omittedDay value)

end A12Kernel
