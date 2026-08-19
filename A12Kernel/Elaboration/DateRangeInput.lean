import A12Kernel.Semantics.ModelZone
import A12Kernel.Semantics.Observation
import A12Kernel.Semantics.TemporalFormat
import A12Kernel.Elaboration.Flat.Types

/-! # Checked DateRange declaration and stored-text ingestion

This capsule classifies stored DateRange text for two exact full-Date pairs plus slash-separated `yyyy`, `yyyy-MM`, `MM`, and `MM-dd`. It retains present-empty placement and four distinct formal causes. Full-Date input, year-bearing fragments, and configured fragments resolve stored-Gregorian model-zone midnight instants; fragments without a Base Year retain only their ordered component identity. Wider `SimpleDateFormat` syntax, other legal zones, JSON mapper behavior, and document traversal remain separate.
-/

namespace A12Kernel

inductive CanonicalDateRangeFieldError where
  | notDateRange (path : List String) (actual : FieldKind)
  | unsupportedPolicy (path : List String) (format separator : String)
  | incoherentCore
  deriving Repr, DecidableEq

/-- One DateRange declaration with its field identity and coherent policy recovered once for every checked input profile. -/
structure CheckedDateRangeFieldPolicy where
  private mk ::
  declaration : FlatFieldDecl
  field : FlatDateRangeField
  policy : DateRangeDeclarationPolicy
  fieldOwned : declaration.toDateRangeField? = some field
  policyOwned : declaration.toDateRangeDeclarationPolicy? = some policy

/-- Recover the shared DateRange field and declaration policy before a consumer selects its supported input profile. -/
private def certifyDateRangeFieldPolicy (declaration : FlatFieldDecl) :
    Except CanonicalDateRangeFieldError CheckedDateRangeFieldPolicy :=
  match hField : declaration.toDateRangeField? with
  | none => .error (.notDateRange declaration.path
      declaration.policy.kind)
  | some field =>
      match hPolicy : declaration.toDateRangeDeclarationPolicy? with
      | none => .error .incoherentCore
      | some policy => .ok {
          declaration
          field
          policy
          fieldOwned := hField
          policyOwned := hPolicy }

/-- One DateRange declaration with its exact field identity, policy, and full-year parser selected once. -/
structure CheckedCanonicalDateRangeField extends CheckedDateRangeFieldPolicy where
  private mk ::
  format : DateRangeFormat
  formatOwned : DateRangeFormat.ofPolicy? policy = some format

/-- Certify one full-year declaration without imposing direct-versus-repeatable addressing; each consumer owns that separate shape gate. -/
def certifyCanonicalDateRangeField (declaration : FlatFieldDecl) :
    Except CanonicalDateRangeFieldError CheckedCanonicalDateRangeField := do
  let checked ← certifyDateRangeFieldPolicy declaration
  match hFormat : DateRangeFormat.ofPolicy? checked.policy with
  | none => throw (.unsupportedPolicy declaration.path
      checked.policy.format checked.policy.separator)
  | some format => pure { checked with format, formatOwned := hFormat }

/-- The bounded classifier cannot guess a value when the declaration or model-zone profile is outside its exact executable fragment. Local-midnight resolution failure remains separate from stored-value formal invalidity. -/
inductive DateRangeInputError where
  | unsupportedPolicy (format separator : String)
  | unsupportedZone (zoneId : String)
  | unresolvableEndpoint (parts : DateParts)
  deriving Repr, DecidableEq

/-- Stored DateRange presentations classified by the checked-document route and reused as checked target profiles. Parsing and exact-or-yearless cell construction remain input-owned. -/
inductive DateRangeInputFormat where
  | exact (format : DateRangeFormat)
  | yearFragment
  | yearMonthFragment
  | yearlessMonth
  | yearlessMonthDay
  deriving Repr, DecidableEq

namespace DateRangeInputFormat

/-- Recognize the two exact full-Date policies plus the measured slash-separated fragment policies. -/
def ofPolicy? (policy : DateRangeDeclarationPolicy) : Option DateRangeInputFormat :=
  match DateRangeFormat.ofPolicy? policy with
  | some format => some (.exact format)
  | none =>
      if policy.format == "yyyy" && policy.separator == "/" then
        some .yearFragment
      else if policy.format == "yyyy-MM" && policy.separator == "/" then
        some .yearMonthFragment
      else if policy.format == "MM" && policy.separator == "/" then
        some .yearlessMonth
      else if policy.format == "MM-dd" && policy.separator == "/" then
        some .yearlessMonthDay
      else
        none

end DateRangeInputFormat

/-- One DateRange declaration with any checked-document input profile selected once. -/
structure CheckedDateRangeInputField extends CheckedDateRangeFieldPolicy where
  private mk ::
  format : DateRangeInputFormat
  formatOwned : DateRangeInputFormat.ofPolicy? policy = some format

/-- Certify one of the six checked-document DateRange input profiles without imposing an addressing shape. -/
def certifyDateRangeInputField (declaration : FlatFieldDecl) :
    Except CanonicalDateRangeFieldError CheckedDateRangeInputField := do
  let checked ← certifyDateRangeFieldPolicy declaration
  match hFormat : DateRangeInputFormat.ofPolicy? checked.policy with
  | none => throw (.unsupportedPolicy declaration.path
      checked.policy.format checked.policy.separator)
  | some format => pure { checked with format, formatOwned := hFormat }

/-- Decode one fixed-width ASCII component. -/
private def parseDateRangeComponent? (width : Nat) (text : String) : Option Nat :=
  if text.length = width then parseAsciiNatural? text else none

/-- Split one range token while retaining the established missing-separator versus malformed-shape precedence. -/
private def splitDateRange (separator text : String) :
    Except BaseFormalCause (String × String) :=
  match text.splitOn separator with
  | [_] => throw .dateRangeSeparator
  | [startText, finishText] => pure (startText, finishText)
  | _ => throw .dateRangeFormat

private def requireDateRangeFormat : Option α → Except BaseFormalCause α
  | some value => pure value
  | none => throw .dateRangeFormat

namespace DateRangeFormat

/-- Decode one endpoint through the exact component order and calendar-reality check of the selected presentation. The universal floor is deliberately later because it has its own DateRange cause and precedence. -/
private def parseEndpoint? : DateRangeFormat → String → Option CivilDate
  | .isoSlash, text =>
      match text.splitOn "-" with
      | [yearText, monthText, dayText] => do
          let year ← parseDateRangeComponent? 4 yearText
          let month ← parseDateRangeComponent? 2 monthText
          let day ← parseDateRangeComponent? 2 dayText
          CivilDate.ofYmd? year month day
      | _ => none
  | .dayMonthYearDash, text =>
      match text.splitOn "." with
      | [dayText, monthText, yearText] => do
          let day ← parseDateRangeComponent? 2 dayText
          let month ← parseDateRangeComponent? 2 monthText
          let year ← parseDateRangeComponent? 4 yearText
          CivilDate.ofYmd? year month day
      | _ => none

/-- Parse and formally classify both endpoint labels before model-zone resolution. Separator absence wins first; malformed split shape or endpoint format/calendar reality comes second, endpoint order third, and the universal floor last. -/
private def parseCivilRange (format : DateRangeFormat) (text : String) :
    Except BaseFormalCause (CivilDate × CivilDate) := do
  let (startText, finishText) ← splitDateRange format.separator text
  let start ← match format.parseEndpoint? startText with
    | some start => pure start
    | none => throw .dateRangeFormat
  let finish ← match format.parseEndpoint? finishText with
    | some finish => pure finish
    | none => throw .dateRangeFormat
  if decide (finish.Before start) then
    throw .dateRangeInvalid
  else if decide (start.Before CivilDate.gregorianFloor) then
    throw .dateRangeTooEarly
  else
    pure (start, finish)

/-- Resolve one already real and floor-admitted endpoint at local midnight while retaining its decoded components and stored-Gregorian origin. -/
private def resolveEndpoint? (profile : ModelZone.ConcreteProfile)
    (date : CivilDate) : Option DateValue := do
  let full ← FullDate.ofCivil? date
  let localDateTime ← LocalDateTime.ofDateHms? full 0 0 0
  let instant ← profile.resolveLocal? localDateTime
  pure {
    instant
    parts := date.parts
    basis := .storedGregorian
  }

end DateRangeFormat

/-- Resolve an already admitted civil range to the shared exact stored carrier. -/
private def resolveCivilRange (profile : ModelZone.ConcreteProfile)
    (start finish : CivilDate) : Except DateRangeInputError RawCell := do
  let startValue ← match DateRangeFormat.resolveEndpoint? profile start with
    | some value => pure value
    | none => throw (.unresolvableEndpoint start.parts)
  let finishValue ← match DateRangeFormat.resolveEndpoint? profile finish with
    | some value => pure value
    | none => throw (.unresolvableEndpoint finish.parts)
  pure (.parsed (.dateRange (.exact { start := startValue, finish := finishValue })))

namespace DateRangeInputFormat

private def parseYear? (text : String) : Option Int := do
  let year ← parseDateRangeComponent? 4 text
  pure (Int.ofNat year)

private def parseMonth? (text : String) : Option Nat := do
  let month ← parseDateRangeComponent? 2 text
  if 1 ≤ month && month ≤ 12 then some month else none

/-- Parse a year-only range and apply the same separator, shape, order, and floor precedence as exact stored ranges. -/
private def parseYearRange (separator text : String) :
    Except BaseFormalCause (CivilDate × CivilDate) := do
  let (startText, finishText) ← splitDateRange separator text
  let startYear ← requireDateRangeFormat (parseYear? startText)
  let finishYear ← requireDateRangeFormat (parseYear? finishText)
  let start ← requireDateRangeFormat (CivilDate.ofYmd? startYear 1 1)
  let finish ← requireDateRangeFormat (CivilDate.ofYmd? finishYear 12 31)
  if decide (finish.Before start) then
    throw .dateRangeInvalid
  else if decide (start.Before CivilDate.gregorianFloor) then
    throw .dateRangeTooEarly
  else
    pure (start, finish)

private def parseYearMonth? (text : String) : Option (Int × Nat) :=
  match text.splitOn "-" with
  | [yearText, monthText] => do
      pure (← parseYear? yearText, ← parseMonth? monthText)
  | _ => none

/- Parse a year-month range and complete each endpoint according to its authored range position. -/
private def parseYearMonthRange (separator text : String) :
    Except BaseFormalCause (CivilDate × CivilDate) := do
  let (startText, finishText) ← splitDateRange separator text
  let (startYear, startMonth) ← requireDateRangeFormat
    (parseYearMonth? startText)
  let (finishYear, finishMonth) ← requireDateRangeFormat
    (parseYearMonth? finishText)
  let start ← requireDateRangeFormat
    (CivilDate.ofYmd? startYear startMonth 1)
  let finishDay ← requireDateRangeFormat
    (DateParts.daysInMonth? finishYear finishMonth)
  let finish ← requireDateRangeFormat
    (CivilDate.ofYmd? finishYear finishMonth finishDay)
  if decide (finish.Before start) then
    throw .dateRangeInvalid
  else if decide (start.Before CivilDate.gregorianFloor) then
    throw .dateRangeTooEarly
  else
    pure (start, finish)

private def parseMonthDay? (text : String) : Option MonthDayValue :=
  match text.splitOn "-" with
  | [monthText, dayText] => do
      let month ← parseDateRangeComponent? 2 monthText
      let day ← parseDateRangeComponent? 2 dayText
      let _ ← CivilDate.ofYmd? 2000 month day
      pure { month, day }
  | _ => none

private def monthDayBefore (left right : MonthDayValue) : Bool :=
  decide (left.month < right.month ∨
    left.month = right.month ∧ left.day < right.day)

/-- Parse one yearless range without manufacturing a calendar year. February 29 is admitted because it denotes a real month/day label in the Gregorian calendar. -/
private def parseYearlessRange (format : DateRangeInputFormat) (separator text : String) :
    Except BaseFormalCause DateRangeCellValue := do
  let (startText, finishText) ← splitDateRange separator text
  match format with
  | .yearFragment | .yearMonthFragment => throw .dateRangeFormat
  | .yearlessMonth =>
      let start ← requireDateRangeFormat (parseMonth? startText)
      let finish ← requireDateRangeFormat (parseMonth? finishText)
      if finish < start then throw .dateRangeInvalid
      else pure (.yearlessMonth start finish)
  | .yearlessMonthDay =>
      let start ← requireDateRangeFormat (parseMonthDay? startText)
      let finish ← requireDateRangeFormat (parseMonthDay? finishText)
      if monthDayBefore finish start then throw .dateRangeInvalid
      else pure (.yearlessMonthDay start finish)
  | .exact _ => throw .dateRangeFormat

private def completedCivilRange (year : Int) :
    DateRangeCellValue → Except BaseFormalCause (CivilDate × CivilDate)
  | .yearlessMonth start finish => do
      let startDate ← requireDateRangeFormat (CivilDate.ofYmd? year start 1)
      let lastDay ← requireDateRangeFormat (DateParts.daysInMonth? year finish)
      let finishDate ← requireDateRangeFormat
        (CivilDate.ofYmd? year finish lastDay)
      pure (startDate, finishDate)
  | .yearlessMonthDay start finish => do
      let startDate ← requireDateRangeFormat
        (CivilDate.ofYmd? year start.month start.day)
      let finishDate ← requireDateRangeFormat
        (CivilDate.ofYmd? year finish.month finish.day)
      pure (startDate, finishDate)
  | .exact _ => throw .dateRangeFormat

end DateRangeInputFormat

private def classifyExactFragmentRange (zoneId text : String)
    (parseRange : String → Except BaseFormalCause (CivilDate × CivilDate)) :
    Except DateRangeInputError RawCell := do
  let profile ← match ModelZone.ConcreteProfile.ofId? zoneId with
    | some profile => pure profile
    | none => throw (.unsupportedZone zoneId)
  if text.isEmpty then
    pure .presentEmpty
  else
    match parseRange text with
    | .error cause => pure (.rejected cause)
    | .ok (start, finish) => resolveCivilRange profile start finish

/-- Classify one physical DateRange token under a declaration and model zone. Formal text failures are successful classifications carrying their exact cause; only unsupported semantic capability returns `Except.error`. -/
def classifyStoredDateRange (zoneId : String)
    (policy : DateRangeDeclarationPolicy) (text : String) :
    Except DateRangeInputError RawCell := do
  let format ← match DateRangeFormat.ofPolicy? policy with
    | some format => pure format
    | none => throw (.unsupportedPolicy policy.format policy.separator)
  let profile ← match ModelZone.ConcreteProfile.ofId? zoneId with
    | some profile => pure profile
    | none => throw (.unsupportedZone zoneId)
  if text.isEmpty then
    pure .presentEmpty
  else
    match format.parseCivilRange text with
    | .error cause => pure (.rejected cause)
    | .ok (start, finish) => resolveCivilRange profile start finish

/-- Classify all currently checked stored DateRange profiles. Year-bearing fragments are always exact; Base Year resolves the two shorter fragments to the existing exact carrier, while its absence retains their component identity. -/
def classifyStoredDateRangeForModel (zoneId : String) (baseYear : Option Int)
    (policy : DateRangeDeclarationPolicy) (text : String) :
    Except DateRangeInputError RawCell := do
  let format ← match DateRangeInputFormat.ofPolicy? policy with
    | some format => pure format
    | none => throw (.unsupportedPolicy policy.format policy.separator)
  match format with
  | .exact _ => classifyStoredDateRange zoneId policy text
  | .yearFragment =>
      classifyExactFragmentRange zoneId text
        (DateRangeInputFormat.parseYearRange policy.separator)
  | .yearMonthFragment =>
      classifyExactFragmentRange zoneId text
        (DateRangeInputFormat.parseYearMonthRange policy.separator)
  | .yearlessMonth | .yearlessMonthDay =>
      if text.isEmpty then
        pure .presentEmpty
      else
        match format.parseYearlessRange policy.separator text with
        | .error cause => pure (.rejected cause)
        | .ok yearless =>
            match baseYear with
            | none => pure (.parsed (.dateRange yearless))
            | some year =>
                let profile ← match ModelZone.ConcreteProfile.ofId? zoneId with
                  | some profile => pure profile
                  | none => throw (.unsupportedZone zoneId)
                match DateRangeInputFormat.completedCivilRange year yearless with
                | .error cause => pure (.rejected cause)
                | .ok (start, finish) =>
                    if decide (start.Before CivilDate.gregorianFloor) then
                      pure (.rejected .dateRangeTooEarly)
                    else
                      resolveCivilRange profile start finish

end A12Kernel
