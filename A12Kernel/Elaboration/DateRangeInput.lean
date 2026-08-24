import A12Kernel.Elaboration.FullDateInput
import A12Kernel.Semantics.Observation
import A12Kernel.Semantics.TemporalFormat
import A12Kernel.Elaboration.Flat.Types

/-! # Checked DateRange declaration and stored-text ingestion

This capsule classifies stored DateRange text for two exact full-Date pairs plus slash-separated `yyyy`, `yyyy-MM`, `MM`, and `MM-dd`. It retains present-empty placement and four distinct formal causes. Full-Date input, year-bearing fragments, and configured fragments resolve stored-Gregorian model-zone midnight instants; fragments without a Base Year retain their component identity, with a declared year interpretation admitting wrapping pairs. Wider `SimpleDateFormat` syntax, other legal zones, JSON mapper behavior, and document traversal remain separate.
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

/-- Stored DateRange presentations classified by the checked-document route and reused as checked target profiles. Parsing and exact-or-yearless cell construction remain input-owned. A constructor names one stored presentation rather than one component shape: two constructors retain a month pair and two retain a month/day pair, because the declared separator and endpoint spelling change the stored text without changing the retained components. -/
inductive DateRangeInputFormat where
  | exact (format : DateRangeFormat)
  | yearFragment
  | yearMonthFragment
  | yearlessMonth
  | yearlessMonthDay
  /-- `MM` with the declared empty separator, whose stored token is the two months concatenated. -/
  | yearlessMonthConcatenated
  /-- `dd.MM` with dash, whose endpoints spell day before month. -/
  | yearlessDayMonthDotted
  deriving Repr, DecidableEq

namespace DateRangeInputFormat

/-- Recognize every admitted declaration pair: the two exact full-Date policies, the slash-separated fragment policies, and the two lexical variants that share a fragment's components under a different stored spelling. -/
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
      else if policy.format == "MM" && policy.separator == "" then
        some .yearlessMonthConcatenated
      else if policy.format == "dd.MM" && policy.separator == "-" then
        some .yearlessDayMonthDotted
      else
        none

/-- Whether the declared endpoints carry a year of their own. This is the declaration's own
component set, independent of any model: a yearless profile gains a year only from a configured
Base Year, and the consuming operator decides whether that completion counts. -/
def includesYear : DateRangeInputFormat → Bool
  | .exact _ | .yearFragment | .yearMonthFragment => true
  | .yearlessMonth | .yearlessMonthDay | .yearlessMonthConcatenated
  | .yearlessDayMonthDotted => false

/-- The date components one stored DateRange profile exposes. A DateRange declaration carries no wall-time component, so only the three calendar halves vary, and two profiles expose the same set exactly when their lexical spellings retain the same components: both full-Date spellings, both month-only spellings, and both day-and-month spellings agree. -/
def components : DateRangeInputFormat → TemporalComponents
  | .exact _ => TemporalComponents.fullDate
  | .yearFragment =>
      { TemporalComponents.fullDate with month := false, day := false }
  | .yearMonthFragment => { TemporalComponents.fullDate with day := false }
  | .yearlessMonth | .yearlessMonthConcatenated =>
      { TemporalComponents.fullDate with year := false, day := false }
  | .yearlessMonthDay | .yearlessDayMonthDotted =>
      { TemporalComponents.fullDate with year := false }

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

/-- Halve one stored token whose declaration carries no separator. A token cannot fail the separator-presence check under an empty separator, so an odd length is a shape failure rather than a missing separator. -/
private def halveDateRange (text : String) :
    Except BaseFormalCause (String × String) :=
  if text.length % 2 == 0 then
    pure ((text.take (text.length / 2)).toString,
      (text.drop (text.length / 2)).toString)
  else
    throw .dateRangeFormat

namespace DateRangeFormat

/-- Reuse the scalar full-Date parser selected by each exact DateRange presentation. -/
private def endpointFormat : DateRangeFormat → FullDateTargetFormat
  | .isoSlash => .yearMonthDayDashes
  | .dayMonthYearDash => .dayMonthYearDots

/-- Decode one endpoint through the exact component order and default-cutover calendar-reality check of the selected presentation. The universal floor is deliberately later because it has its own DateRange cause and precedence. -/
private def parseEndpoint? : DateRangeFormat → String → Option DateParts
  | format, text => format.endpointFormat.parseLegacyParts? text

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
  else if decide (start.Before CivilDate.gregorianFloor.parts) then
    throw .dateRangeTooEarly
  else do
    let startDate ← requireDateRangeFormat (CivilDate.ofParts? start)
    let finishDate ← requireDateRangeFormat (CivilDate.ofParts? finish)
    pure (startDate, finishDate)

end DateRangeFormat

/-- Resolve an already admitted civil range to the shared exact stored carrier. -/
private def resolveCivilRange (profile : ModelZone.ConcreteProfile)
    (start finish : CivilDate) : Except DateRangeInputError RawCell := do
  let startValue ← match profile.resolveStoredDate? start with
    | some value => pure value
    | none => throw (.unresolvableEndpoint start.parts)
  let finishValue ← match profile.resolveStoredDate? finish with
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

/-- Decode one dotted endpoint whose components spell day before month. The leap probe year is the same one the slash-separated profile uses, so February 29 stays a real month/day label. -/
private def parseDayMonth? (text : String) : Option MonthDayValue :=
  match text.splitOn "." with
  | [dayText, monthText] => do
      let day ← parseDateRangeComponent? 2 dayText
      let month ← parseDateRangeComponent? 2 monthText
      let _ ← CivilDate.ofYmd? 2000 month day
      pure { month, day }
  | _ => none

/-- Decode one yearless range's endpoint labels without manufacturing a calendar year and without deciding their order. February 29 is admitted because it denotes a real month/day label in the Gregorian calendar. The stored presentation selects the split and the endpoint spelling; the retained component pair is shared, so the order rule can be applied once by the caller that knows whether a wrap is legal. -/
private def parseYearlessEndpoints (format : DateRangeInputFormat) (separator text : String) :
    Except BaseFormalCause DateRangeCellValue := do
  let (startText, finishText) ←
    match format with
    | .yearlessMonthConcatenated => halveDateRange text
    | _ => splitDateRange separator text
  match format with
  | .yearFragment | .yearMonthFragment => throw .dateRangeFormat
  | .yearlessMonth | .yearlessMonthConcatenated =>
      let start ← requireDateRangeFormat (parseMonth? startText)
      let finish ← requireDateRangeFormat (parseMonth? finishText)
      pure (.yearlessMonth start finish)
  | .yearlessMonthDay =>
      let start ← requireDateRangeFormat (parseMonthDay? startText)
      let finish ← requireDateRangeFormat (parseMonthDay? finishText)
      pure (.yearlessMonthDay start finish)
  | .yearlessDayMonthDotted =>
      let start ← requireDateRangeFormat (parseDayMonth? startText)
      let finish ← requireDateRangeFormat (parseDayMonth? finishText)
      pure (.yearlessMonthDay start finish)
  | .exact _ => throw .dateRangeFormat

/-- Complete a decoded yearless pair into two civil dates, one placed in each supplied calendar year. An ordered range receives the same year twice; a wrapping range receives the adjacent pair its declared interpretation selects. The month-only finish takes the last day of its own placed year, so a February finish follows that year's leap rule rather than the start year's. -/
private def completedCivilRange (startYear finishYear : Int) :
    DateRangeCellValue → Except BaseFormalCause (CivilDate × CivilDate)
  | .yearlessMonth start finish => do
      let startDate ← requireDateRangeFormat (CivilDate.ofYmd? startYear start 1)
      let lastDay ← requireDateRangeFormat (DateParts.daysInMonth? finishYear finish)
      let finishDate ← requireDateRangeFormat
        (CivilDate.ofYmd? finishYear finish lastDay)
      pure (startDate, finishDate)
  | .yearlessMonthDay start finish => do
      let startDate ← requireDateRangeFormat
        (CivilDate.ofYmd? startYear start.month start.day)
      let finishDate ← requireDateRangeFormat
        (CivilDate.ofYmd? finishYear finish.month finish.day)
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

/-- Select each endpoint's calendar year under a declared Base Year. An ordered pair takes that year twice, so every interpretation agrees on it; a wrapping pair takes the adjacent pair its interpretation selects, and has no placement at all without one. -/
def completionYears (interpretation : Option DateRangeYearInterpretation)
    (baseYear : Int) (yearless : DateRangeCellValue) : Option (Int × Int) :=
  if yearless.wrapsYearBoundary then
    interpretation.map (·.wrappingYears baseYear)
  else
    some (baseYear, baseYear)

/-- Place a decoded yearless pair under the model's Base Year and declared year interpretation.

Without a Base Year there is no anchor year to complete against, so the pair keeps its component identity. A wrapping pair is admitted only when the declaration supplies an interpretation, even though `FROM` and `TO` cannot choose concrete years on this route. Under a Base Year the placement comes from `completionYears`, and an unplaceable wrapping pair is `dateRangeInvalid`. The model zone is consulted only where a completion actually happens, so an unsupported zone is not refused on the uncompleted route.
-/
def resolveYearlessForModel (zoneId : String) (baseYear : Option Int)
    (interpretation : Option DateRangeYearInterpretation)
    (yearless : DateRangeCellValue) : Except DateRangeInputError RawCell :=
  match baseYear with
  | none =>
      if yearless.wrapsYearBoundary then
        match interpretation with
        | none => .ok (.rejected .dateRangeInvalid)
        | some _ => .ok (.parsed (.dateRange yearless))
      else
        .ok (.parsed (.dateRange yearless))
  | some year =>
      match completionYears interpretation year yearless with
      | none => .ok (.rejected .dateRangeInvalid)
      | some (startYear, finishYear) => do
          let profile ← match ModelZone.ConcreteProfile.ofId? zoneId with
            | some profile => pure profile
            | none => throw (.unsupportedZone zoneId)
          match DateRangeInputFormat.completedCivilRange startYear finishYear yearless with
          | .error cause => pure (.rejected cause)
          | .ok (start, finish) =>
              if decide (start.Before CivilDate.gregorianFloor) then
                pure (.rejected .dateRangeTooEarly)
              else
                resolveCivilRange profile start finish

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
  | .yearlessMonth | .yearlessMonthDay | .yearlessMonthConcatenated
  | .yearlessDayMonthDotted =>
      if text.isEmpty then
        pure .presentEmpty
      else
        match format.parseYearlessEndpoints policy.separator text with
        | .error cause => pure (.rejected cause)
        | .ok yearless =>
            resolveYearlessForModel zoneId baseYear policy.interpretationOfYear yearless

end A12Kernel
