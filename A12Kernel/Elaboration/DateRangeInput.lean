import A12Kernel.Semantics.ModelZone
import A12Kernel.Semantics.Observation
import A12Kernel.Semantics.TemporalFormat

/-! # Checked DateRange stored-text ingestion

This capsule classifies stored DateRange text for the two exact declaration pairs already admitted by the bounded computation family. It retains present-empty placement, four distinct formal causes, decoded Gregorian components, model-zone midnight instants, and stored-calendar provenance. Wider `SimpleDateFormat` syntax, fragment ranges, other legal zones, JSON mapper behavior, and document traversal remain separate.
-/

namespace A12Kernel

/-- The bounded classifier cannot guess a value when the declaration or model-zone profile is outside its exact executable fragment. Local-midnight resolution failure remains separate from stored-value formal invalidity. -/
inductive DateRangeInputError where
  | unsupportedPolicy (format separator : String)
  | unsupportedZone (zoneId : String)
  | unresolvableEndpoint (parts : DateParts)
  deriving Repr, DecidableEq

namespace DateRangeFormat

/-- Decode one fixed-width ASCII component. -/
private def parseComponent? (width : Nat) (text : String) : Option Nat :=
  if text.length = width then parseAsciiNatural? text else none

/-- Decode one endpoint through the exact component order and calendar-reality check of the selected presentation. The universal floor is deliberately later because it has its own DateRange cause and precedence. -/
private def parseEndpoint? : DateRangeFormat → String → Option CivilDate
  | .isoSlash, text =>
      match text.splitOn "-" with
      | [yearText, monthText, dayText] => do
          let year ← parseComponent? 4 yearText
          let month ← parseComponent? 2 monthText
          let day ← parseComponent? 2 dayText
          CivilDate.ofYmd? year month day
      | _ => none
  | .dayMonthYearDash, text =>
      match text.splitOn "." with
      | [dayText, monthText, yearText] => do
          let day ← parseComponent? 2 dayText
          let month ← parseComponent? 2 monthText
          let year ← parseComponent? 4 yearText
          CivilDate.ofYmd? year month day
      | _ => none

/-- Parse and formally classify both endpoint labels before model-zone resolution. Separator absence wins first; malformed split shape or endpoint format/calendar reality comes second, endpoint order third, and the universal floor last. -/
private def parseCivilRange (format : DateRangeFormat) (text : String) :
    Except BaseFormalCause (CivilDate × CivilDate) := do
  let (startText, finishText) ← match text.splitOn format.separator with
    | [_] => throw .dateRangeSeparator
    | [startText, finishText] => pure (startText, finishText)
    | _ => throw .dateRangeFormat
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
    | .ok (start, finish) => do
        let startValue ← match DateRangeFormat.resolveEndpoint? profile start with
          | some value => pure value
          | none => throw (DateRangeInputError.unresolvableEndpoint start.parts)
        let finishValue ← match DateRangeFormat.resolveEndpoint? profile finish with
          | some value => pure value
          | none => throw (DateRangeInputError.unresolvableEndpoint finish.parts)
        pure (.parsed (.dateRange {
          start := startValue
          finish := finishValue
        }))

end A12Kernel
