import A12Kernel.Semantics.FullDateInputFormat
import A12Kernel.Elaboration.Flat.Types
import A12Kernel.Semantics.Observation
import A12Kernel.Semantics.ConstructedDateShift
import A12Kernel.Semantics.TemporalTarget

/-! # Checked full-Date stored input
This capsule classifies full-precision stored Date text for the three measured complete formats. It preserves declared-format parsing, calendar reality, the universal Gregorian floor, the optional pre-1900 check, model-zone midnight identity, and stored-Gregorian provenance before the immutable checked document exposes a value. Partial precision, computed-target policy, wider format syntax, and other model zones remain separate. -/

namespace A12Kernel

/-- Fail-closed reasons before a declaration can use the bounded full-Date input classifier. -/
inductive CanonicalFullDateFieldError where
  | notFullDate (path : List String) (actual : FieldKind)
  | policyUnavailable (path : List String)
  | unsupportedPolicy (path : List String) (format : String)
      (partialMode : TemporalPartialMode)
  deriving Repr, DecidableEq

/-- One full-Date declaration whose kind, complete component shape, policy, precision, and input format are model-owned. Addressing remains consumer-owned. -/
structure CheckedFullDateInputField where
  private mk ::
  declaration : FlatFieldDecl
  field : FlatTemporalField
  policy : TemporalTargetPolicy
  format : FullDateInputFormat
  fieldOwned : declaration.toTemporalField? = some field
  policyOwned : declaration.toTemporalTargetPolicy? = some policy
  componentsOwned : field.components = TemporalComponents.fullDate
  precisionOwned : policy.partialMode = .full
  formatOwned : FullDateInputFormat.ofSource? policy.format = some format

/-- Certify one bounded full-Date input declaration without imposing a direct or repeatable addressing shape. -/
def certifyFullDateInputField (declaration : FlatFieldDecl) :
    Except CanonicalFullDateFieldError CheckedFullDateInputField :=
  match hField : declaration.toTemporalField? with
  | none => .error (.notFullDate declaration.path declaration.policy.kind)
  | some field =>
      if hComponents : field.components = TemporalComponents.fullDate then
        match hPolicy : declaration.toTemporalTargetPolicy? with
        | none => .error (.policyUnavailable declaration.path)
        | some policy =>
            if hPrecision : policy.partialMode = .full then
              match hFormat : FullDateInputFormat.ofSource? policy.format with
              | none => .error (.unsupportedPolicy declaration.path
                  policy.format policy.partialMode)
              | some format => .ok {
                  declaration
                  field
                  policy
                  format
                  fieldOwned := hField
                  policyOwned := hPolicy
                  componentsOwned := hComponents
                  precisionOwned := hPrecision
                  formatOwned := hFormat }
            else
              .error (.unsupportedPolicy declaration.path
                policy.format policy.partialMode)
      else
        .error (.notFullDate declaration.path declaration.policy.kind)

/-- The bounded classifier cannot resolve a value outside its exact model-zone profile. A locally impossible midnight remains distinct from a formal text failure. -/
inductive FullDateInputError where
  | unsupportedZone (zoneId : String)
  | unresolvableDate (parts : DateParts)
  deriving Repr, DecidableEq

/-- Decode one fixed-width ASCII full Date under the default-cutover legacy calendar used by non-lenient stored-value parsing. -/
def FullDateInputFormat.parseLegacyParts? (format : FullDateInputFormat)
    (text : String) : Option DateParts := do
  let parts ← format.parseComponents? text
  if DateParts.LegacyHybrid.isReal parts then some parts else none

/-- Decode a computed-target format through the shared stored-input parser. -/
def FullDateTargetFormat.parseLegacyParts? (format : FullDateTargetFormat)
    (text : String) : Option DateParts :=
  (FullDateInputFormat.ofTarget format).parseLegacyParts? text

/-- Resolve one admitted stored Date label at local midnight while retaining its decoded components and stored-Gregorian origin. -/
def ModelZone.ConcreteProfile.resolveStoredDate? (profile : ModelZone.ConcreteProfile)
    (date : CivilDate) : Option DateValue := do
  let full ← FullDate.ofCivil? date
  let localDateTime ← LocalDateTime.ofDateHms? full 0 0 0
  let instant ← profile.resolveLocal? localDateTime
  pure { instant, parts := date.parts, basis := .storedGregorian }

/-- Classify stored full-Date text under its certified declaration and one bounded model-zone profile. Formal text failures are successful classifications; only unsupported or unresolvable model context returns an error. -/
def CheckedFullDateInputField.classifyStoredForModel
    (checked : CheckedFullDateInputField)
    (zoneId text : String) : Except FullDateInputError RawCell := do
  let profile ← match ModelZone.ConcreteProfile.ofId? zoneId with
    | some profile => pure profile
    | none => throw (.unsupportedZone zoneId)
  if text.isEmpty then
    pure .presentEmpty
  else
    match checked.format.parseLegacyParts? text with
    | none => pure (.rejected .dateFormat)
    | some parts =>
        if decide (parts.Before CivilDate.gregorianFloor.parts) ||
            (checked.policy.youngerThan1900Check &&
              decide (parts.Before FullDate.year1900Start.civil.parts)) then
          pure (.rejected .dateInvalid)
        else
          match CivilDate.ofParts? parts with
          | none => pure (.rejected .dateFormat)
          | some date =>
              match profile.resolveStoredDate? date with
              | none => throw (.unresolvableDate parts)
              | some value => pure (.parsed (.temporal (.date value)))

end A12Kernel
