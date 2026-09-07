import A12Kernel.Elaboration.Flat.Model
import A12Kernel.Elaboration.StaticDiagnostic
import A12Kernel.Semantics.TemporalTarget

/-! # Checked temporal declaration policy

This capsule resolves one nonrepeatable temporal declaration against a validated flat model and retains the complete declaration-owned format policy plus the model-owned time zone. Its first consumers render computed targets and certify stored partial-Date `ValueAsDate`; the bounded target refinements render Time in its exact whole-second format without zone resolution, FULL Date values in two exact formats, and DateTime in the kernel's standard whole-second format against one concrete model-zone profile. Parsing stored text, delta classification, and application remain separate.
-/

namespace A12Kernel

/-- Fail-closed reasons before a temporal target can expose its declaration-owned policy. -/
inductive TemporalTargetElabError where
  | resolve (error : ResolveError)
  /-- The target's declared kind is not temporal at all. It carries that kind because a consuming
  carrier's Kernel class can depend on it: at a constant assignment a Boolean or Confirm target
  outranks the constant's own family, which no other information at this position recovers. -/
  | targetNotTemporal (target : FieldId) (actual : SurfaceScalarKind)
  | targetPolicyUnavailable (target : FieldId)
  | incoherentCore
  deriving Repr, DecidableEq

/-- One checked temporal declaration whose policy cannot be replaced by caller input. Existing field names remain target-oriented because computed targets were the first consumer. -/
structure CheckedTemporalTargetPolicy (model : FlatModel) where
  /-- The resolved declaration behind the target. It is retained rather than projected away because
  a consumer reading this field at a rule's row needs the declaration's repeatable scope, and
  recovering it by identifier lookup would need a total fallback for a declaration that cannot be
  missing. -/
  declaration : FlatFieldDecl
  target : FlatTemporalField
  policy : TemporalTargetPolicy
  modelWellFormed : model.validate.isOk = true
  targetOwned : declaration.toTemporalField? = some target
  policyAdmitted :
    policy.errorFor? target.kind target.components = none

namespace CheckedTemporalTargetPolicy

/-- Rendering observes the exact model time-zone identifier separately from the field's declaration-owned policy. -/
def timeZoneId (_ : CheckedTemporalTargetPolicy model) : String :=
  model.timeZoneId

end CheckedTemporalTargetPolicy

/-- Resolve one complete nonrepeatable temporal target policy. A temporal declaration without retained exact policy is explicit insufficient information. -/
def elaborateTemporalTargetPolicyIn
    (model : FlatModel) (scope : List RepeatableLevel) (targetField : FieldId) :
    Except TemporalTargetElabError (CheckedTemporalTargetPolicy model) := do
  match hModel : model.validate with
  | .error error => throw (.resolve error)
  | .ok () =>
      let resolved ← model.lookupUniqueId targetField |>.mapError .resolve
      let declaration ← resolved.requireRepetitionBoundBy scope
        |>.mapError .resolve
      match hTarget : declaration.toTemporalField? with
      | none =>
          throw (.targetNotTemporal targetField declaration.policy.kind.surfaceKind)
      | some target =>
          let policy ←
            match declaration.temporalTargetPolicy,
                declaration.toTemporalTargetPolicy? with
            | none, _ => throw (.targetPolicyUnavailable targetField)
            | some _, some policy => pure policy
            | some _, none => throw .incoherentCore
          if hPolicy : policy.errorFor? target.kind target.components = none then
            pure {
              declaration
              target
              policy
              modelWellFormed := by
                rw [hModel]
                rfl
              targetOwned := hTarget
              policyAdmitted := hPolicy }
          else
            throw .incoherentCore

/-- The scalar instance: a target read where the reading rule iterates no level. -/
def elaborateTemporalTargetPolicy
    (model : FlatModel) (targetField : FieldId) :
    Except TemporalTargetElabError (CheckedTemporalTargetPolicy model) :=
  elaborateTemporalTargetPolicyIn model [] targetField

/-- Static refusal before the bounded Time target can execute. -/
inductive TimeTargetElabError where
  | targetPolicy (error : TemporalTargetElabError)
  | targetKind (target : FieldId) (actual : TemporalKind)
  | components (target : FieldId) (actual : TemporalComponents)
  | unsupportedFormat (target : FieldId) (source : String)
  deriving Repr, DecidableEq

/-- One renderable complete-clock target, admitted by its declared **format** alone.

    This is the Kernel's own rule at this position: measured across all three temporal families, a computed target is gated by its declared format string and not by its declared kind, so a DateTime or a DATE declared with the degenerate `HH:mm:ss` format is a legal clock target ([checkpoint](../../docs/SOURCES.md#src-computed-temporal-target-reads-the-format-not-the-kind)). The runtime's 1970 transport date and the model zone do not enter clock rendering. -/
structure CheckedClockFormatTarget (model : FlatModel) where
  checked : CheckedTemporalTargetPolicy model
  format : TimeTargetFormat
  componentsComplete :
    checked.target.components = TemporalComponents.time
  formatMatches :
    TimeTargetFormat.ofSource? checked.policy.format = some format

/-- The clock target **narrowed to a TIME declaration**, which is strictly narrower than the Kernel.

    Its TIME-only narrowing is **retired**. It had been retained on carrier count — the cross-kind cell measured for the repeatable-constant carrier alone — and the carrier axis is now closed rather than enumerated: a computation *is* a comparison condition whose operand 1 is the target's own `FieldValue`, so the admission gate is `checkDateType` over the two operands' result formats, in which the target's declared kind is not a reachable input; and every computed temporal value, constant and constructed alike, reaches one `handleBerechnetenWert(VkDate, …)` overload from one emitted call site, which renders through the target's declared format, so the carrier is erased before the store ([checkpoint](../../docs/SOURCES.md#src-computed-target-gate-is-carrier-invariant)). A carrier cannot reach either decision, so no family owed a row of its own. -/
abbrev CheckedTimeTarget := @CheckedClockFormatTarget

namespace CheckedTemporalTargetPolicy

/-- Refine a checked temporal target to the renderable complete-clock subset without reading its declared kind. -/
def toClockFormatTarget
    (checked : CheckedTemporalTargetPolicy model) :
    Except TimeTargetElabError (CheckedClockFormatTarget model) :=
  if hComponents :
      checked.target.components = TemporalComponents.time then
    match hFormat : TimeTargetFormat.ofSource? checked.policy.format with
    | none =>
        throw (.unsupportedFormat checked.target.id checked.policy.format)
    | some format =>
        pure {
          checked
          format
          componentsComplete := hComponents
          formatMatches := hFormat }
  else
    throw (.components checked.target.id checked.target.components)

/-- Refine a checked temporal target to the complete Time subset. Alias of `toClockFormatTarget`,
which is now the whole gate. -/
abbrev toTimeTarget := @toClockFormatTarget

end CheckedTemporalTargetPolicy

/-- Resolve and refine one model-owned clock target by its declared format alone, with the repetition scope bound by the caller. This is the Kernel's own admission, and `elaborateTimeTargetIn` is now an alias of it rather than a narrowing. -/
def elaborateClockFormatTargetIn
    (model : FlatModel) (scope : List RepeatableLevel)
    (targetField : FieldId) :
    Except TimeTargetElabError (CheckedClockFormatTarget model) := do
  let checked ←
    elaborateTemporalTargetPolicyIn model scope targetField
      |>.mapError .targetPolicy
  checked.toClockFormatTarget

/-- Resolve and refine one model-owned nonrepeatable renderable complete-clock target, reading the
declared format and not the declared kind. -/
def elaborateClockFormatTarget
    (model : FlatModel) (targetField : FieldId) :
    Except TimeTargetElabError (CheckedClockFormatTarget model) :=
  elaborateClockFormatTargetIn model [] targetField

/-- Resolve and refine one model-owned complete Time target whose repetition scope is bound by the
caller. Alias of `elaborateClockFormatTargetIn`. -/
abbrev elaborateTimeTargetIn := @elaborateClockFormatTargetIn

/-- Resolve and refine one model-owned nonrepeatable complete Time target. Alias of
`elaborateClockFormatTarget`. -/
abbrev elaborateTimeTarget := @elaborateClockFormatTarget

/-- Static refusal before the bounded full-Date target can execute. -/
inductive FullDateTargetElabError where
  | targetPolicy (error : TemporalTargetElabError)
  | targetKind (target : FieldId) (actual : TemporalKind)
  | partialPrecision (target : FieldId) (actual : TemporalPartialMode)
  | unsupportedFormat (target : FieldId) (source : String)
  | unsupportedZone (zoneId : String)
  deriving Repr, DecidableEq

namespace FullDateTargetElabError

/-- Project only the measured partial computed-Date target rejection. Formats,
zones, kinds, and policy-resolution failures remain unmapped. -/
def partialTargetDiagnostic? :
    FullDateTargetElabError → Option KernelStaticDiagnostic
  | .partialPrecision _ .dayOptional => some .invalidDateType
  | .partialPrecision _ .monthOptional => some .invalidDateType
  | .partialPrecision _ .yearOptional => some .invalidDateType
  | _ => none

end FullDateTargetElabError

/-- One renderable complete-Date target, admitted by its declared **format** alone — the Kernel's own rule at this position, the same one `CheckedClockFormatTarget` carries for clocks. -/
structure CheckedDateFormatTarget (model : FlatModel) where
  checked : CheckedTemporalTargetPolicy model
  format : FullDateTargetFormat
  profile : ModelZone.ConcreteProfile
  precisionFull : checked.policy.partialMode = .full
  formatMatches :
    FullDateTargetFormat.ofSource? checked.policy.format = some format
  profileMatches :
    ModelZone.ConcreteProfile.ofId? checked.timeZoneId = some profile

/-- The complete-Date target. Its DATE-only narrowing is **retired** on the carrier-invariance
result its clock sibling records; this name is retained as an alias of the measured certificate so
seven consumers need no mechanical rename. -/
abbrev CheckedFullDateTarget := @CheckedDateFormatTarget

namespace CheckedTemporalTargetPolicy

/-- Refine a checked temporal target to the executable FULL Date subset. Partial precision, wider kinds, formats, and zones are explicit refusals. -/
def toDateFormatTarget
    (checked : CheckedTemporalTargetPolicy model) :
    Except FullDateTargetElabError (CheckedDateFormatTarget model) :=
  match hPrecision : checked.policy.partialMode with
  | .full =>
      match hFormat : FullDateTargetFormat.ofSource? checked.policy.format with
      | none =>
          throw (.unsupportedFormat checked.target.id checked.policy.format)
      | some format =>
          match hProfile :
              ModelZone.ConcreteProfile.ofId? checked.timeZoneId with
          | none => throw (.unsupportedZone checked.timeZoneId)
          | some profile =>
              pure {
                checked
                format
                profile
                precisionFull := hPrecision
                formatMatches := hFormat
                profileMatches := hProfile }
  | mode => throw (.partialPrecision checked.target.id mode)

/-- Refine a checked temporal target to the complete Date subset. Alias of `toDateFormatTarget`,
which is now the whole gate. -/
abbrev toFullDateTarget := @toDateFormatTarget

end CheckedTemporalTargetPolicy

/-- Resolve and refine one model-owned complete-Date target by its declared format alone, with the repetition scope bound by the caller. This is the Kernel's own admission, and `elaborateFullDateTargetIn` is now an alias of it rather than a narrowing. -/
def elaborateDateFormatTargetIn
    (model : FlatModel) (scope : List RepeatableLevel)
    (targetField : FieldId) :
    Except FullDateTargetElabError (CheckedDateFormatTarget model) := do
  let checked ←
    elaborateTemporalTargetPolicyIn model scope targetField
      |>.mapError .targetPolicy
  checked.toDateFormatTarget

/-- Resolve and refine one model-owned full-Date target whose repetition scope is bound by the
caller's reading environment. Alias of `elaborateDateFormatTargetIn`. -/
abbrev elaborateFullDateTargetIn := @elaborateDateFormatTargetIn

/-- Resolve and refine one model-owned nonrepeatable full-Date target. -/
def elaborateFullDateTarget
    (model : FlatModel) (targetField : FieldId) :
    Except FullDateTargetElabError (CheckedDateFormatTarget model) :=
  elaborateDateFormatTargetIn model [] targetField

/-- Runtime refusal when an exact result instant has no post-floor local Date in the selected concrete profile. -/
inductive FullDateTargetEvaluationFault where
  | localDateUnavailable (instant : Instant)
  deriving Repr, DecidableEq

namespace CheckedDateFormatTarget

/-- Render one real civil result before applying the target's ordered additional-check and universal-floor gates. The attempted text survives either rejection. -/
def evaluateCivil (target : CheckedDateFormatTarget model)
    (date : CivilDate) : FullDateTargetOutcome :=
  let stored := target.format.renderCivil date
  if target.checked.policy.youngerThan1900Check &&
      date.Before FullDate.year1900Start.civil then
    .errored stored .before1900
  else if date.Before CivilDate.gregorianFloor then
    .errored stored .beforeGregorianFloor
  else
    .accepted stored

/-- Render and basic-check one already-selected full-Date computation result without classifying a delta or mutating a document. -/
def evaluate
    (target : CheckedDateFormatTarget model) :
    TemporalComputationResult →
      Except FullDateTargetEvaluationFault FullDateTargetOutcome
  | .noValue => pure .noValue
  | .poison cause => pure (.poison cause)
  | .value instant =>
      match target.profile.localDate? instant with
      | none => throw (.localDateUnavailable instant)
      | some date =>
          pure (target.evaluateCivil date.civil)

end CheckedDateFormatTarget

/-- Static refusal before a component-omitting Date target can execute. -/
inductive OmittedComponentDateTargetElabError where
  | targetPolicy (error : TemporalTargetElabError)
  | targetKind (target : FieldId) (actual : TemporalKind)
  | unsupportedFormat (target : FieldId) (source : String)
  /-- A yearless declaration in a model that declares no Base Year. This is the Kernel's own refusal
  rather than a narrower local one: the same target admits the constant once a Base Year is
  declared. -/
  | yearlessWithoutBaseYear (target : FieldId) (source : String)
  deriving Repr, DecidableEq

/-- One checked Date target whose declared format names fewer components than a calendar date has.

    It constrains **only** the format, leaving `partialMode` and the declared kind free. The
    Kernel decides this shape from the declared format string alone: a `yyyy-MM` DATE and a `yyyy-MM`
    DATE_FRAGMENT accept the same constant and store the same text
    ([checkpoint](../../docs/SOURCES.md#src-component-omitting-date-formats)), so constraining the
    precision here would refuse a declaration the Kernel accepts — and the same holds of the kind,
    which the [carrier-invariance checkpoint](../../docs/SOURCES.md#src-computed-target-gate-is-carrier-invariant)
    closes for every carrier rather than one at a time. -/
structure CheckedOmittedComponentDateTarget (model : FlatModel) where
  checked : CheckedTemporalTargetPolicy model
  format : OmittingDateFormat
  formatMatches :
    OmittingDateFormat.ofSource? checked.policy.format = some format
  /-- A yearless target exists only in a model that declares a Base Year, so no consumer can build
  one the Kernel would refuse. "Yearless" is `carriesYear` failing — the Base Year requirement *is*
  year-absence, not a second classification of it. The Base Year is consumed **here and nowhere
  else**: it gates this certificate and reaches no part of the rendering.

  Read the direction precisely, because the converse is false. The Kernel's rule is symmetric over
  the **pair**: a Base Year is required exactly when the constant and the target disagree about
  carrying a year, so a *yearless* constant reaches a yearless target with no Base Year declared —
  measured, admitted, storing the month alone
  ([checkpoint](../../docs/sources/computation-placement-and-constant-probes.md#src-temporal-format-gate-not-component-sets)).
  This field states the requirement on the target alone, which is sound only because every constant
  reaching it is year-bearing by construction: `DateParts.year` is an `Int`, not an option, so the
  yearless literal is unrepresentable as a Date constant here. A carrier that gains a yearless
  constant must move the requirement onto the pair rather than reuse this field, which would refuse
  a declaration the Kernel accepts. -/
  baseYearWhenYearless :
    (!format.carriesYear && !model.hasBaseYear) = false

namespace CheckedTemporalTargetPolicy

/-- Refine a checked temporal target to the renderable component-omitting Date subset. The yearless
`MM` and `MM-dd` formats are inside it exactly when the model declares a Base Year, which is the
Kernel's own gate and the Base Year's only effect: the store that follows keeps no year either way
([checkpoint](../../docs/SOURCES.md#src-base-year-yearless-store)). -/
def toOmittedComponentDateTarget
    (checked : CheckedTemporalTargetPolicy model) :
    Except OmittedComponentDateTargetElabError
      (CheckedOmittedComponentDateTarget model) := do
  match hFormat :
      OmittingDateFormat.ofSource? checked.policy.format with
  | none =>
      throw (.unsupportedFormat checked.target.id checked.policy.format)
  | some format =>
      if hBase : (!format.carriesYear && !model.hasBaseYear) = false then
        pure { checked, format, formatMatches := hFormat,
               baseYearWhenYearless := hBase }
      else
        throw (.yearlessWithoutBaseYear checked.target.id checked.policy.format)

end CheckedTemporalTargetPolicy

/-- Resolve and refine one model-owned component-omitting Date target whose repetition scope is bound
by the caller. -/
def elaborateOmittedComponentDateTargetIn
    (model : FlatModel) (scope : List RepeatableLevel) (targetField : FieldId) :
    Except OmittedComponentDateTargetElabError
      (CheckedOmittedComponentDateTarget model) := do
  let checked ←
    elaborateTemporalTargetPolicyIn model scope targetField
      |>.mapError .targetPolicy
  checked.toOmittedComponentDateTarget

namespace CheckedOmittedComponentDateTarget

/-- Render one literal civil Date into this target's declared component subset, then apply the
declaration's **own** ordered additional-check and floor gates.

    Reusing those gates here is an assumption rather than a measurement: the component-omitting
    constant rows covered only targets with no additional check, so what a `yyyy` target declaring
    the pre-1900 check does with a 1899 constant is unobserved. The gates are declaration-owned and
    the flag sits on the policy whatever the format, which is why they are applied rather than
    dropped; the exclusion is recorded beside the carrier's coverage entry. -/
def evaluateCivil (target : CheckedOmittedComponentDateTarget model)
    (date : CivilDate) : FullDateTargetOutcome :=
  let stored := target.format.renderCivil date
  if target.checked.policy.youngerThan1900Check &&
      date.Before FullDate.year1900Start.civil then
    .errored stored .before1900
  else if date.Before CivilDate.gregorianFloor then
    .errored stored .beforeGregorianFloor
  else
    .accepted stored

end CheckedOmittedComponentDateTarget

/-- Static refusal before the bounded DateTime target can execute. -/
inductive DateTimeTargetElabError where
  | targetPolicy (error : TemporalTargetElabError)
  | targetKind (target : FieldId) (actual : TemporalKind)
  | components (target : FieldId) (actual : TemporalComponents)
  | unsupportedFormat (target : FieldId) (source : String)
  | unsupportedZone (zoneId : String)
  deriving Repr, DecidableEq

/-- One checked complete DateTime target with an executable whole-second format and concrete model-zone profile, admitted by its declared **format** alone.

    This completes the family rule the clock and full-Date certificates already state: a computed temporal target is gated by its declared format string and not by its declared kind. Both halves are measured for this carrier — admission across all three families, and the **store**, where a DATE declared with the DateTime format stores `2024-03-05T12:30:00` and a DATETIME declared `yyyy-MM-dd` stores `2024-03-05`, each against its same-kind control ([checkpoint](../../docs/SOURCES.md#src-datetime-carrier-stores-by-its-format)). Rendering here is format-driven by construction, so the store row confirms the construction rather than merely being consistent with it. -/
structure CheckedDateTimeFormatTarget (model : FlatModel) where
  checked : CheckedTemporalTargetPolicy model
  format : DateTimeTargetFormat
  profile : ModelZone.ConcreteProfile
  componentsComplete :
    checked.target.components = TemporalComponents.now
  formatMatches :
    DateTimeTargetFormat.ofSource? checked.policy.format = some format
  profileMatches :
    ModelZone.ConcreteProfile.ofId? checked.timeZoneId = some profile

/-- The complete DateTime target. Its DATETIME-only narrowing is **retired**: the shift,
first-filled, and addressed families that share this certificate never owed a cross-kind row of
their own, because neither the admission gate nor the store can read which carrier produced the
value — the reason `CheckedTimeTarget` records. Retained as an alias so nine consumers need no
mechanical rename. -/
abbrev CheckedDateTimeTarget := @CheckedDateTimeFormatTarget

namespace CheckedTemporalTargetPolicy

/-- Refine a checked temporal target to the renderable complete-DateTime subset without reading its declared kind. -/
def toDateTimeFormatTarget
    (checked : CheckedTemporalTargetPolicy model) :
    Except DateTimeTargetElabError (CheckedDateTimeFormatTarget model) :=
  if hComponents :
      checked.target.components = TemporalComponents.now then
    match hFormat :
        DateTimeTargetFormat.ofSource? checked.policy.format with
    | none =>
        throw (.unsupportedFormat checked.target.id checked.policy.format)
    | some format =>
        match hProfile :
            ModelZone.ConcreteProfile.ofId? checked.timeZoneId with
        | none => throw (.unsupportedZone checked.timeZoneId)
        | some profile =>
            pure {
              checked
              format
              profile
              componentsComplete := hComponents
              formatMatches := hFormat
              profileMatches := hProfile }
  else
    throw (.components checked.target.id checked.target.components)

/-- Refine a checked temporal target to the executable DateTime subset. Alias of
`toDateTimeFormatTarget`, which is now the whole gate. -/
abbrev toDateTimeTarget := @toDateTimeFormatTarget

end CheckedTemporalTargetPolicy

/-- Resolve and refine one model-owned complete DateTime target by its declared format alone, with the repetition scope bound by the caller. This is the Kernel's own admission, and `elaborateDateTimeTargetIn` is now an alias of it rather than a narrowing. -/
def elaborateDateTimeFormatTargetIn
    (model : FlatModel) (scope : List RepeatableLevel)
    (targetField : FieldId) :
    Except DateTimeTargetElabError (CheckedDateTimeFormatTarget model) := do
  let checked ←
    elaborateTemporalTargetPolicyIn model scope targetField
      |>.mapError .targetPolicy
  checked.toDateTimeFormatTarget

/-- Resolve and refine one model-owned complete DateTime target whose repetition scope is bound by
the caller's reading environment. Alias of `elaborateDateTimeFormatTargetIn`. -/
abbrev elaborateDateTimeTargetIn := @elaborateDateTimeFormatTargetIn

/-- Resolve and refine one model-owned nonrepeatable complete DateTime target. -/
def elaborateDateTimeTarget
    (model : FlatModel) (targetField : FieldId) :
    Except DateTimeTargetElabError (CheckedDateTimeFormatTarget model) :=
  elaborateDateTimeFormatTargetIn model [] targetField

/-- Runtime refusal when an exact result instant has no local DateTime label in the selected concrete profile. -/
inductive DateTimeTargetEvaluationFault where
  | localDateTimeUnavailable (instant : Instant)
  deriving Repr, DecidableEq

namespace CheckedDateTimeFormatTarget

/-- Render one already-selected DateTime computation result at the target's declared whole-second precision without classifying a delta or mutating a document.

    It sits on the format-keyed certificate so the narrowed one inherits it: the declared kind reaches no part of the rendering, which is what the cross-kind store rows measure. -/
def evaluate
    (target : CheckedDateTimeFormatTarget model) :
    TemporalComputationResult →
      Except DateTimeTargetEvaluationFault DateTimeTargetOutcome
  | .noValue => pure .noValue
  | .poison cause => pure (.poison cause)
  | .value instant =>
      match target.profile.localDateTime? instant with
      | none => throw (.localDateTimeUnavailable instant)
      | some dateTime =>
          pure (.accepted (target.format.render dateTime))

end CheckedDateTimeFormatTarget

end A12Kernel
