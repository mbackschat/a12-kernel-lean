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
  | targetNotTemporal (target : FieldId)
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
      | none => throw (.targetNotTemporal targetField)
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

/-- One checked complete Time target. The runtime's 1970 transport date and model zone do not enter clock rendering. -/
structure CheckedTimeTarget (model : FlatModel) where
  checked : CheckedTemporalTargetPolicy model
  format : TimeTargetFormat
  targetIsTime : checked.target.kind = .time
  componentsComplete :
    checked.target.components = TemporalComponents.time
  formatMatches :
    TimeTargetFormat.ofSource? checked.policy.format = some format

namespace CheckedTemporalTargetPolicy

/-- Refine a checked temporal target to the exact complete Time subset. -/
def toTimeTarget
    (checked : CheckedTemporalTargetPolicy model) :
    Except TimeTargetElabError (CheckedTimeTarget model) := do
  if hKind : checked.target.kind = .time then
    if hComponents :
        checked.target.components = TemporalComponents.time then
      match hFormat : TimeTargetFormat.ofSource? checked.policy.format with
      | none =>
          throw (.unsupportedFormat checked.target.id checked.policy.format)
      | some format =>
          pure {
            checked
            format
            targetIsTime := hKind
            componentsComplete := hComponents
            formatMatches := hFormat }
    else
      throw (.components checked.target.id checked.target.components)
  else
    throw (.targetKind checked.target.id checked.target.kind)

end CheckedTemporalTargetPolicy

/-- Resolve and refine one model-owned complete Time target whose repetition scope is bound by the caller. -/
def elaborateTimeTargetIn
    (model : FlatModel) (scope : List RepeatableLevel)
    (targetField : FieldId) :
    Except TimeTargetElabError (CheckedTimeTarget model) := do
  let checked ←
    elaborateTemporalTargetPolicyIn model scope targetField
      |>.mapError .targetPolicy
  checked.toTimeTarget

/-- Resolve and refine one model-owned nonrepeatable complete Time target. -/
def elaborateTimeTarget
    (model : FlatModel) (targetField : FieldId) :
    Except TimeTargetElabError (CheckedTimeTarget model) :=
  elaborateTimeTargetIn model [] targetField

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

/-- One checked FULL Date target with an executable format and concrete model-zone profile. Partial precision is a stored-input capability rejected by computation authoring. -/
structure CheckedFullDateTarget (model : FlatModel) where
  checked : CheckedTemporalTargetPolicy model
  format : FullDateTargetFormat
  profile : ModelZone.ConcreteProfile
  targetIsDate : checked.target.kind = .date
  precisionFull : checked.policy.partialMode = .full
  formatMatches :
    FullDateTargetFormat.ofSource? checked.policy.format = some format
  profileMatches :
    ModelZone.ConcreteProfile.ofId? checked.timeZoneId = some profile

namespace CheckedTemporalTargetPolicy

/-- Refine a checked temporal target to the executable FULL Date subset. Partial precision, wider kinds, formats, and zones are explicit refusals. -/
def toFullDateTarget
    (checked : CheckedTemporalTargetPolicy model) :
    Except FullDateTargetElabError (CheckedFullDateTarget model) := do
  if hDate : checked.target.kind = .date then
    match hPrecision : checked.policy.partialMode with
    | .full =>
        match hFormat :
            FullDateTargetFormat.ofSource? checked.policy.format with
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
                  targetIsDate := hDate
                  precisionFull := hPrecision
                  formatMatches := hFormat
                  profileMatches := hProfile }
    | mode =>
        throw (.partialPrecision checked.target.id mode)
  else
    throw (.targetKind checked.target.id checked.target.kind)

end CheckedTemporalTargetPolicy

/-- Resolve and refine one model-owned full-Date target whose repetition scope is bound by the caller's reading environment. -/
def elaborateFullDateTargetIn
    (model : FlatModel) (scope : List RepeatableLevel)
    (targetField : FieldId) :
    Except FullDateTargetElabError (CheckedFullDateTarget model) := do
  let checked ←
    elaborateTemporalTargetPolicyIn model scope targetField
      |>.mapError .targetPolicy
  checked.toFullDateTarget

/-- Resolve and refine one model-owned nonrepeatable full-Date target. -/
def elaborateFullDateTarget
    (model : FlatModel) (targetField : FieldId) :
    Except FullDateTargetElabError (CheckedFullDateTarget model) :=
  elaborateFullDateTargetIn model [] targetField

/-- Runtime refusal when an exact result instant has no post-floor local Date in the selected concrete profile. -/
inductive FullDateTargetEvaluationFault where
  | localDateUnavailable (instant : Instant)
  deriving Repr, DecidableEq

namespace CheckedFullDateTarget

/-- Render one real civil result before applying the target's ordered additional-check and universal-floor gates. The attempted text survives either rejection. -/
def evaluateCivil (target : CheckedFullDateTarget model)
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
    (target : CheckedFullDateTarget model) :
    TemporalComputationResult →
      Except FullDateTargetEvaluationFault FullDateTargetOutcome
  | .noValue => pure .noValue
  | .poison cause => pure (.poison cause)
  | .value instant =>
      match target.profile.localDate? instant with
      | none => throw (.localDateUnavailable instant)
      | some date =>
          pure (target.evaluateCivil date.civil)

end CheckedFullDateTarget

/-- Static refusal before a component-omitting Date target can execute. -/
inductive OmittedComponentDateTargetElabError where
  | targetPolicy (error : TemporalTargetElabError)
  | targetKind (target : FieldId) (actual : TemporalKind)
  | unsupportedFormat (target : FieldId) (source : String)
  deriving Repr, DecidableEq

/-- One checked Date target whose declared format names fewer components than a calendar date has.

    It deliberately constrains **only** the kind and the format, leaving `partialMode` free. The
    Kernel decides this shape from the declared format string alone: a `yyyy-MM` DATE and a `yyyy-MM`
    DATE_FRAGMENT accept the same constant and store the same text
    ([checkpoint](../../docs/SOURCES.md#src-component-omitting-date-formats)), so constraining the
    precision here would refuse a declaration the Kernel accepts. -/
structure CheckedOmittedComponentDateTarget (model : FlatModel) where
  checked : CheckedTemporalTargetPolicy model
  format : OmittedComponentDateFormat
  targetIsDate : checked.target.kind = .date
  formatMatches :
    OmittedComponentDateFormat.ofSource? checked.policy.format = some format

namespace CheckedTemporalTargetPolicy

/-- Refine a checked temporal target to the renderable component-omitting Date subset. The yearless
`MM` and `MM-dd` formats are outside it: the Kernel refuses a Date constant for them unless the model
declares a Base Year, and what such a target then stores is unmeasured. -/
def toOmittedComponentDateTarget
    (checked : CheckedTemporalTargetPolicy model) :
    Except OmittedComponentDateTargetElabError
      (CheckedOmittedComponentDateTarget model) := do
  if hDate : checked.target.kind = .date then
    match hFormat :
        OmittedComponentDateFormat.ofSource? checked.policy.format with
    | none =>
        throw (.unsupportedFormat checked.target.id checked.policy.format)
    | some format =>
        pure { checked, format, targetIsDate := hDate, formatMatches := hFormat }
  else
    throw (.targetKind checked.target.id checked.target.kind)

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

    Reusing those gates here is an assumption rather than a measurement: the constant rows covered
    only targets with no additional check, so what a `yyyy` target declaring the pre-1900 check does
    with a 1899 constant is unobserved. The gates are declaration-owned and the flag sits on the
    policy whatever the format, which is why they are applied rather than dropped; the exclusion is
    recorded beside the carrier's coverage entry so the assumption is visible rather than silent. -/
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

/-- One checked complete DateTime target with an executable whole-second format and concrete model-zone profile. -/
structure CheckedDateTimeTarget (model : FlatModel) where
  checked : CheckedTemporalTargetPolicy model
  format : DateTimeTargetFormat
  profile : ModelZone.ConcreteProfile
  targetIsDateTime : checked.target.kind = .dateTime
  componentsComplete :
    checked.target.components = TemporalComponents.now
  formatMatches :
    DateTimeTargetFormat.ofSource? checked.policy.format = some format
  profileMatches :
    ModelZone.ConcreteProfile.ofId? checked.timeZoneId = some profile

namespace CheckedTemporalTargetPolicy

/-- Refine a checked temporal target to the first executable DateTime subset. Every wider kind, component set, format, or zone is an explicit refusal. -/
def toDateTimeTarget
    (checked : CheckedTemporalTargetPolicy model) :
    Except DateTimeTargetElabError (CheckedDateTimeTarget model) := do
  if hKind : checked.target.kind = .dateTime then
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
                targetIsDateTime := hKind
                componentsComplete := hComponents
                formatMatches := hFormat
                profileMatches := hProfile }
    else
      throw (.components checked.target.id checked.target.components)
  else
    throw (.targetKind checked.target.id checked.target.kind)

end CheckedTemporalTargetPolicy

/-- Resolve and refine one model-owned complete DateTime target whose repetition scope is bound by the caller's reading environment. -/
def elaborateDateTimeTargetIn
    (model : FlatModel) (scope : List RepeatableLevel)
    (targetField : FieldId) :
    Except DateTimeTargetElabError (CheckedDateTimeTarget model) := do
  let checked ←
    elaborateTemporalTargetPolicyIn model scope targetField
      |>.mapError .targetPolicy
  checked.toDateTimeTarget

/-- Resolve and refine one model-owned nonrepeatable complete DateTime target. -/
def elaborateDateTimeTarget
    (model : FlatModel) (targetField : FieldId) :
    Except DateTimeTargetElabError (CheckedDateTimeTarget model) :=
  elaborateDateTimeTargetIn model [] targetField

/-- Runtime refusal when an exact result instant has no local DateTime label in the selected concrete profile. -/
inductive DateTimeTargetEvaluationFault where
  | localDateTimeUnavailable (instant : Instant)
  deriving Repr, DecidableEq

namespace CheckedDateTimeTarget

/-- Render one already-selected DateTime computation result at the target's declared whole-second precision without classifying a delta or mutating a document. -/
def evaluate
    (target : CheckedDateTimeTarget model) :
    TemporalComputationResult →
      Except DateTimeTargetEvaluationFault DateTimeTargetOutcome
  | .noValue => pure .noValue
  | .poison cause => pure (.poison cause)
  | .value instant =>
      match target.profile.localDateTime? instant with
      | none => throw (.localDateTimeUnavailable instant)
      | some dateTime =>
          pure (.accepted (target.format.render dateTime))

end CheckedDateTimeTarget

end A12Kernel
