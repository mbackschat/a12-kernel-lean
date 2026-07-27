import A12Kernel.Elaboration.Flat.Model
import A12Kernel.Semantics.TemporalTarget

/-! # Checked temporal declaration policy

This capsule resolves one nonrepeatable Date or DateTime declaration against a validated flat model and retains the complete declaration-owned format policy plus the model-owned time zone. Its first consumers render computed targets and certify stored partial-Date `ValueAsDate`; the bounded target refinements render concrete Date values in two exact formats, including when the target permits partially known stored inputs, and DateTime in the kernel's standard whole-second format against one concrete model-zone profile. Parsing stored text, delta classification, and application remain separate.
-/

namespace A12Kernel

/-- Fail-closed reasons before a temporal target can expose its declaration-owned policy. -/
inductive TemporalTargetElabError where
  | resolve (error : ResolveError)
  | targetNotTemporal (target : FieldId)
  | unsupportedTargetKind (target : FieldId) (kind : TemporalKind)
  | targetPolicyUnavailable (target : FieldId)
  | incoherentCore
  deriving Repr, DecidableEq

/-- One checked Date/DateTime declaration whose policy cannot be replaced by caller input. Existing field names remain target-oriented because computed targets were the first consumer. -/
structure CheckedTemporalTargetPolicy (model : FlatModel) where
  target : FlatTemporalField
  policy : TemporalTargetPolicy
  targetSupported : target.kind = .date ∨ target.kind = .dateTime
  modelWellFormed : model.validate.isOk = true
  policyAdmitted :
    policy.errorFor? target.kind target.components = none

namespace CheckedTemporalTargetPolicy

/-- Rendering observes the exact model time-zone identifier separately from the field's declaration-owned policy. -/
def timeZoneId (_ : CheckedTemporalTargetPolicy model) : String :=
  model.timeZoneId

end CheckedTemporalTargetPolicy

/-- Resolve one complete nonrepeatable Date/DateTime target policy. A temporal declaration without retained exact policy is explicit insufficient information. -/
def elaborateTemporalTargetPolicy
    (model : FlatModel) (targetField : FieldId) :
    Except TemporalTargetElabError (CheckedTemporalTargetPolicy model) := do
  match hModel : model.validate with
  | .error error => throw (.resolve error)
  | .ok () =>
      let declaration ←
        model.resolveNonrepeatableDeclarationById targetField |>.mapError .resolve
      let target ← match declaration.toTemporalField? with
        | some target => pure target
        | none => throw (.targetNotTemporal targetField)
      let finish
          (targetSupported :
            target.kind = .date ∨ target.kind = .dateTime) :
          Except TemporalTargetElabError
            (CheckedTemporalTargetPolicy model) := do
        let policy ←
          match declaration.temporalTargetPolicy,
              declaration.toTemporalTargetPolicy? with
          | none, _ => throw (.targetPolicyUnavailable targetField)
          | some _, some policy => pure policy
          | some _, none => throw .incoherentCore
        if hPolicy : policy.errorFor? target.kind target.components = none then
          pure {
            target
            policy
            targetSupported
            modelWellFormed := by
              rw [hModel]
              rfl
            policyAdmitted := hPolicy }
        else
          throw .incoherentCore
      match hKind : target.kind with
      | .time => throw (.unsupportedTargetKind targetField .time)
      | .date => finish (Or.inl hKind)
      | .dateTime => finish (Or.inr hKind)

/-- Static refusal before the bounded full-Date target can execute. -/
inductive FullDateTargetElabError where
  | targetPolicy (error : TemporalTargetElabError)
  | targetKind (target : FieldId) (actual : TemporalKind)
  | unsupportedFormat (target : FieldId) (source : String)
  | unsupportedZone (zoneId : String)
  deriving Repr, DecidableEq

/-- One checked concrete-Date target with an executable format and concrete model-zone profile. Its declaration may also permit partially known stored inputs; computation itself supplies no unknown fragments. -/
structure CheckedFullDateTarget (model : FlatModel) where
  checked : CheckedTemporalTargetPolicy model
  format : FullDateTargetFormat
  profile : ModelZone.ConcreteProfile
  targetIsDate : checked.target.kind = .date
  formatMatches :
    FullDateTargetFormat.ofSource? checked.policy.format = some format
  profileMatches :
    ModelZone.ConcreteProfile.ofId? checked.timeZoneId = some profile

namespace CheckedTemporalTargetPolicy

/-- Refine a checked temporal target to the first executable concrete-Date subset. Partial modes remain admitted because every one accepts a fully known Date; wider kinds, formats, and zones are explicit refusals. -/
def toFullDateTarget
    (checked : CheckedTemporalTargetPolicy model) :
    Except FullDateTargetElabError (CheckedFullDateTarget model) := do
  if hDate : checked.target.kind = .date then
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
              formatMatches := hFormat
              profileMatches := hProfile }
  else
    throw (.targetKind checked.target.id checked.target.kind)

end CheckedTemporalTargetPolicy

/-- Resolve and refine one model-owned nonrepeatable full-Date target. -/
def elaborateFullDateTarget
    (model : FlatModel) (targetField : FieldId) :
    Except FullDateTargetElabError (CheckedFullDateTarget model) := do
  let checked ←
    elaborateTemporalTargetPolicy model targetField |>.mapError .targetPolicy
  checked.toFullDateTarget

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

/-- Resolve and refine one model-owned nonrepeatable complete DateTime target. -/
def elaborateDateTimeTarget
    (model : FlatModel) (targetField : FieldId) :
    Except DateTimeTargetElabError (CheckedDateTimeTarget model) := do
  let checked ←
    elaborateTemporalTargetPolicy model targetField |>.mapError .targetPolicy
  checked.toDateTimeTarget

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
