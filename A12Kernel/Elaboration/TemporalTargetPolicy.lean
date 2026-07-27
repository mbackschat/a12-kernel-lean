import A12Kernel.Elaboration.Flat.Model
import A12Kernel.Semantics.TemporalTarget

/-! # Checked temporal-target policy

This capsule resolves one nonrepeatable Date or DateTime target against a validated flat model and retains the complete declaration-owned format policy plus the model-owned time zone. Its bounded refinements render full Date in two exact formats and DateTime in the kernel's standard whole-second format against one concrete model-zone profile. Parsing, delta classification, and application remain separate.
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

/-- One checked Date/DateTime target whose declaration policy cannot be replaced by caller input. -/
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
  | partialMode (target : FieldId) (actual : TemporalPartialMode)
  | unsupportedFormat (target : FieldId) (source : String)
  | unsupportedZone (zoneId : String)
  deriving Repr, DecidableEq

/-- One checked full-Date target with an executable format and concrete model-zone profile. -/
structure CheckedFullDateTarget (model : FlatModel) where
  checked : CheckedTemporalTargetPolicy model
  format : FullDateTargetFormat
  profile : ModelZone.ConcreteProfile
  targetIsDate : checked.target.kind = .date
  partialModeFull : checked.policy.partialMode = .full
  formatMatches :
    FullDateTargetFormat.ofSource? checked.policy.format = some format
  profileMatches :
    ModelZone.ConcreteProfile.ofId? checked.timeZoneId = some profile

namespace CheckedTemporalTargetPolicy

/-- Refine a checked temporal target to the first executable full-Date subset. Every wider kind, partial mode, format, or zone is an explicit refusal. -/
def toFullDateTarget
    (checked : CheckedTemporalTargetPolicy model) :
    Except FullDateTargetElabError (CheckedFullDateTarget model) := do
  if hDate : checked.target.kind = .date then
    if hMode : checked.policy.partialMode = .full then
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
                partialModeFull := hMode
                formatMatches := hFormat
                profileMatches := hProfile }
    else
      throw (.partialMode checked.target.id checked.policy.partialMode)
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
          let stored := target.format.render date
          if target.checked.policy.youngerThan1900Check &&
              date.before1900 then
            pure (.errored stored .before1900)
          else
            pure (.accepted stored)

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
