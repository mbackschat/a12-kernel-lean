import A12Kernel.Elaboration.Flat.Model

/-! # Checked temporal-target policy

This capsule resolves one nonrepeatable Date or DateTime target against a validated flat model and retains the complete declaration-owned format policy plus the model-owned time zone. It deliberately performs no parsing, rendering, target check, result classification, or application.
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

end A12Kernel
