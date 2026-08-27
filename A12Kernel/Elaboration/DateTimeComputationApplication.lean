import A12Kernel.Elaboration.TemporalValueComputationApplication

/-! # DateTime whole-result application

This capsule applies an already-classified DateTime result to an explicitly supplied compatible destination. It distinguishes source-classified retained clears from accepted outcomes and never reclassifies an action against the destination. The bounded result domain has no target-error action.
-/

namespace A12Kernel

/-- Exact caller-supplied target-state projection shared by scalar and addressed DateTime fragments. -/
abbrev DateTimeComputationDestination (Target : Type := FieldId) :=
  TemporalComputationDestination StoredDateTime Target

namespace DateTimeComputationDestination

/-- Replace one target projection while preserving every other field. -/
def update {Target : Type} [DecidableEq Target]
    (destination : DateTimeComputationDestination Target)
    (target : Target) (state : DateTimeTargetState) :
    DateTimeComputationDestination Target :=
  TemporalComputationDestination.update destination target state

/-- Specialize the existing one-target transition at one field. -/
def applyOutcome {Target : Type} [DecidableEq Target]
    (destination : DateTimeComputationDestination Target)
    (target : Target) (outcome : DateTimeTargetOutcome) :
    DateTimeComputationDestination Target :=
  destination.update target (outcome.applyTo (destination target))

/-- Apply one source-classified CLEARED action without reclassifying it against the destination. -/
def applyRetainedClear {Target : Type} [DecidableEq Target]
    (destination : DateTimeComputationDestination Target)
    (target : Target) : DateTimeComputationDestination Target :=
  TemporalComputationDestination.applyRetainedClear destination target

end DateTimeComputationDestination

namespace DateTimeComputationRunView

/-- Structural failure before any destination action is selected. -/
abbrev DateTimeComputationRunApplicationError
    (Target : Type := FieldId) :=
  TemporalValueComputationApplicationError Target

/-- Targets consumed by application. Successful unchanged instances and residual messages are deliberately absent. -/
def actionTargets {Target : Type}
    (view : DateTimeComputationRunView ResidualMessage Target) :
    List Target :=
  TemporalValueComputationRunView.actionTargets view

/-- Apply the immutable V2 action collections in kernel order: clears, then source-relative changed successes. Duplicate targets fail before destination lookup. -/
def applyTo {Target : Type} [DecidableEq Target]
    (view : DateTimeComputationRunView ResidualMessage Target)
    (destination : DateTimeComputationDestination Target) :
    Except (DateTimeComputationRunApplicationError Target)
      (DateTimeComputationDestination Target) :=
  TemporalValueComputationRunView.applyTo view destination
    DateTimeComputationDestination.applyRetainedClear
    (fun current target value =>
      current.applyOutcome target (.accepted value))

/-- Fail-closed errors for checked nonrepeatable DateTime destination projection. -/
inductive DateTimeComputationCheckedApplicationError where
  | duplicateActionTarget (field : FieldId)
  | targetField (field : FieldId) (cause : ResolveError)
  | nonDateTimeTarget (field : FieldId)
  | repeatableTarget (field : FieldId)
  deriving Repr, DecidableEq

private def acceptsActionKind : FieldKind → Bool
  | .temporal .dateTime components => components == TemporalComponents.now
  | _ => false

def validateActionTargets (model : FlatModel) (targets : List FieldId) :
    Except DateTimeComputationCheckedApplicationError Unit :=
  TemporalComputationApplicationTarget.validateAllNonrepeatable
    model acceptsActionKind
    DateTimeComputationCheckedApplicationError.targetField
    DateTimeComputationCheckedApplicationError.nonDateTimeTarget
    DateTimeComputationCheckedApplicationError.repeatableTarget targets

/-- Apply one retained nonrepeatable DateTime result to the exact root DateTime-state projection of a separately supplied checked destination. The retained result is not model-indexed, so source/destination model compatibility remains a caller precondition. -/
def applyToChecked (view : DateTimeComputationRunView ResidualMessage)
    (destination : CheckedDocument model) :
    Except DateTimeComputationCheckedApplicationError
      DateTimeComputationDestination :=
  match FieldId.firstDuplicate? view.actionTargets with
  | some duplicate => .error (.duplicateActionTarget duplicate)
  | none => do
      validateActionTargets model view.actionTargets
      (view.applyTo destination.sourceDateTimeTargetState).mapError
        (fun | .duplicateActionTarget duplicate => .duplicateActionTarget duplicate)

end DateTimeComputationRunView

end A12Kernel
