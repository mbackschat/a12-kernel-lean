import A12Kernel.Elaboration.TemporalComputationResult

/-! # DateTime whole-result application

This capsule applies an already-classified DateTime result to an explicitly supplied compatible destination. It consumes only clears and source-relative changes through the existing one-target transition, and never reclassifies against the destination. The bounded result domain has no target-error action.
-/

namespace A12Kernel

/-- Exact caller-supplied target-state projection needed by the nonrepeatable DateTime fragment. -/
abbrev DateTimeComputationDestination :=
  TemporalComputationDestination StoredDateTime

namespace DateTimeComputationDestination

/-- Replace one target projection while preserving every other field. -/
def update (destination : DateTimeComputationDestination)
    (target : FieldId) (state : DateTimeTargetState) :
    DateTimeComputationDestination :=
  TemporalComputationDestination.update destination target state

/-- Specialize the existing one-target transition at one field. -/
def applyOutcome (destination : DateTimeComputationDestination)
    (target : FieldId) (outcome : DateTimeTargetOutcome) :
    DateTimeComputationDestination :=
  destination.update target (outcome.applyTo (destination target))

end DateTimeComputationDestination

namespace DateTimeComputationRunView

/-- Structural failure before any destination action is selected. -/
inductive DateTimeComputationRunApplicationError where
  | duplicateActionTarget (field : FieldId)
  deriving Repr, DecidableEq

/-- Targets consumed by application. Successful unchanged instances and residual messages are deliberately absent. -/
def actionTargets (view : DateTimeComputationRunView ResidualMessage) :
    List FieldId :=
  view.cleared ++ view.withChanges.map (·.targetField)

/-- Apply the immutable V2 action collections in kernel order: clears, then source-relative changed successes. Duplicate targets fail before destination lookup. -/
def applyTo (view : DateTimeComputationRunView ResidualMessage)
    (destination : DateTimeComputationDestination) :
    Except DateTimeComputationRunApplicationError
      DateTimeComputationDestination :=
  match FieldId.firstDuplicate? view.actionTargets with
  | some duplicate => .error (.duplicateActionTarget duplicate)
  | none =>
      let afterCleared := view.cleared.foldl
        (fun current target => current.applyOutcome target .noValue) destination
      .ok (view.withChanges.foldl
        (fun current computed => current.applyOutcome computed.targetField
          (.accepted computed.value)) afterCleared)

end DateTimeComputationRunView

end A12Kernel
