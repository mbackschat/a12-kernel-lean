import A12Kernel.Elaboration.StringComputationRunResult
import A12Kernel.Semantics.StringApplication

/-! # String-specific whole-run application

This capsule applies an already-classified String result to an explicitly supplied compatible destination. The destination projects only the exact nonrepeatable String target states admitted by this fragment; it is not another checked document. Application folds cleared targets, errored attempts, and changed successes through the existing one-target transition and never reclassifies change against the destination.
-/

namespace A12Kernel

/-- The exact caller-supplied target-state projection needed by the nonrepeatable String fragment. -/
abbrev StringComputationDestination := FieldId → StringTargetState

namespace StringComputationDestination

/-- Replace one target state while preserving every other field projection. -/
def update (destination : StringComputationDestination)
    (target : FieldId) (state : StringTargetState) :
    StringComputationDestination :=
  fun field => if field == target then state else destination field

/-- Specialize the existing one-target transition at one field. -/
def applyOutcome (destination : StringComputationDestination)
    (target : FieldId) (outcome : StringTargetOutcome) :
    StringComputationDestination :=
  destination.update target (outcome.applyTo (destination target))

end StringComputationDestination

namespace StringComputationRunView

inductive StringComputationRunApplicationError where
  | duplicateActionTarget (field : FieldId)
  deriving Repr, DecidableEq

/-- The targets consumed by application. Successful unchanged instances and residual messages are deliberately absent. -/
def actionTargets (view : StringComputationRunView ResidualMessage) :
    List FieldId :=
  view.cleared ++ view.withErrors.map (·.targetField) ++
    view.withChanges.map (·.targetField)

/-- Apply the immutable V2 action collections in kernel order: public clears, errored instances, then source-relative changed successes. A malformed view with a repeated action target fails structurally rather than letting private list order choose a write. -/
def applyTo (view : StringComputationRunView ResidualMessage)
    (destination : StringComputationDestination) :
    Except StringComputationRunApplicationError StringComputationDestination :=
  match FieldId.firstDuplicate? view.actionTargets with
  | some duplicate => .error (.duplicateActionTarget duplicate)
  | none =>
      let afterCleared := view.cleared.foldl
        (fun current target => current.applyOutcome target .noValue) destination
      let afterErrors := view.withErrors.foldl
        (fun current computed => current.applyOutcome computed.targetField
          (.errored computed.attempted computed.cause)) afterCleared
      .ok (view.withChanges.foldl
        (fun current computed => current.applyOutcome computed.targetField
          (.accepted computed.value)) afterErrors)

end StringComputationRunView

end A12Kernel
