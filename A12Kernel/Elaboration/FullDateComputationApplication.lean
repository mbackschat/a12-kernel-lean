import A12Kernel.Elaboration.TemporalComputationResult

/-! # Full-Date whole-result application

This capsule applies an already-classified full-Date result to an explicitly supplied compatible destination. It consumes only clears, target errors, and source-relative changes through the existing one-target transition, and never reclassifies against the destination.
-/

namespace A12Kernel

/-- Exact caller-supplied target-state projection needed by the nonrepeatable full-Date fragment. -/
abbrev FullDateComputationDestination := FieldId → FullDateTargetState

namespace FullDateComputationDestination

/-- Replace one target projection while preserving every other field. -/
def update (destination : FullDateComputationDestination)
    (target : FieldId) (state : FullDateTargetState) :
    FullDateComputationDestination :=
  fun field => if field == target then state else destination field

/-- Specialize the existing one-target transition at one field. -/
def applyOutcome (destination : FullDateComputationDestination)
    (target : FieldId) (outcome : FullDateTargetOutcome) :
    FullDateComputationDestination :=
  destination.update target (outcome.applyTo (destination target))

end FullDateComputationDestination

namespace FullDateComputationRunView

/-- Structural failure before any destination action is selected. -/
inductive FullDateComputationRunApplicationError where
  | duplicateActionTarget (field : FieldId)
  deriving Repr, DecidableEq

/-- Targets consumed by application. Successful unchanged instances and residual messages are deliberately absent. -/
def actionTargets (view : FullDateComputationRunView ResidualMessage) :
    List FieldId :=
  view.cleared ++ view.withErrors.map (·.targetField) ++
    view.withChanges.map (·.targetField)

/-- Apply the immutable V2 action collections in kernel order: clears, errors, then source-relative changed successes. Duplicate targets fail before destination lookup. -/
def applyTo (view : FullDateComputationRunView ResidualMessage)
    (destination : FullDateComputationDestination) :
    Except FullDateComputationRunApplicationError
      FullDateComputationDestination :=
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

end FullDateComputationRunView

end A12Kernel
