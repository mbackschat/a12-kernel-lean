import A12Kernel.Elaboration.NumericComputation.RunResult
import A12Kernel.Semantics.NumericApplication

/-! # Number-specific whole-run application

This capsule applies an already-classified Number result to an explicitly supplied compatible destination. It consumes only clears, errors, and source-relative changes, delegates each address to the existing one-target transition, and never reclassifies against the destination. -/

namespace A12Kernel

/-- The exact caller-supplied target-state projection needed by the nonrepeatable Number fragment. -/
abbrev NumericComputationDestination := FieldId → NumericTargetState

namespace NumericComputationDestination

def update (destination : NumericComputationDestination)
    (target : FieldId) (state : NumericTargetState) :
    NumericComputationDestination :=
  fun field => if field == target then state else destination field

def applyOutcome (destination : NumericComputationDestination)
    (target : FieldId) (outcome : NumericTargetOutcome) :
    NumericComputationDestination :=
  destination.update target (outcome.applyTo (destination target))

end NumericComputationDestination

namespace NumericComputationRunView

inductive NumericComputationRunApplicationError where
  | duplicateActionTarget (field : FieldId)
  deriving Repr, DecidableEq

/-- Targets consumed by application. Unchanged successes and residual messages are deliberately absent. -/
def actionTargets (view : NumericComputationRunView ResidualMessage) :
    List FieldId :=
  view.cleared ++ view.withErrors.map (·.targetField) ++
    view.withChanges.map (·.targetField)

/-- Apply clears, errors, then source-relative changes. Repeated action targets are structural rather than list-order conflicts. -/
def applyTo (view : NumericComputationRunView ResidualMessage)
    (destination : NumericComputationDestination) :
    Except NumericComputationRunApplicationError NumericComputationDestination :=
  match FieldId.firstDuplicate? view.actionTargets with
  | some duplicate => .error (.duplicateActionTarget duplicate)
  | none =>
      let afterCleared := view.cleared.foldl
        (fun current target => current.applyOutcome target .noValue) destination
      let afterErrors := view.withErrors.foldl
        (fun current computed => current.applyOutcome computed.targetField
          (.rejected computed.attempted computed.cause)) afterCleared
      .ok (view.withChanges.foldl
        (fun current computed => current.applyOutcome computed.targetField
          (.accepted computed.value)) afterErrors)

end NumericComputationRunView

end A12Kernel
