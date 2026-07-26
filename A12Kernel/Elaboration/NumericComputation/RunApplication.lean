import A12Kernel.Elaboration.NumericComputation.RunResult
import A12Kernel.Semantics.NumericApplication

/-! # Number-specific whole-run application

This capsule applies an already-classified Number result to an explicitly supplied compatible destination. It consumes only clears, errors, and source-relative changes, delegates each address to the existing one-target transition, and never reclassifies against the destination. -/

namespace A12Kernel

/-- The exact caller-supplied target-state projection needed by one Number result target-key domain. -/
abbrev NumericComputationDestination (Target : Type := FieldId) :=
  Target → NumericTargetState

namespace NumericComputationDestination

def update {Target : Type} [DecidableEq Target]
    (destination : NumericComputationDestination Target)
    (target : Target) (state : NumericTargetState) :
    NumericComputationDestination Target :=
  fun candidate =>
    if candidate = target then state else destination candidate

def applyOutcome {Target : Type} [DecidableEq Target]
    (destination : NumericComputationDestination Target)
    (target : Target) (outcome : NumericTargetOutcome) :
    NumericComputationDestination Target :=
  destination.update target (outcome.applyTo (destination target))

end NumericComputationDestination

namespace NumericComputationRunView

inductive NumericComputationRunApplicationError
    (Target : Type := FieldId) where
  | duplicateActionTarget (target : Target)
  deriving Repr, DecidableEq

/-- Targets consumed by application. Unchanged successes and residual messages are deliberately absent. -/
def actionTargets {Target : Type}
    (view : NumericComputationRunView ResidualMessage Target) :
    List Target :=
  view.cleared ++ view.withErrors.map (·.targetField) ++
    view.withChanges.map (·.targetField)

def firstDuplicateActionTarget? {Target : Type} [DecidableEq Target]
    (view : NumericComputationRunView ResidualMessage Target) :
    Option Target :=
  firstDuplicate? view.actionTargets
where
  firstDuplicate? : List Target → Option Target
    | [] => none
    | target :: remaining =>
        if target ∈ remaining then some target
        else firstDuplicate? remaining

/-- Apply clears, errors, then source-relative changes. Repeated action targets are structural rather than list-order conflicts. -/
def applyTo {Target : Type} [DecidableEq Target]
    (view : NumericComputationRunView ResidualMessage Target)
    (destination : NumericComputationDestination Target) :
    Except (NumericComputationRunApplicationError Target)
      (NumericComputationDestination Target) :=
  match view.firstDuplicateActionTarget? with
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
