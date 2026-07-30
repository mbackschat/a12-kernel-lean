import A12Kernel.Elaboration.StringComputationRunResult
import A12Kernel.Semantics.StringApplication

/-! # String-specific whole-run application

This capsule applies an already-classified String result to an explicitly supplied compatible destination. The destination projects only the exact nonrepeatable String target states admitted by this fragment; it is not another checked document. Application distinguishes source-classified retained clears from direct errored and accepted outcomes and never reclassifies an action against the destination.
-/

namespace A12Kernel

/-- The exact caller-supplied target-state projection needed by one String result target-key domain. -/
abbrev StringComputationDestination (Target : Type := FieldId) :=
  Target → StringTargetState

namespace StringComputationDestination

/-- Replace one target state while preserving every other field projection. -/
def update {Target : Type} [DecidableEq Target]
    (destination : StringComputationDestination Target)
    (target : Target) (state : StringTargetState) :
    StringComputationDestination Target :=
  fun candidate => if candidate = target then state else destination candidate

/-- Specialize the existing one-target transition at one field. -/
def applyOutcome {Target : Type} [DecidableEq Target]
    (destination : StringComputationDestination Target)
    (target : Target) (outcome : StringTargetOutcome) :
    StringComputationDestination Target :=
  destination.update target (outcome.applyTo (destination target))

/-- Apply one source-classified CLEARED action without reclassifying it against the destination. -/
def applyRetainedClear {Target : Type} [DecidableEq Target]
    (destination : StringComputationDestination Target)
    (target : Target) : StringComputationDestination Target :=
  destination.update target (destination target).applyRetainedClear

end StringComputationDestination

namespace StringComputationRunView

inductive StringComputationRunApplicationError
    (Target : Type := FieldId) where
  | duplicateActionTarget (target : Target)
  deriving Repr, DecidableEq

/-- The targets consumed by application. Successful unchanged instances and residual messages are deliberately absent. -/
def actionTargets {Target : Type}
    (view : StringComputationRunView ResidualMessage Target) :
    List Target :=
  view.cleared ++ view.withErrors.map (·.targetField) ++
    view.withChanges.map (·.targetField)

/-- Locate the first repeated exact target key in encounter order. -/
def firstDuplicateStringTarget? {Target : Type} [DecidableEq Target] :
    List Target → Option Target
  | [] => none
  | target :: remaining =>
      if target ∈ remaining then some target
      else firstDuplicateStringTarget? remaining

/-- Locate the first malformed repeated action target before destination application begins. -/
def firstDuplicateActionTarget? {Target : Type} [DecidableEq Target]
    (view : StringComputationRunView ResidualMessage Target) :
    Option Target :=
  firstDuplicateStringTarget? view.actionTargets

/-- Apply retained clears, target errors, then source-relative changes. Repeated action targets fail structurally before application. -/
def applyTo {Target : Type} [DecidableEq Target]
    (view : StringComputationRunView ResidualMessage Target)
    (destination : StringComputationDestination Target) :
    Except (StringComputationRunApplicationError Target)
      (StringComputationDestination Target) :=
  match view.firstDuplicateActionTarget? with
  | some duplicate => .error (.duplicateActionTarget duplicate)
  | none =>
      let afterCleared := view.cleared.foldl
        (fun current target => current.applyRetainedClear target) destination
      let afterErrors := view.withErrors.foldl
        (fun current computed => current.applyOutcome computed.targetField
          (.errored computed.attempted computed.cause)) afterCleared
      .ok (view.withChanges.foldl
        (fun current computed => current.applyOutcome computed.targetField
          (.accepted computed.value)) afterErrors)

end StringComputationRunView

end A12Kernel
