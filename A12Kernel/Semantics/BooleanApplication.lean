import A12Kernel.Semantics.ScalarText
import A12Kernel.Document

/-! # Typed Boolean and Confirm computation outcomes and target-state application

This module retains typed Boolean and Confirm identity while preserving absent, present-empty, and formally invalid nonempty placement. Its target-polymorphic state transition serves both fixed field identifiers and exact repeatable cell addresses; document traversal, scheduling, row reconstruction, and validation remain separate.
-/

namespace A12Kernel

/-- Operation-neutral Boolean computation outcome. A selected source may clear on exhaustion or poison, while a constant uses only the value arm. -/
inductive BooleanComputationOutcome where
  | value (value : Bool)
  | noValue
  | poison (cause : FormalCause)
  deriving Repr, DecidableEq

/-- Exact comparison-relevant state of one Boolean or Confirm target cell. A nonempty invalid token remains filled without pretending to carry a typed value. -/
inductive BooleanTargetState where
  | absent
  | presentEmpty
  | presentValue (value : Bool)
  | presentInvalid (stored : String)
  deriving Repr, DecidableEq

namespace BooleanTargetState

/-- Return the typed Boolean or Confirm identity of a valid filled target. -/
def value? : BooleanTargetState → Option Bool
  | .presentValue value => some value
  | .absent | .presentEmpty | .presentInvalid _ => none

/-- A valid or invalid nonempty placement is source-filled for clear classification. -/
def isFilled : BooleanTargetState → Bool
  | .presentValue _ | .presentInvalid _ => true
  | .absent | .presentEmpty => false

/-- Apply one source-classified CLEARED action, materializing present-empty even from absence. -/
def applyRetainedClear : BooleanTargetState → BooleanTargetState
  | .absent | .presentEmpty | .presentValue _ | .presentInvalid _ => .presentEmpty

end BooleanTargetState

/-- Exact caller-supplied Boolean or Confirm target-state projection. -/
abbrev BooleanComputationDestination (Target : Type := FieldId) :=
  Target → BooleanTargetState

namespace BooleanComputationDestination

/-- Replace one Boolean target state while preserving every other projection. -/
def update [DecidableEq Target]
    (destination : BooleanComputationDestination Target)
    (target : Target) (state : BooleanTargetState) :
    BooleanComputationDestination Target :=
  fun candidate => if candidate = target then state else destination candidate

/-- Apply one retained source-classified clear. -/
def applyRetainedClear [DecidableEq Target]
    (destination : BooleanComputationDestination Target)
    (target : Target) : BooleanComputationDestination Target :=
  destination.update target (destination target).applyRetainedClear

/-- Apply one changed typed Boolean value. -/
def applyValue [DecidableEq Target]
    (destination : BooleanComputationDestination Target)
    (target : Target) (value : Bool) : BooleanComputationDestination Target :=
  destination.update target (.presentValue value)

end BooleanComputationDestination

end A12Kernel
