import A12Kernel.Semantics.ScalarText
import A12Kernel.Document

/-! # Exact one-target Boolean application

This capsule retains typed Boolean identity while preserving absent, present-empty, and formally invalid nonempty placement. It owns only an already-classified fixed-target state transition; document traversal, repeatable addressing, scheduling, and validation remain separate.
-/

namespace A12Kernel

/-- Exact comparison-relevant state of one Boolean target cell. A nonempty invalid token remains filled without pretending to carry a Boolean value. -/
inductive BooleanTargetState where
  | absent
  | presentEmpty
  | presentValue (value : Bool)
  | presentInvalid (stored : String)
  deriving Repr, DecidableEq

namespace BooleanTargetState

/-- Return the typed Boolean identity of a valid filled target. -/
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

/-- Exact caller-supplied Boolean field-state projection. -/
abbrev BooleanComputationDestination := FieldId → BooleanTargetState

namespace BooleanComputationDestination

/-- Replace one Boolean target state while preserving every other projection. -/
def update (destination : BooleanComputationDestination)
    (target : FieldId) (state : BooleanTargetState) :
    BooleanComputationDestination :=
  fun candidate => if candidate == target then state else destination candidate

/-- Apply one retained source-classified clear. -/
def applyRetainedClear (destination : BooleanComputationDestination)
    (target : FieldId) : BooleanComputationDestination :=
  destination.update target (destination target).applyRetainedClear

/-- Apply one changed typed Boolean value. -/
def applyValue (destination : BooleanComputationDestination)
    (target : FieldId) (value : Bool) : BooleanComputationDestination :=
  destination.update target (.presentValue value)

end BooleanComputationDestination

end A12Kernel
