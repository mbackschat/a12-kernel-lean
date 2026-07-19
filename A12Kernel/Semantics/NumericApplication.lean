import A12Kernel.Semantics.NumericTarget

/-! # Exact one-target Number application

This capsule models only the placement-sensitive final state of one already-addressed Number target. It preserves exact decimal form and deliberately excludes document traversal, missing-ancestor creation, repeatable addressing, scheduling, multi-target application, and whether an extensionally equal value was physically rewritten.
-/

namespace A12Kernel

/-- Exact state of one Number target cell. Unlike `PriorNumericTarget`, this type preserves absent versus present-empty placement. -/
inductive NumericTargetState where
  | absent
  | presentEmpty
  | presentValue (stored : StoredNumber)
  deriving Repr, DecidableEq

namespace NumericTargetState

/-- Empty a present target in place without creating an absent target. -/
def clearValue : NumericTargetState → NumericTargetState
  | .absent => .absent
  | .presentEmpty | .presentValue _ => .presentEmpty

/-- Project away placement while retaining the exact stored decimal, when present. -/
def storedValue : NumericTargetState → Option StoredNumber
  | .presentValue stored => some stored
  | .absent | .presentEmpty => none

/-- Report target placement independently of its stored value. -/
def isPresent : NumericTargetState → Bool
  | .absent => false
  | .presentEmpty | .presentValue _ => true

/-- Project exact state to the delta-only prior vocabulary, deliberately merging absent and present-empty. -/
def toDeltaPrior : NumericTargetState → PriorNumericTarget
  | .presentValue stored => .filled stored
  | .absent | .presentEmpty => .empty

end NumericTargetState

namespace NumericTargetOutcome

/-- Value-only projection after target classification. A rejected attempt is not stored by application but remains available on the full outcome and ERRORED delta; target invalidity remains full-outcome-only. -/
def appliedValue : NumericTargetOutcome → Option StoredNumber
  | .accepted stored => some stored
  | .noValue | .rejected _ _ | .invalidNoValue _ | .inheritedPoison _ => none

/-- Apply one supported target outcome to the abstract final state. Accepted output yields its exact decimal form; every other outcome empties a present target in place and leaves an absent target absent. -/
def applyTo : NumericTargetOutcome → NumericTargetState → NumericTargetState
  | .accepted stored, _ => .presentValue stored
  | .noValue, prior
  | .rejected _ _, prior
  | .invalidNoValue _, prior
  | .inheritedPoison _, prior => prior.clearValue

end NumericTargetOutcome

end A12Kernel
