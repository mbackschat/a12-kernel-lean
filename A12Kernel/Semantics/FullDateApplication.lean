import A12Kernel.Semantics.TemporalTarget

/-! # Full-Date delta and exact one-target application

This capsule classifies one already-checked full-Date target outcome relative to its computation source and applies that classification to one exact target cell. It preserves rendered text and placement without parsing the stored Date again. Document traversal, missing-ancestor creation, repeatable addressing, scheduling, and multi-target application remain separate.
-/

namespace A12Kernel

/-- Prior full-Date value used by source-relative delta classification. Empty placement is intentionally not represented here. -/
inductive PriorFullDateTarget where
  | empty
  | filled (value : StoredDate)
  deriving Repr, DecidableEq

/-- Source-relative action for one checked full-Date outcome. Target rejection retains the exact rendered attempt. -/
inductive FullDateDelta where
  | value (stored : StoredDate)
  | cleared
  | errored (attempted : StoredDate) (cause : FullDateTargetError)
  deriving Repr, DecidableEq

namespace FullDateDelta

/-- Classify an accepted stored Date relative to the source value. -/
def projectValue (value : StoredDate) : PriorFullDateTarget → Option FullDateDelta
  | .empty => some (.value value)
  | .filled previous => if value == previous then none else some (.value value)

/-- Classify an outcome that stores no value relative to the source value. -/
def projectNoValue : PriorFullDateTarget → Option FullDateDelta
  | .empty => none
  | .filled _ => some .cleared

end FullDateDelta

namespace FullDateTargetOutcome

/-- Classify one rich target outcome relative to the computation source. Accepted values are change-sensitive; target errors are unconditional; quiet no-value and poison clear only a source-filled target. -/
def projectDelta (outcome : FullDateTargetOutcome)
    (prior : PriorFullDateTarget) : Option FullDateDelta :=
  match outcome with
  | .accepted value => FullDateDelta.projectValue value prior
  | .errored attempted cause => some (.errored attempted cause)
  | .noValue | .poison _ => FullDateDelta.projectNoValue prior

/-- Exact stored value supplied by an accepted outcome, independently of placement. -/
def appliedValue : FullDateTargetOutcome → Option StoredDate
  | .accepted value => some value
  | .noValue | .errored _ _ | .poison _ => none

end FullDateTargetOutcome

/-- Exact state of one full-Date target cell. This retains absent versus present-empty placement beyond the delta vocabulary. -/
inductive FullDateTargetState where
  | absent
  | presentEmpty
  | presentValue (value : StoredDate)
  deriving Repr, DecidableEq

namespace FullDateTargetState

/-- Empty a present target in place without creating an absent target. -/
def clearValue : FullDateTargetState → FullDateTargetState
  | .absent => .absent
  | .presentEmpty | .presentValue _ => .presentEmpty

/-- Return the exact stored Date when this state contains one. -/
def storedValue : FullDateTargetState → Option StoredDate
  | .presentValue value => some value
  | .absent | .presentEmpty => none

/-- Report whether the target cell exists independently of its stored value. -/
def isPresent : FullDateTargetState → Bool
  | .absent => false
  | .presentEmpty | .presentValue _ => true

/-- Forget placement while retaining the source value needed for delta classification. -/
def toDeltaPrior : FullDateTargetState → PriorFullDateTarget
  | .presentValue value => .filled value
  | .absent | .presentEmpty => .empty

end FullDateTargetState

namespace FullDateTargetOutcome

/-- Apply one checked full-Date outcome to an exact target cell. Accepted text creates or overwrites the value; every other outcome clears an existing target in place and leaves absence unchanged. -/
def applyTo : FullDateTargetOutcome → FullDateTargetState → FullDateTargetState
  | .accepted value, _ => .presentValue value
  | .noValue, prior => prior.clearValue
  | .errored _ _, prior => prior.clearValue
  | .poison _, prior => prior.clearValue

end FullDateTargetOutcome

end A12Kernel
