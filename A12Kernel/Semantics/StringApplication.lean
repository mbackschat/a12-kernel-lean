import A12Kernel.Semantics.StringComputation

/-! # A12Kernel.Semantics.StringApplication — exact one-target String application

This capsule models only the placement-sensitive update of one already-addressed root target from `spec/01-data-model.md` §4.3 and `spec/09-computations.md` §2. It deliberately excludes document traversal, missing-ancestor creation, repeatable addressing, computation scheduling, untouched raw text, and multi-target application.
-/

namespace A12Kernel

/-- Exact state of one String-shaped target cell. This shared carrier preserves absent versus present-empty placement and DateFragment's original unconverted ingress identity from spec/09 §3.3. -/
inductive StringTargetState where
  | absent
  | presentEmpty
  | presentValue (value : StoredString)
  | presentUnconverted (value : StoredString)
  deriving Repr, DecidableEq

namespace StringTargetState

/-- Clear a present target's stored value in place without creating an absent target. -/
def clearValue : StringTargetState → StringTargetState
  | .absent => .absent
  | .presentEmpty | .presentValue _ | .presentUnconverted _ => .presentEmpty

/-- Apply one retained CLEARED result action. Classification already happened against the source, so the destination target exists empty even when it was absent. -/
def applyRetainedClear : StringTargetState → StringTargetState
  | .absent | .presentEmpty | .presentValue _ | .presentUnconverted _ => .presentEmpty

/-- Project away placement while retaining the stored value, when one exists. -/
def storedValue : StringTargetState → Option StoredString
  | .presentValue value | .presentUnconverted value => some value
  | .absent | .presentEmpty => none

/-- Return identity compatible with a computed value. The shared text carrier retains DateFragment's unconverted ingress distinction from spec/09 §3.3. -/
def computedValue : StringTargetState → Option StoredString
  | .presentValue value => some value
  | .absent | .presentEmpty | .presentUnconverted _ => none

/-- Report whether the target cell exists independently of whether it contains a value. -/
def isPresent : StringTargetState → Bool
  | .absent => false
  | .presentEmpty | .presentValue _ | .presentUnconverted _ => true

/-- Project exact state to the older delta-only prior vocabulary. Absent and present-empty deliberately become the same empty delta input. -/
def toDeltaPrior : StringTargetState → PriorStringTarget
  | .presentValue value => .filled value
  | .presentUnconverted value => .unconverted value
  | .absent | .presentEmpty => .empty

end StringTargetState

namespace StringTargetOutcome

/-- Apply one checked outcome to an exact target state. Accepted values create or overwrite the target; every outcome without an applied value clears an existing target in place and leaves an absent target absent. -/
def applyTo : StringTargetOutcome → StringTargetState → StringTargetState
  | .accepted value, _ => .presentValue value
  | .noValue, prior | .invalidNoValue, prior => prior.clearValue
  | .errored _ _, prior => prior.clearValue
  | .poison _, prior => prior.clearValue

end StringTargetOutcome

end A12Kernel
