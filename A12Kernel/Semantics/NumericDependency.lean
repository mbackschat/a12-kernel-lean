import A12Kernel.Semantics.NumericTarget

/-! # One numeric outcome-to-dependency projection

This capsule preserves exactly what a later computation can observe from one already-computed Number target: clean emptiness, the exact stored decimal, or poison. It is not an applied document state, dependency graph, scheduler, or downstream expression evaluator.
-/

namespace A12Kernel

/-- Result exposed by one completed Number target to an explicitly later dependent computation. Poison is deliberately cause-free here: the complete producer outcome retains its attempted value and cause, while the dependent gate exposes only that the target is invalid. -/
inductive NumericDependencyObservation where
  | empty
  | value (stored : StoredNumber)
  | poisoned
  deriving Repr, DecidableEq

namespace NumericTargetOutcome

/-- Project the complete target outcome to its dependency meaning. A rejected attempt is never readable; calculation invalidity and inherited invalidity are likewise poison rather than clean emptiness. -/
def dependencyObservation : NumericTargetOutcome → NumericDependencyObservation
  | .noValue => .empty
  | .accepted stored => .value stored
  | .rejected _ _ | .invalidNoValue _ | .inheritedPoison _ => .poisoned

end NumericTargetOutcome

end A12Kernel
