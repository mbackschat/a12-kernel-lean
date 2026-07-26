import A12Kernel.Semantics.NumericTarget
import A12Kernel.Semantics.Observation

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

/-- A checked synthetic Number dependency cell with the same representation invariant as a document cell. The stored decimal remains in the rich producer outcome; a later numeric read observes its exact rational amount. -/
structure NumericDependencyCell where
  checked : CheckedCell
  wellFormed : checked.WellFormed

namespace NumericDependencyCell

/-- Embed the cause-free Number dependency observation in the common checked-cell read boundary. Invalid producer details have already been erased by `dependencyObservation`. -/
def ofObservation : NumericDependencyObservation → NumericDependencyCell
  | .empty => {
      checked := { rawPresent := false, parsed := none, findings := [] }
      wellFormed := by simp [CheckedCell.WellFormed] }
  | .value stored => {
      checked := {
        rawPresent := true
        parsed := some (.num stored.amount)
        findings := [] }
      wellFormed := by simp [CheckedCell.WellFormed] }
  | .poisoned => {
      checked := {
        rawPresent := true
        parsed := none
        findings := [.computedDependency] }
      wellFormed := by simp [CheckedCell.WellFormed] }

/-- Project one complete Number target outcome to the checked cell observed by a later computation. -/
def ofOutcome (outcome : NumericTargetOutcome) : NumericDependencyCell :=
  ofObservation outcome.dependencyObservation

end NumericDependencyCell

end A12Kernel
