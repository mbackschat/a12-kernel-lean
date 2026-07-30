import A12Kernel.Semantics.NumericDependency
import A12Kernel.Semantics.StringCascade

/-! # Cross-family computation dependency projections

This module contains only projections that cross a completed target-family boundary. The producer outcome remains rich and typed; each consumer receives its established checked-cell representation.
-/

namespace A12Kernel

namespace StringDependencyCell

/-- Convert a completed Number outcome into the String computation read it exposes. Accepted output retains canonical stored decimal text; every invalid Number outcome becomes the same cause-blind computed-dependency poison. -/
def ofNumericOutcome : NumericTargetOutcome → StringDependencyCell
  | .noValue => empty
  | .accepted stored => {
      checked := {
        rawPresent := true
        parsed := some (.str stored.render)
        findings := [] }
      wellFormed := by simp [CheckedCell.WellFormed] }
  | .rejected _ _ | .invalidNoValue _ | .inheritedPoison _ =>
      poison .computedDependency

end StringDependencyCell

end A12Kernel
