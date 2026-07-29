import A12Kernel.Elaboration.TemporalTargetPolicy
import A12Kernel.Semantics.TimeConstruction

/-! # Checked `Time(...)` target execution

This capsule carries an already-resolved `Time(...)` result through one exact `HH:mm:ss` target. The clock remains zone-free; the runtime's 1970 date is only a transport representation. Source-relative result classification, application, wider formats, repeatable targets, scheduling, and message construction remain separate.
-/

namespace A12Kernel

namespace TimeConstructionResult

/-- Forget construction-only no-value reasons while retaining value and poison. -/
def asTimeComputationResult : TimeConstructionResult → TimeComputationResult
  | .value time => .value time
  | .unavailable cause => .poison cause
  | .incomplete | .unreal | .nonRelevant => .noValue

end TimeConstructionResult

namespace CheckedTimeTarget

/-- Render one selected Time result; every admitted clock passes the exact target basic check. -/
def evaluate (target : CheckedTimeTarget model) :
    TimeComputationResult → TimeTargetOutcome
  | .noValue => .noValue
  | .poison cause => .poison cause
  | .value time => .accepted (target.format.render time)

end CheckedTimeTarget

end A12Kernel
