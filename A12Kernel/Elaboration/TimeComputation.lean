import A12Kernel.Elaboration.TemporalValueComputationApplication
import A12Kernel.Elaboration.TemporalTargetPolicy
import A12Kernel.Semantics.TimeConstruction

/-! # Checked `Time(...)` target execution

This capsule carries an already-resolved `Time(...)` result through one exact `HH:mm:ss` target, source-relative result classification, and exact scalar application. The clock remains zone-free; the runtime's 1970 date is only a transport representation. Wider formats, repeatable targets, scheduling, and message construction remain separate.
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

/-- Exact caller-supplied Time destination. -/
abbrev TimeComputationDestination :=
  TemporalComputationDestination StoredTime

namespace TimeComputationDestination

/-- Specialize the existing one-target transition at one Time field. -/
def applyOutcome (destination : TimeComputationDestination)
    (target : FieldId) (outcome : TimeTargetOutcome) :
    TimeComputationDestination :=
  TemporalComputationDestination.update destination target
    (outcome.applyTo (destination target))

end TimeComputationDestination

namespace TimeComputationRunView

/-- Targets consumed by Time application; unchanged successes and residual messages are absent. -/
def actionTargets (view : TimeComputationRunView ResidualMessage) :
    List FieldId :=
  TemporalValueComputationRunView.actionTargets view

/-- Apply clears before changed values; unchanged successes and residual messages never mutate the destination. -/
def applyTo (view : TimeComputationRunView ResidualMessage)
    (destination : TimeComputationDestination) :
    Except TemporalValueComputationApplicationError
      TimeComputationDestination :=
  TemporalValueComputationRunView.applyTo view destination
    TimeComputationDestination.applyOutcome .noValue .accepted

end TimeComputationRunView

end A12Kernel
