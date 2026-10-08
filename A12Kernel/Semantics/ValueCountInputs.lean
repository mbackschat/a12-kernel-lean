import A12Kernel.Semantics.Observation
import A12Kernel.Semantics.ValueList

namespace A12Kernel

/-- The fixed storage token selected by an authored Boolean constant. -/
def booleanValueCountToken (expected : Bool) : String :=
  if expected then "true" else "false"

/-- Boolean/Confirm counting uses checked values, never stored or display tokens. -/
def booleanValueCountObservation : CellObservation → ValueListCell .token
  | .empty => .empty
  | .value (.bool value) => .present (booleanValueCountToken value)
  | .value (.conf true) => .present (booleanValueCountToken true)
  | .value _ => .unknown .malformed
  | .unknown cause | .poison cause => .unknown cause

/-- Project the phase observation; an impossible false Confirm fails closed. -/
def booleanValueCountCellAt (phase : Phase) (cell : CheckedCell) : ValueListCell .token :=
  booleanValueCountObservation (observeCell phase cell)

end A12Kernel
