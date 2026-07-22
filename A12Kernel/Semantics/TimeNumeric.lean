import A12Kernel.Semantics.DateTime
import A12Kernel.Semantics.NumericComparison

/-! # Typed Time and DateTime numeric-component projection

This capsule consumes an already phase-classified typed Time or DateTime observation for `HoursFromTime`, `MinutesFromTime`, or `SecondsFromTime`. Present values expose the selected clock component as fixed. Empty input reuses the temporal numeric symmetric-zero projection, while formal unavailability preserves its exact cause.

DateTime extraction deliberately projects its Time component and ignores the date. Concrete parsing, authored source admission, the heterogeneous flat context, arithmetic composition, computation reads, and target application remain outside.
-/

namespace A12Kernel

/-- The three direct numeric components exposed by a Time source. -/
inductive TimeNumericPart where
  | hour
  | minute
  | second
  deriving Repr, DecidableEq

namespace TimeNumericPart

/-- Select the named numeric component from an already-decoded time of day. -/
def extract (part : TimeNumericPart) (time : TimeOfDay) : Rat :=
  match part with
  | .hour => time.hour
  | .minute => time.minute
  | .second => time.second

/-- Apply the shared validation-phase temporal empty/unavailable projection before selecting a clock component. -/
def fromObservation (part : TimeNumericPart) (timeOf : α → TimeOfDay) :
    CellObservation α → NumericOperand :=
  symmetricValidationNumericOperand
    (fun value => part.extract (timeOf value))

/-- Select a numeric clock component from a typed Time validation observation. -/
def fromTimeObservation (part : TimeNumericPart) :
    CellObservation TimeOfDay → NumericOperand :=
  part.fromObservation id

/-- Select a numeric clock component from a typed DateTime validation observation, ignoring its date. -/
def fromDateTimeObservation (part : TimeNumericPart) :
    CellObservation LocalDateTime → NumericOperand :=
  part.fromObservation (·.time)

end TimeNumericPart

end A12Kernel
