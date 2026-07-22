import A12Kernel.Semantics.DateConstructionNumeric
import A12Kernel.Semantics.DateTime
import A12Kernel.Semantics.Observation

/-! # Typed Date and DateTime numeric-component projection

This capsule consumes an already phase-classified typed Date or DateTime observation for `DayFromDate`, `MonthFromDate`, `QuarterFromDate`, or `YearFromDate`. Present values expose the selected component as fixed. Empty input substitutes numeric zero with symmetric fillability, while formal unavailability preserves its exact cause.

DateTime extraction deliberately projects its Date component and ignores the clock. Concrete parsing, authored source admission, partial-Date completion, the heterogeneous flat context, arithmetic composition, computation reads, and target application remain outside.
-/

namespace A12Kernel

namespace DateNumericPart

/-- Static format admission for one direct date-component extractor. Base Year supplements only the year component. Partial-known Date policy is an earlier model fact outside this flat declaration fragment. -/
def admittedBy (part : DateNumericPart) (hasBaseYear : Bool)
    (components : TemporalComponents) : Bool :=
  match part with
  | .day => components.day
  | .month | .quarter => components.month
  | .year => components.year || hasBaseYear

/-- Apply the shared validation-phase empty/unavailable projection before selecting a date component. The caller supplies the already-admitted value's calendar parts. -/
def fromObservation (part : DateNumericPart) (partsOf : α → DateParts) :
    CellObservation α → NumericOperand :=
  symmetricValidationNumericOperand
    (fun value => part.extract (partsOf value))

/-- Select a numeric component from a typed full-Date validation observation. -/
def fromFullDateObservation (part : DateNumericPart) :
    CellObservation FullDate → NumericOperand :=
  part.fromObservation (·.civil.parts)

/-- Select a numeric date component from a typed DateTime validation observation, ignoring its clock. -/
def fromDateTimeObservation (part : DateNumericPart) :
    CellObservation LocalDateTime → NumericOperand :=
  part.fromObservation (·.date.civil.parts)

end DateNumericPart

end A12Kernel
