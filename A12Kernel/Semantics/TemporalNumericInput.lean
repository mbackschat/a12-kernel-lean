import A12Kernel.Semantics.FlatValidation
import A12Kernel.Semantics.FullDateInputFormat

/-! # Numeric extraction from complete and partially known temporal fields -/

namespace A12Kernel

/-- Read the selected component without completing a partial Date to an invented endpoint.
The owning declaration gate admits only guaranteed components (spec/05 §3, KF529). -/
def TemporalNumericPart.projectStored? (part : TemporalNumericPart) (field : FlatTemporalField)
    (partialFormat : Option FullDateTargetFormat) : Value → Option Rat
  | .temporal value => if field.holdsValue value then part.project? value else none
  | .partialDate text => do
      let .date part := part | none
      let format ← partialFormat
      part.extract <$> format.parseComponents? text
  | _ => none

/-- Share empty substitution and exact formal causes across ordinary and filtered extraction.
Structural payload faults remain malformed; computation can retain its stricter fault boundary. -/
def CellObservation.asStoredTemporalNumericOperand (observation : CellObservation)
    (field : FlatTemporalField) (part : TemporalNumericPart)
    (partialFormat : Option FullDateTargetFormat := none) : NumericOperand :=
  match observation with
  | .empty => .value 0 .both
  | .unknown cause | .poison cause => .unknown cause
  | .value payload => match part.projectStored? field partialFormat payload with
    | some amount => .value amount .fixed
    | none => .unknown .malformed

end A12Kernel
