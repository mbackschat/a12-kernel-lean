import A12Kernel.Semantics.CheckedEnumeration
import A12Kernel.Semantics.RepetitionNotUnique

/-! # A12Kernel.Semantics.EnumerationRepetitionNotUnique — checked key bridge

This bridge converts the shared resolved Enumeration operand classification into the established repetition-key component. It performs no second stored-token or category lookup.
-/

namespace A12Kernel

/-- Preserve the exact resolved Enumeration classification while changing only the RNU consumer vocabulary. -/
def ResolvedEnumerationProjection.asRepetitionKeyComponent
    (projection : ResolvedEnumerationProjection)
    (observation : CellObservation) : RepetitionKeyComponent :=
  match projection.resolveOperand observation with
  | .value token _ => .present (.token token)
  | .notEvaluated => .empty
  | .unknown cause => .unknown cause

/-- Project one already checked Enumeration value through the selected phase into an RNU key component. -/
def CheckedEnumerationProjection.classifyCheckedKeyAt
    (operand : CheckedEnumerationProjection) (phase : Phase)
    (cell : CheckedCell) : RepetitionKeyComponent :=
  operand.projection.asRepetitionKeyComponent (observeCell phase cell)

/-- Check one raw Enumeration value once, then delegate its validation observation to the checked-key boundary. -/
def CheckedEnumerationProjection.classifyRawKey
    (operand : CheckedEnumerationProjection) (raw : RawCell) : RepetitionKeyComponent :=
  operand.classifyCheckedKeyAt .validation (operand.declaration.checkRaw raw)

end A12Kernel
