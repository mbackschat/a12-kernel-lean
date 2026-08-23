import A12Kernel.Elaboration.DateRangeBound
import A12Kernel.Semantics.DateRangeComparison

/-! # Checked stored-versus-stored DateRange equality

This capsule owns equality and inequality between two direct stored DATE_RANGE fields: the
declaration-level component-set gate that decides admission, and the verdict over the shared
exact-or-yearless identity domain. The construction-bearing comparisons, bound extraction,
overlap, computation targets, and stored classification remain with their existing owners.
-/

namespace A12Kernel

/-- Static refusal while certifying one stored-versus-stored DateRange equality. -/
inductive DirectDateRangeComparisonElabError where
  | left (cause : DirectDateRangeElabError)
  | right (cause : DirectDateRangeElabError)
  | componentMismatch (left right : DateRangeInputFormat)
  deriving Repr, DecidableEq

namespace DirectDateRangeComparisonElabError

/-- Only the component-set refusal has an established Kernel diagnostic; the two operand refusals are local ingestion insufficiency. -/
def diagnostic? : DirectDateRangeComparisonElabError → Option KernelStaticDiagnostic
  | .componentMismatch _ _ => some .invalidCompareToDateRange
  | .left cause | .right cause => cause.diagnostic?

end DirectDateRangeComparisonElabError

/-- Two model-certified direct stored DateRange operands whose declared profiles expose the same date components, retained in authored order beside the authored equality direction. -/
structure CheckedDirectDateRangeComparison (model : FlatModel) where
  private mk ::
  left : CheckedDirectDateRange model
  right : CheckedDirectDateRange model
  comparison : EqualityOp
  componentsMatch : left.format.components = right.format.components

/-- Certify both operands and their shared component set. The gate reads the declared component set rather than the lexical spelling, so the two full-Date, the two month-only, and the two day-and-month spellings each cross in either authored order, and every other pair is refused identically for `==` and `!=`. -/
def elaborateDirectDateRangeComparison (model : FlatModel)
    (left right : FieldId) (comparison : EqualityOp) :
    Except DirectDateRangeComparisonElabError
      (CheckedDirectDateRangeComparison model) := do
  let leftSource ← elaborateDirectDateRange model left |>.mapError .left
  let rightSource ← elaborateDirectDateRange model right |>.mapError .right
  if hComponents : leftSource.format.components = rightSource.format.components then
    pure {
      left := leftSource
      right := rightSource
      comparison
      componentsMatch := hComponents }
  else
    throw (.componentMismatch leftSource.format rightSource.format)

/-- Defensive failure while reading one of the two stored operands. -/
inductive DirectDateRangeComparisonFault where
  | left (cause : DirectDateRangeFault)
  | right (cause : DirectDateRangeFault)
  deriving Repr, DecidableEq

/-- One-read result for Execute and Explain: both operand observations in authored order beside the verdict they produced. -/
structure DirectDateRangeComparisonResult where
  left : CellObservation DateRangeCellValue
  right : CellObservation DateRangeCellValue
  verdict : Verdict
  deriving Repr, DecidableEq

namespace CheckedDirectDateRangeComparison

/-- Read both operands through the shared direct DateRange route and compare their retained identity. Equal spellings of one component set are compared by identity rather than by stored text, so a resolved endpoint pair decides a full-Date crossing and the retained component pair decides a yearless one. An empty operand on either side leaves both directions unfired, and formal unavailability on either side is UNKNOWN. -/
def evaluate (checked : CheckedDirectDateRangeComparison model) (phase : Phase)
    (input : CheckedDocument model) :
    Except DirectDateRangeComparisonFault DirectDateRangeComparisonResult := do
  let left ← checked.left.evaluate phase input |>.mapError .left
  let right ← checked.right.evaluate phase input |>.mapError .right
  pure {
    left
    right
    verdict := checked.comparison.evalDateRangeCellValues
      left.asValidationSimpleOperand right.asValidationSimpleOperand }

end CheckedDirectDateRangeComparison

end A12Kernel
