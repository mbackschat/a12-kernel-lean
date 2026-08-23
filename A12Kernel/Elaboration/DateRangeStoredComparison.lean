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

/-- Two DateRange operands read at one rule locus that binds every repeatable level either of them
crosses. Both operands agree on the reading scope, because a leaf reads one row at a time; the
component gate is the scalar carrier's, unchanged. -/
structure CheckedDateRangeSourceComparison (model : FlatModel) where
  private mk ::
  left : CheckedDateRangeSource model
  right : CheckedDateRangeSource model
  comparison : EqualityOp
  scopesAgree : left.scope = right.scope
  componentsMatch : left.format.components = right.format.components

/-- Certify both operands at one reading scope. The refusal classes are the scalar carrier's, so an
operand crossing an unbound level is reported as its own resolution failure rather than as a
comparability failure. -/
def elaborateDateRangeSourceComparisonIn (model : FlatModel)
    (scope : List RepeatableLevel) (left right : FieldId)
    (comparison : EqualityOp) :
    Except DirectDateRangeComparisonElabError
      (CheckedDateRangeSourceComparison model) := do
  let leftSource ← elaborateDateRangeSourceIn model scope left |>.mapError .left
  let rightSource ←
    elaborateDateRangeSourceIn model scope right |>.mapError .right
  if hComponents :
      leftSource.format.components = rightSource.format.components then
    -- Both operands were certified at the same argument, so the scope equation is a defensive
    -- reconstruction rather than a reachable refusal.
    if hScopes : leftSource.scope = rightSource.scope then
      pure {
        left := leftSource
        right := rightSource
        comparison
        scopesAgree := hScopes
        componentsMatch := hComponents }
    else
      throw (.left .incoherentCore)
  else
    throw (.componentMismatch leftSource.format rightSource.format)

namespace CheckedDateRangeSourceComparison

/-- The verdict for two already-read operand observations. The read itself belongs to the consuming
leaf, which owns the row environment; this keeps the comparison identical to the scalar carrier's
so the two cannot drift on emptiness, unknown, or identity. -/
def verdictOf (checked : CheckedDateRangeSourceComparison model)
    (left right : CellObservation DateRangeCellValue) : Verdict :=
  checked.comparison.evalDateRangeCellValues
    left.asValidationSimpleOperand right.asValidationSimpleOperand

/-- Whether both retained declarations are still the model's own and still bound by the reading
group's scope. The checked condition re-establishes this at assembly, so a leaf cannot smuggle a
stale declaration or an unbound level past the locus gate. -/
def wellFormedIn (checked : CheckedDateRangeSourceComparison model)
    (scope : List RepeatableLevel) : Bool :=
  [checked.left, checked.right].all fun operand =>
    operand.scope == scope &&
      operand.declaration.repetitionBoundBy scope &&
      match model.lookupUniqueId operand.declaration.id with
      | .ok owned => owned == operand.declaration
      | .error _ => false

/-- The repeatable declarations this carrier reads, in authored order. -/
def repeatableDeclarations (checked : CheckedDateRangeSourceComparison model) :
    List FlatFieldDecl :=
  [checked.left, checked.right].filterMap fun operand =>
    if operand.declaration.repeatableScope.isEmpty then none
    else some operand.declaration

end CheckedDateRangeSourceComparison

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
