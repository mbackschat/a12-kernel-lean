import A12Kernel.Elaboration.NumericStar
import A12Kernel.Elaboration.StarNumber
import A12Kernel.Semantics.FirstFilledValue

/-! # Checked Number-star `FirstFilledValue` -/

namespace A12Kernel

/-- Partial validation keeps a reached nonrelevant cell distinct from both formal unavailability and an evaluated first-filled result. -/
inductive PartialValidationFirstFilledNumberResult where
  | nonRelevant
  | evaluated (result : FirstFilledNumberResult)
  deriving Repr, DecidableEq

namespace CheckedNumericStarSource

/-- Evaluate the checked ordered star through the existing prefix-terminating Number consumer. -/
def evaluateFirstFilled (checked : CheckedNumericStarSource model)
    (raw : RawSingleGroupContext) : Except NumericStarContextError FirstFilledNumberResult := do
  checked.validateContext raw
  pure (evalFirstFilledNumber (checked.resolvedValueSide raw))

end CheckedNumericStarSource

namespace CheckedStarNumberSource

/-- Shared recursive worker for order-aware partial-validation Number first-filled evaluation. -/
def scanPartialValidationFirstFilled (checked : CheckedStarNumberSource model)
    (scope : ValidationRelevanceScope) (read : Env → FieldId → RawCell)
    : List Env → FirstFilledNumberScanState → PartialValidationFirstFilledNumberResult
  | [], state => .evaluated state.finish
  | environment :: environments, state =>
      if checked.source.cellRelevant scope environment then
        match state.step (checked.valueListCell read environment) with
        | .continue next =>
            scanPartialValidationFirstFilled checked scope read
              environments next
        | .done result => .evaluated result
      else
        .nonRelevant

/-- Scan one already-resolved nested Number star in encounter order, checking each concrete cell's relevance immediately before its declaration-owned classification. A terminal value or formal unavailability hides every later relevance and target read. -/
def selectedPartialValidationFirstFilled (checked : CheckedStarNumberSource model)
    (resolved : ResolvedStarTopology) (scope : ValidationRelevanceScope)
    (read : Env → FieldId → RawCell) : PartialValidationFirstFilledNumberResult :=
  scanPartialValidationFirstFilled checked scope read resolved.environments
    (({} : FirstFilledNumberScanState).enter resolved.domain.hasOpenTail false)

/-- Resolve the canonical nested topology once, then run the order-aware partial-validation first-filled scan. -/
def resolvedPartialValidationFirstFilled (checked : CheckedStarNumberSource model)
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (read : Env → FieldId → RawCell) :
    Except StarAddressingError PartialValidationFirstFilledNumberResult := do
  let resolved ← checked.source.path.resolve document outer
  pure (checked.selectedPartialValidationFirstFilled resolved scope read)

end CheckedStarNumberSource

end A12Kernel
