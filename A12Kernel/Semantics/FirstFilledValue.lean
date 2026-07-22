import A12Kernel.Semantics.NumericComputationResult
import A12Kernel.Semantics.ValueList

/-! # Resolved Number `FirstFilledValue`

This capsule admits one resolved field-list operand after ordered expansion and `Having` filtering. It scans only until the first present Number or first unavailable cell, while retaining whether an empty cell or that sole operand's filter made the selected result fillable. Its step/finalize interface lets checked adapters interleave operator-specific relevance before each reached cell without duplicating the prefix scan. Authored multi-operand forms require ordered per-operand filter metadata and remain outside this boundary.
-/

namespace A12Kernel

/-- The resolved Number selection before a validation or computation consumer interprets it. `notGiven` retains the kernel-observed polarity contribution of an empty prefix, an uninstantiated empty selection, or a `Having` filter. -/
inductive FirstFilledNumberResult where
  | value (amount : Rat) (notGiven : Bool)
  | unavailable (cause : FormalCause)
  deriving Repr, DecidableEq

/-- The prefix fact retained while an ordered Number first-filled scan can still change. -/
structure FirstFilledNumberScanState where
  emptyBefore : Bool := false
  deriving Repr, DecidableEq

/-- One shared scan step either continues after an empty cell or terminates at the first value or formal unavailability. -/
inductive FirstFilledNumberScanStep where
  | continue (state : FirstFilledNumberScanState)
  | done (result : FirstFilledNumberResult)
  deriving Repr, DecidableEq

namespace FirstFilledNumberScanState

/-- Consume one reached, relevant cell. Later consumers may place their own gates before invoking this step. -/
def step (state : FirstFilledNumberScanState) (hasHaving : Bool) :
    ValueListCell .number → FirstFilledNumberScanStep
  | .present amount => .done (.value amount (state.emptyBefore || hasHaving))
  | .empty => .continue { emptyBefore := true }
  | .unknown cause => .done (.unavailable cause)

/-- Close an exhausted scan with Number's zero identity and the exact accumulated missingness. -/
def finish (state : FirstFilledNumberScanState)
    (hasUninstantiatedTail hasHaving : Bool) : FirstFilledNumberResult :=
  .value 0 (state.emptyBefore || hasUninstantiatedTail || hasHaving)

end FirstFilledNumberScanState

private def scanFirstFilledNumber :
    List (ValueListCell .number) → FirstFilledNumberScanState → Bool → Bool →
      FirstFilledNumberResult
  | [], state, hasUninstantiatedTail, hasHaving =>
      state.finish hasUninstantiatedTail hasHaving
  | cell :: cells, state, hasUninstantiatedTail, hasHaving =>
      match state.step hasHaving cell with
      | .continue next =>
          scanFirstFilledNumber cells next hasUninstantiatedTail hasHaving
      | .done result => result

/-- Select the first usable Number from one resolved operand. An explicit or uninstantiated empty selection contributes zero; the operand's resolved `Having` clause makes any selected value fillable. A checked adapter must mark an authored no-row star with `hasUninstantiatedTail`; the total state with no cells and neither missingness marker returns fixed zero but is not claimed authored-reachable. -/
def evalFirstFilledNumber
    (side : ResolvedValueListSide .number) : FirstFilledNumberResult :=
  scanFirstFilledNumber side.cells {}
    side.hasUninstantiatedTail side.hasHaving

namespace FirstFilledNumberResult

/-- Validation observes the selected amount together with the retained not-given/fillability classification. -/
def asValidationOperand : FirstFilledNumberResult → NumericOperand
  | .value amount true => .value amount .both
  | .value amount false => .value amount .fixed
  | .unavailable cause => .unknown cause

/-- Computation consumes the selected amount but treats reached formal invalidity as poison. -/
def asComputationResult : FirstFilledNumberResult → NumericComputationResult
  | .value amount _ => .value amount
  | .unavailable cause => .poison cause

end FirstFilledNumberResult

end A12Kernel
