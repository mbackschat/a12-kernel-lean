import A12Kernel.Semantics.NumericComputationResult
import A12Kernel.Semantics.ValueList

/-! # Resolved Number `FirstFilledValue`

This capsule admits one resolved field-list operand after ordered expansion, `Having` filtering, and partial-relevance classification. It scans only until the first present Number or first unavailable cell, while retaining whether an empty cell or that sole operand's filter made the selected result fillable. Authored multi-operand forms require ordered per-operand filter metadata and remain outside this boundary.
-/

namespace A12Kernel

/-- The resolved Number selection before a validation or computation consumer interprets it. `notGiven` retains the kernel-observed polarity contribution of an empty prefix, an uninstantiated empty selection, or a `Having` filter. -/
inductive FirstFilledNumberResult where
  | value (amount : Rat) (notGiven : Bool)
  | unavailable (cause : FormalCause)
  deriving Repr, DecidableEq

private def scanFirstFilledNumber :
    List (ValueListCell .number) → Bool → Bool → Bool →
      FirstFilledNumberResult
  | [], emptyBefore, hasUninstantiatedTail, hasHaving =>
      .value 0 (emptyBefore || hasUninstantiatedTail || hasHaving)
  | .present amount :: _, emptyBefore, _, hasHaving =>
      .value amount (emptyBefore || hasHaving)
  | .empty :: cells, _, hasUninstantiatedTail, hasHaving =>
      scanFirstFilledNumber cells true hasUninstantiatedTail hasHaving
  | .unknown cause :: _, _, _, _ =>
      .unavailable cause

/-- Select the first usable Number from one resolved operand. An explicit or uninstantiated empty selection contributes zero; the operand's resolved `Having` clause makes any selected value fillable. A checked adapter must mark an authored no-row star with `hasUninstantiatedTail`; the total state with no cells and neither missingness marker returns fixed zero but is not claimed authored-reachable. -/
def evalFirstFilledNumber
    (side : ResolvedValueListSide .number) : FirstFilledNumberResult :=
  scanFirstFilledNumber side.cells false
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
