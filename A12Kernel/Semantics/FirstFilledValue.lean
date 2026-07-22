import A12Kernel.Semantics.NumericComputationResult
import A12Kernel.Semantics.ValueList

/-! # Resolved Number `FirstFilledValue`

This capsule scans one or more resolved Number field-list operands in authored order after expansion and `Having` filtering. It stops at the first present Number or first unavailable cell, enters each operand's filter only when that slot is reached, and keeps actual empty prefixes distinct from omitted declared tails. Its enter/step/finalize interface lets checked adapters interleave operator-specific relevance before each reached cell without duplicating the prefix scan.
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
  encounteredHaving : Bool := false
  omittedTailSeen : Bool := false
  deriving Repr, DecidableEq

/-- One shared scan step either continues after an empty cell or terminates at the first value or formal unavailability. -/
inductive FirstFilledNumberScanStep where
  | continue (state : FirstFilledNumberScanState)
  | done (result : FirstFilledNumberResult)
  deriving Repr, DecidableEq

namespace FirstFilledNumberScanState

/-- Enter one reached operand's metadata before inspecting its cells. A filter affects a later selected value; an omitted tail affects only the all-exhausted identity. -/
def enter (state : FirstFilledNumberScanState)
    (hasUninstantiatedTail hasHaving : Bool) : FirstFilledNumberScanState :=
  { state with
    encounteredHaving := state.encounteredHaving || hasHaving
    omittedTailSeen := state.omittedTailSeen || hasUninstantiatedTail }

/-- Enter one resolved operand before inspecting its cells. -/
def enterOperand (state : FirstFilledNumberScanState)
    (side : ResolvedValueListSide .number) : FirstFilledNumberScanState :=
  state.enter side.hasUninstantiatedTail side.hasHaving

/-- Consume one reached, relevant cell. Later consumers may place their own gates before invoking this step. -/
def step (state : FirstFilledNumberScanState) :
    ValueListCell .number → FirstFilledNumberScanStep
  | .present amount =>
      .done (.value amount (state.emptyBefore || state.encounteredHaving))
  | .empty => .continue { state with emptyBefore := true }
  | .unknown cause => .done (.unavailable cause)

/-- Close an exhausted scan with Number's zero identity and the exact accumulated missingness. -/
def finish (state : FirstFilledNumberScanState) : FirstFilledNumberResult :=
  .value 0 (state.emptyBefore || state.omittedTailSeen || state.encounteredHaving)

end FirstFilledNumberScanState

private def scanFirstFilledNumberCells :
    List (ValueListCell .number) → FirstFilledNumberScanState →
      FirstFilledNumberScanState ⊕ FirstFilledNumberResult
  | [], state => .inl state
  | cell :: cells, state =>
      match state.step cell with
      | .continue next => scanFirstFilledNumberCells cells next
      | .done result => .inr result

/-- A nonempty resolved Number operand list in authored encounter order. -/
structure FirstFilledNumberOperands where
  first : ResolvedValueListSide .number
  rest : List (ResolvedValueListSide .number)

private def scanFirstFilledNumberOperands :
    List (ResolvedValueListSide .number) → FirstFilledNumberScanState →
      FirstFilledNumberResult
  | [], state => state.finish
  | side :: sides, state =>
      match scanFirstFilledNumberCells side.cells (state.enterOperand side) with
      | .inl next => scanFirstFilledNumberOperands sides next
      | .inr result => result

/-- Select the first usable Number across nonempty resolved operand slots. Each slot's filter and cells are observed only after every earlier slot has fallen through. -/
def evalFirstFilledNumberOperands
    (operands : FirstFilledNumberOperands) : FirstFilledNumberResult :=
  scanFirstFilledNumberOperands (operands.first :: operands.rest) {}

/-- Select the first usable Number from one resolved operand. An explicit or uninstantiated empty selection contributes zero; the operand's resolved `Having` clause makes any selected value fillable. A checked adapter must mark an authored no-row star with `hasUninstantiatedTail`; the total state with no cells and neither missingness marker returns fixed zero but is not claimed authored-reachable. -/
def evalFirstFilledNumber
    (side : ResolvedValueListSide .number) : FirstFilledNumberResult :=
  evalFirstFilledNumberOperands { first := side, rest := [] }

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
