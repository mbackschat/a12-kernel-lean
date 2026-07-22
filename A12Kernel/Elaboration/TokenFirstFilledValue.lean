import A12Kernel.Elaboration.TokenEntityList
import A12Kernel.Semantics.FirstFilledValue

/-! # Checked String/Enumeration `FirstFilledValue`

This consumer applies the common checked String/ordinary stored-Enumeration entity list to `FirstFilledValue`. It owns lazy authored-order scanning, relevance, filter selection, and token-family empty-result semantics; token admission and declaration-owned classification stay in `TokenEntityList`.
-/

namespace A12Kernel

abbrev SurfaceFirstFilledTokenOperand := SurfaceTokenEntityOperand
abbrev SurfaceFirstFilledTokenSource := SurfaceTokenEntitySource
abbrev CheckedFirstFilledTokenField := CheckedTokenField
abbrev CheckedFirstFilledTokenStarSource := CheckedTokenStarSource
abbrev CheckedFirstFilledTokenOperand := CheckedTokenEntityOperand
abbrev CheckedFirstFilledTokenSource := CheckedTokenEntitySource
abbrev FirstFilledTokenElabError := TokenEntityElabError

def firstDuplicateDirectFirstFilledTokenField? :=
  @firstDuplicateDirectTokenField?

def elaborateFirstFilledTokenSource := elaborateTokenEntitySource

/-- Partial validation keeps a reached nonrelevant token cell distinct from formal unavailability, exhaustion, and a selected token. -/
inductive PartialValidationFirstFilledTokenResult where
  | nonRelevant
  | evaluated (result : FirstFilledTokenResult)
  deriving Repr, DecidableEq

namespace CheckedTokenStarSource

/-- Continue one reached star slot in encounter order. Relevance is checked immediately before declaration-owned target classification. -/
def scanPartialFirstFilledState (checked : CheckedTokenStarSource model)
    (scope : ValidationRelevanceScope)
    (read : Env → FieldId → CheckedCell) :
    List Env → FirstFilledScanState →
      FirstFilledScanState ⊕ PartialValidationFirstFilledTokenResult
  | [], state => .inl state
  | environment :: environments, state =>
      if checked.source.cellRelevant scope environment then
        match state.step (checked.valueListCellAt .validation read environment) with
        | .continue next =>
            checked.scanPartialFirstFilledState scope read environments next
        | .done result => .inr (.evaluated result.asToken)
      else
        .inr .nonRelevant

end CheckedTokenStarSource

private def scanCheckedFirstFilledTokenOperand
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (directRead : FieldId → CheckedCell)
    (starRead : Env → FieldId → CheckedCell)
    (state : FirstFilledScanState) :
    CheckedTokenEntityOperand model →
      Except StarAddressingError
        (FirstFilledScanState ⊕ PartialValidationFirstFilledTokenResult)
  | .field source =>
      if scope.coversCell model source.declaration.path [] then
        match state.step (source.valueListCellAt .validation directRead) with
        | .continue next => pure (.inl next)
        | .done result => pure (.inr (.evaluated result.asToken))
      else
        pure (.inr .nonRelevant)
  | .star source => do
      let resolved ← source.source.path.resolve document outer
      let selected := match source.filter with
        | none => resolved.environments
        | some filter =>
            filter.condition.selectEnvironments { read := starRead } outer
              resolved.environments
      pure (source.scanPartialFirstFilledState scope starRead selected
        (state.enterSelection selected.isEmpty resolved.domain.hasOpenTail
          source.filter.isSome))

private def scanCheckedFirstFilledTokenOperands
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (directRead : FieldId → CheckedCell)
    (starRead : Env → FieldId → CheckedCell) :
    List (CheckedTokenEntityOperand model) → FirstFilledScanState →
      Except StarAddressingError PartialValidationFirstFilledTokenResult
  | [], _ => pure (.evaluated .noValue)
  | operand :: remaining, state => do
      match ← scanCheckedFirstFilledTokenOperand document outer scope directRead
          starRead state operand with
      | .inl next =>
          scanCheckedFirstFilledTokenOperands document outer scope directRead starRead
            remaining next
      | .inr result => pure result

namespace CheckedTokenEntitySource

/-- Evaluate checked direct and independently resolved star slots in authored order. Later topology, filters, relevance, and target reads remain unobserved after a terminal prefix. -/
def evaluatePartialFirstFilledValidation
    (checked : CheckedTokenEntitySource model)
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (directRead : FieldId → CheckedCell)
    (starRead : Env → FieldId → CheckedCell) :
    Except StarAddressingError PartialValidationFirstFilledTokenResult :=
  scanCheckedFirstFilledTokenOperands document outer scope directRead starRead
    checked.operands {}

end CheckedTokenEntitySource

end A12Kernel
