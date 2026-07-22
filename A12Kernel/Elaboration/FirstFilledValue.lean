import A12Kernel.Elaboration.NumberEntityList
import A12Kernel.Elaboration.NumericStar
import A12Kernel.Semantics.FirstFilledValue

/-! # Checked Number-star `FirstFilledValue` -/

namespace A12Kernel

/-- Compatibility names preserve the established `FirstFilledValue` checked API while the common entity-list authoring mechanism now lives in `NumberEntityList`. -/
abbrev SurfaceFirstFilledNumberOperand := SurfaceNumberEntityOperand
abbrev SurfaceFirstFilledNumberSource := SurfaceNumberEntitySource
abbrev CheckedFirstFilledNumberField := CheckedNumberEntityField
abbrev CheckedFirstFilledNumberOperand := CheckedNumberEntityOperand
abbrev CheckedFirstFilledNumberSource := CheckedNumberEntitySource
abbrev FirstFilledNumberElabError := NumberEntityElabError

def firstDuplicateDirectFirstFilledNumberField? :=
  @firstDuplicateDirectNumberEntityField?

def elaborateFirstFilledNumberSource := elaborateNumberEntitySource

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

/-- Shared continuation-capable worker for one reached star slot. Falling through returns the accumulated scan state; a present, unavailable, or nonrelevant cell returns the terminal result. -/
def scanPartialValidationFirstFilledState (checked : CheckedStarNumberSource model)
    (scope : ValidationRelevanceScope) (read : Env → FieldId → RawCell)
    : List Env → FirstFilledNumberScanState →
      FirstFilledNumberScanState ⊕ PartialValidationFirstFilledNumberResult
  | [], state => .inl state
  | environment :: environments, state =>
      if checked.source.cellRelevant scope environment then
        match state.step (checked.valueListCell read environment) with
        | .continue next =>
            scanPartialValidationFirstFilledState checked scope read
              environments next
        | .done result => .inr (.evaluated result)
      else
        .inr .nonRelevant

/-- Finish one resolved star as a standalone partial-validation `FirstFilledValue` operand. -/
def scanPartialValidationFirstFilled (checked : CheckedStarNumberSource model)
    (scope : ValidationRelevanceScope) (read : Env → FieldId → RawCell)
    (environments : List Env) (state : FirstFilledNumberScanState) :
    PartialValidationFirstFilledNumberResult :=
  match checked.scanPartialValidationFirstFilledState scope read environments state with
  | .inl next => .evaluated next.finish
  | .inr result => result

/-- Scan one already-resolved nested Number star in encounter order, checking each concrete cell's relevance immediately before its declaration-owned classification. A terminal value or formal unavailability hides every later relevance and target read. -/
def selectedPartialValidationFirstFilled (checked : CheckedStarNumberSource model)
    (resolved : ResolvedStarTopology) (scope : ValidationRelevanceScope)
    (read : Env → FieldId → RawCell) : PartialValidationFirstFilledNumberResult :=
  scanPartialValidationFirstFilled checked scope read resolved.environments
    (({} : FirstFilledNumberScanState).enterSelection
      resolved.environments.isEmpty resolved.domain.hasOpenTail false)

/-- Resolve the canonical nested topology once, then run the order-aware partial-validation first-filled scan. -/
def resolvedPartialValidationFirstFilled (checked : CheckedStarNumberSource model)
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (read : Env → FieldId → RawCell) :
    Except StarAddressingError PartialValidationFirstFilledNumberResult := do
  let resolved ← checked.source.path.resolve document outer
  pure (checked.selectedPartialValidationFirstFilled resolved scope read)

end CheckedStarNumberSource

private def scanCheckedFirstFilledNumberOperand
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (direct : FlatContext) (filterRead : Env → FieldId → CheckedCell)
    (starRead : Env → FieldId → RawCell) (state : FirstFilledNumberScanState) :
    CheckedFirstFilledNumberOperand model →
      Except StarAddressingError
        (FirstFilledNumberScanState ⊕ PartialValidationFirstFilledNumberResult)
  | .field source =>
      let relevant := scope.coversCell model source.declaration.path []
      if relevant then
        match state.step (source.field.valueListCell direct) with
        | .continue next => pure (.inl next)
        | .done result => pure (.inr (.evaluated result))
      else
        pure (.inr .nonRelevant)
  | .star source => do
      let resolved ← source.source.path.resolve document outer
      pure (source.scanPartialValidationFirstFilledState scope starRead
        resolved.environments (state.enterSelection resolved.environments.isEmpty
          resolved.domain.hasOpenTail false))
  | .starHaving source => do
      let resolved ← source.source.source.path.resolve document outer
      let selected := source.having.selectEnvironments { read := filterRead } outer
        resolved.environments
      pure (source.source.scanPartialValidationFirstFilledState scope starRead selected
        (state.enterSelection selected.isEmpty resolved.domain.hasOpenTail true))

private def scanCheckedFirstFilledNumberOperands
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (direct : FlatContext) (filterRead : Env → FieldId → CheckedCell)
    (starRead : Env → FieldId → RawCell) :
    List (CheckedFirstFilledNumberOperand model) → FirstFilledNumberScanState →
      Except StarAddressingError PartialValidationFirstFilledNumberResult
  | [], state => pure (.evaluated state.finish)
  | operand :: remaining, state => do
      match ← scanCheckedFirstFilledNumberOperand document outer scope direct
          filterRead starRead state operand with
      | .inl next =>
          scanCheckedFirstFilledNumberOperands document outer scope direct
            filterRead starRead remaining next
      | .inr result => pure result

namespace CheckedNumberEntitySource

/-- Evaluate checked direct and independently resolved star slots in authored order. Relevance and filters are sampled only after every earlier slot has fallen through; no later topology or reader is touched after a terminal result. -/
def evaluatePartialValidation (checked : CheckedNumberEntitySource model)
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (directRead : RawFlatContext) (filterRead : Env → FieldId → CheckedCell)
    (starRead : Env → FieldId → RawCell) :
    Except StarAddressingError PartialValidationFirstFilledNumberResult :=
  scanCheckedFirstFilledNumberOperands document outer scope
    (model.checkContext directRead) filterRead starRead checked.operands {}

end CheckedNumberEntitySource

end A12Kernel
