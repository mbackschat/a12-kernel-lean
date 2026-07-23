import A12Kernel.Elaboration.NumberEntityList
import A12Kernel.Elaboration.NumericStar
import A12Kernel.Semantics.FirstFilledValue

/-! # Checked Number entity-list `FirstFilledValue` -/

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

/-- Shared continuation-capable worker for one reached star slot. The caller supplies the already phase-correct Number classifier, so raw checked validation and a prepared addressed consumer share the same relevance and prefix scan. -/
def scanPartialValidationFirstFilledStateWith
    (checked : CheckedStarNumberSource model)
    (scope : ValidationRelevanceScope) (classify : Env → ValueListCell .number)
    : List Env → FirstFilledNumberScanState →
      FirstFilledNumberScanState ⊕ PartialValidationFirstFilledNumberResult
  | [], state => .inl state
  | environment :: environments, state =>
      if checked.source.cellRelevant scope environment then
        match state.step (classify environment) with
        | .continue next =>
            scanPartialValidationFirstFilledStateWith checked scope classify
              environments next
        | .done result => .inr (.evaluated result.asNumber)
      else
        .inr .nonRelevant

/-- Raw-cell compatibility wrapper for established partial-validation consumers. -/
def scanPartialValidationFirstFilledState (checked : CheckedStarNumberSource model)
    (scope : ValidationRelevanceScope) (read : Env → FieldId → RawCell) :=
  checked.scanPartialValidationFirstFilledStateWith scope
    (checked.valueListCell read)

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

private def scanCheckedFirstFilledNumberOperandWith
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (direct : FlatContext) (filterRead : Env → FieldId → CheckedCell)
    (classifyStar : CheckedStarNumberSource model → Env → ValueListCell .number)
    (state : FirstFilledNumberScanState) :
    CheckedFirstFilledNumberOperand model →
      Except StarAddressingError
        (FirstFilledNumberScanState ⊕ PartialValidationFirstFilledNumberResult)
  | .field source =>
      let relevant := scope.coversCell model source.declaration.path []
      if relevant then
        match state.step (source.field.valueListCell direct) with
        | .continue next => pure (.inl next)
        | .done result => pure (.inr (.evaluated result.asNumber))
      else
        pure (.inr .nonRelevant)
  | .star source => do
      let resolved ← source.source.path.resolve document outer
      pure (source.scanPartialValidationFirstFilledStateWith scope
        (classifyStar source)
        resolved.environments (state.enterSelection resolved.environments.isEmpty
          resolved.domain.hasOpenTail false))
  | .starHaving source => do
      let resolved ← source.source.source.path.resolve document outer
      let selected := source.having.selectEnvironments { read := filterRead } outer
        resolved.environments
      pure (source.source.scanPartialValidationFirstFilledStateWith scope
        (classifyStar source.source) selected
        (state.enterSelection selected.isEmpty resolved.domain.hasOpenTail true))

private def scanCheckedFirstFilledNumberOperandsWith
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (direct : FlatContext) (filterRead : Env → FieldId → CheckedCell)
    (classifyStar : CheckedStarNumberSource model → Env → ValueListCell .number) :
    List (CheckedFirstFilledNumberOperand model) → FirstFilledNumberScanState →
      Except StarAddressingError PartialValidationFirstFilledNumberResult
  | [], state => pure (.evaluated state.finish)
  | operand :: remaining, state => do
      match ← scanCheckedFirstFilledNumberOperandWith document outer scope direct
          filterRead classifyStar state operand with
      | .inl next =>
          scanCheckedFirstFilledNumberOperandsWith document outer scope direct
            filterRead classifyStar remaining next
      | .inr result => pure result

namespace CheckedNumberEntitySource

/-- Evaluate checked direct and independently resolved star slots in authored order. Relevance and filters are sampled only after every earlier slot has fallen through; no later topology or reader is touched after a terminal result. -/
def evaluatePartialValidation (checked : CheckedNumberEntitySource model)
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (directRead : RawFlatContext) (filterRead : Env → FieldId → CheckedCell)
    (starRead : Env → FieldId → RawCell) :
    Except StarAddressingError PartialValidationFirstFilledNumberResult :=
  scanCheckedFirstFilledNumberOperandsWith document outer scope
    (model.checkContext directRead) filterRead
    (fun source => source.valueListCell starRead) checked.operands {}

/-- Evaluate the same addressed validation prefix over one caller-prepared checked context. Direct and repeated cells therefore come from a coherent checked-document view, and structural addressing failure remains outside the semantic UNKNOWN channel. -/
def evaluateValidationIn (checked : CheckedNumberEntitySource model)
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (direct : FlatContext) (read : Env → FieldId → CheckedCell) :
    Except StarAddressingError PartialValidationFirstFilledNumberResult :=
  scanCheckedFirstFilledNumberOperandsWith document outer scope direct read
    (fun source => source.checkedValueListCellAt .validation read)
    checked.operands {}

/-- Evaluate the scalar computation fragment exactly when every checked operand is direct. The original source order and the shared stop-at-first scan are retained; no empty synthetic document is constructed for a repeated source. -/
def evaluateDirectComputationFirstFilled?
    (checked : CheckedNumberEntitySource model)
    (directRead : FieldId → CheckedCell) : Option FirstFilledNumberResult := do
  let (first, rest) ← checked.directFields?
  pure (match scanFirstFilledItems
      (fun field => field.valueListCellAt .computation { read := directRead })
      (first :: rest) {} with
    | .inl state => state.finish
    | .inr result => result.asNumber)

end CheckedNumberEntitySource

private def scanComputationFirstFilledNumberOperand
    (document : Document) (outer : Env) (direct : FlatContext)
    (filterRead starRead : Env → FieldId → CheckedCell)
    (state : FirstFilledScanState) :
    CheckedFirstFilledNumberOperand model →
      Except StarAddressingError
        (FirstFilledScanState ⊕ FirstFilledNumberResult)
  | .field source =>
      match state.step (source.field.valueListCellAt .computation direct) with
      | .continue next => pure (.inl next)
      | .done result => pure (.inr result.asNumber)
  | .star source => do
      let resolved ← source.source.path.resolve document outer
      match scanFirstFilledItems
          (source.checkedValueListCellAt .computation starRead)
          resolved.environments
          (state.enterSelection resolved.environments.isEmpty
            resolved.domain.hasOpenTail false) with
      | .inl next => pure (.inl next)
      | .inr result => pure (.inr result.asNumber)
  | .starHaving source => do
      let resolved ← source.source.source.path.resolve document outer
      match scanFilteredComputationFirstFilled source.having
          { read := filterRead } outer
          (source.source.checkedValueListCellAt .computation starRead)
          resolved.environments resolved.domain.hasOpenTail state with
      | .inl next => pure (.inl next)
      | .inr result => pure (.inr result.asNumber)

private def scanComputationFirstFilledNumberOperands
    (document : Document) (outer : Env) (direct : FlatContext)
    (filterRead starRead : Env → FieldId → CheckedCell) :
    List (CheckedFirstFilledNumberOperand model) → FirstFilledScanState →
      Except StarAddressingError FirstFilledNumberResult
  | [], state => pure state.finish
  | operand :: remaining, state => do
      match ← scanComputationFirstFilledNumberOperand document outer direct
          filterRead starRead state operand with
      | .inl next =>
          scanComputationFirstFilledNumberOperands document outer direct
            filterRead starRead remaining next
      | .inr result => pure result

namespace CheckedNumberEntitySource

/-- Evaluate the complete checked Number entity list at computation phase. Direct, plain-star, and filtered-star slots remain authored-order lazy; filtered stars delegate to the shared one-kept-successor traversal and the first selected value or formal poison hides every later slot. -/
def evaluateComputationFirstFilled
    (checked : CheckedNumberEntitySource model)
    (document : Document) (outer : Env)
    (directRead : FieldId → CheckedCell)
    (filterRead starRead : Env → FieldId → CheckedCell) :
    Except StarAddressingError FirstFilledNumberResult :=
  scanComputationFirstFilledNumberOperands document outer
    { read := directRead } filterRead starRead checked.operands {}

end CheckedNumberEntitySource

end A12Kernel
