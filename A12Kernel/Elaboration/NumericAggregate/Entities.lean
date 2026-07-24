import A12Kernel.Elaboration.NumericAggregate.Fields

/-! # Checked mixed entity-list numeric aggregates and value counts -/

namespace A12Kernel

private def appendNumericSumSide
    (left right : ResolvedNumericSumSide) : ResolvedNumericSumSide :=
  { cells := left.cells ++ right.cells
    uninstantiatedSignedness :=
      left.uninstantiatedSignedness ++ right.uninstantiatedSignedness
    hasHaving := left.hasHaving || right.hasHaving }

private structure ResolvedNumberEntityAggregateSides where
  values : ResolvedValueListSide .number := {
    cells := [], hasUninstantiatedTail := false, hasHaving := false }
  sum : ResolvedNumericSumSide := {
    cells := [], uninstantiatedSignedness := [], hasHaving := false }

namespace ResolvedNumberEntityAggregateSides

private def append (accumulated : ResolvedNumberEntityAggregateSides)
    (declarationSigned : Bool) (side : ResolvedValueListSide .number) :
    ResolvedNumberEntityAggregateSides :=
  { values := accumulated.values.append side
    sum := appendNumericSumSide accumulated.sum
      (side.toNumericSumSide declarationSigned) }

private def evaluate (accumulated : ResolvedNumberEntityAggregateSides)
    (op : NumericAggregateOp) : NumericOperand :=
  match op with
  | .sum => evalDeclaredNumericSumAggregate accumulated.sum
  | .minimum => evalNumericExtremumAggregate .minimum accumulated.values
  | .maximum => evalNumericExtremumAggregate .maximum accumulated.values
  | .distinctCount => evalNumericDistinctCountAggregate accumulated.values

end ResolvedNumberEntityAggregateSides

namespace CheckedNumberEntityField

/-- Classify one checked direct slot through the declaration-owned Number reader at the caller's phase. -/
def resolvedAggregateSideAt (checked : CheckedNumberEntityField model)
    (phase : Phase) (context : FlatContext) : ResolvedValueListSide .number :=
  { cells := [checked.field.valueListCellAt phase context]
    hasUninstantiatedTail := false
    hasHaving := false }

/-- Validation specialization retained for established aggregate consumers. -/
def resolvedAggregateSide (checked : CheckedNumberEntityField model)
    (context : FlatContext) : ResolvedValueListSide .number :=
  checked.resolvedAggregateSideAt .validation context

end CheckedNumberEntityField

namespace CheckedNumberEntityOperand

private def resolveCheckedDocumentNumberCells
    (document : CheckedDocument model) (phase : Phase)
    (field : FlatNumberField) :
    List Env → List (ValueListCell .number) →
      Except CheckedAddressingError
        (Sum (List (ValueListCell .number)) NumericOperand)
  | [], reversed => pure (.inl reversed.reverse)
  | environment :: remaining, reversed => do
      match ← document.numberValueListCellAt phase environment field with
      | .unknown cause => pure (.inr (.unknown cause))
      | cell =>
          resolveCheckedDocumentNumberCells document phase field
            remaining (cell :: reversed)

private def resolvedCheckedDocumentSide
    (document : CheckedDocument model) (phase : Phase)
    (field : FlatNumberField)
    (environments : List Env) (hasUninstantiatedTail hasHaving : Bool) :
    Except CheckedAddressingError
      (Sum (ResolvedValueListSide .number) NumericOperand) := do
  match ← resolveCheckedDocumentNumberCells document phase field
      environments [] with
  | .inl cells => pure (.inl { cells, hasUninstantiatedTail, hasHaving })
  | .inr result => pure (.inr result)

/-- Resolve exactly one authored slot. Plain and filtered stars reuse the general checked topology and filter owners; direct fields reuse the checked flat Number reader. -/
def resolvedAggregateSide (checked : CheckedNumberEntityOperand model)
    (document : Document) (outer : Env) (direct : FlatContext)
    (filterRead : Env → FieldId → CheckedCell)
    (starRead : Env → FieldId → RawCell) :
    Except StarAddressingError (ResolvedValueListSide .number) :=
  match checked with
  | .field source => pure (source.resolvedAggregateSide direct)
  | .star source => source.resolvedValueSide document outer starRead
  | .starHaving source =>
      source.resolvedValueSide document outer filterRead starRead

/-- Resolve one full-validation aggregate slot from a caller-prepared checked view. Direct and repeated cells therefore share one validation phase without resampling declaration checks. -/
def resolvedValidationAggregateSideIn
    (checked : CheckedNumberEntityOperand model)
    (document : Document) (outer : Env) (direct : FlatContext)
    (read : Env → FieldId → CheckedCell) :
    Except StarAddressingError (ResolvedValueListSide .number) :=
  match checked with
  | .field source =>
      pure (source.resolvedAggregateSideAt .validation direct)
  | .star source => do
      let resolved ← source.source.path.resolve document outer
      pure (resolved.toResolvedSide
        (source.checkedValueListCellAt .validation read))
  | .starHaving source =>
      source.source.source.resolvedValidationHavingValueListSide
        document outer source.having read
        (source.source.checkedValueListCellAt .validation read)

/-- Resolve one aggregate slot at computation phase. Filtered stars use the runtime iterator's one-kept-successor lookahead and stop at the first reached filter or target poison; plain stars and direct fields preserve the same checked-cell classification without validation's unknown-as-drop projection. -/
def resolvedComputationAggregateSide
    (checked : CheckedNumberEntityOperand model)
    (document : Document) (outer : Env) (direct : FlatContext)
    (filterRead starRead : Env → FieldId → CheckedCell) :
    Except StarAddressingError
      (Sum (ResolvedValueListSide .number) NumericOperand) :=
  match checked with
  | .field source =>
      pure (.inl (source.resolvedAggregateSideAt .computation direct))
  | .star source => do
      let resolved ← source.source.path.resolve document outer
      pure (.inl (resolved.toResolvedSide
        (source.checkedValueListCellAt .computation starRead)))
  | .starHaving source => do
      let resolved ← source.source.source.path.resolve document outer
      let filterContext : CorrelationContext := { read := filterRead }
      let consume := fun cells environment =>
        match source.source.checkedValueListCellAt .computation
            starRead environment with
        | .unknown cause => .inr cause
        | cell => .inl (cell :: cells)
      match source.having.scanComputation filterContext outer consume
          resolved.environments [] with
      | .exhausted reversed =>
          pure (.inl {
            cells := reversed.reverse
            hasUninstantiatedTail := resolved.domain.hasOpenTail
            hasHaving := true })
      | .terminated cause | .poison cause =>
          pure (.inr (.unknown cause))

/-- Resolve one validation aggregate slot from the immutable checked document. Validation filters evaluate every candidate before the first target classification; target reads then stop at the first formal cause. -/
def resolvedCheckedDocumentValidationAggregateSide
    (checked : CheckedNumberEntityOperand model)
    (document : CheckedDocument model) (outer : Env) :
    Except CheckedAddressingError
      (Sum (ResolvedValueListSide .number) NumericOperand) :=
  do
    let side :=
      (← checked.resolveCheckedValidationOperand document outer)
        |>.valueListSideAt .validation
    match side.available with
    | .error cause => pure (.inr (.unknown cause))
    | .ok () => pure (.inl side)

/-- Resolve one computation aggregate slot from the same checked document. A filtered slot retains one-kept-successor lookahead and keeps structural target/filter failure outside formal poison. -/
def resolvedCheckedDocumentComputationAggregateSide
    (checked : CheckedNumberEntityOperand model)
    (document : CheckedDocument model) (outer : Env) :
    Except CheckedAddressingError
      (Sum (ResolvedValueListSide .number) NumericOperand) :=
  match checked with
  | .field source =>
      resolvedCheckedDocumentSide document .computation source.field
        [[]] false false
  | .star source => do
      let resolved ←
        (source.source.path.resolve document.source.toDocument outer)
          |>.mapError .addressing
      resolvedCheckedDocumentSide document .computation source.field
        resolved.environments resolved.domain.hasOpenTail false
  | .starHaving source => do
      let resolved ←
        (source.source.source.path.resolve document.source.toDocument outer)
          |>.mapError .addressing
      let consume := fun cells environment => do
        match ← document.numberValueListCellAt .computation environment
            source.source.field with
        | .unknown cause => pure (.inr cause)
        | cell => pure (.inl (cell :: cells))
      match ← source.having.scanComputationResolving
          document.resolvingCorrelationContext outer consume
          resolved.environments [] with
      | .exhausted reversed =>
          pure (.inl {
            cells := reversed.reverse
            hasUninstantiatedTail := resolved.domain.hasOpenTail
            hasHaving := true })
      | .terminated cause | .poison cause =>
          pure (.inr (.unknown cause))

/-- Resolve one unfiltered partial-validation slot from the checked document. Direct nonrelevance precedes its cell query; star topology precedes the established all-rows gate; a local filter remains a rule-level skip. -/
def resolvedCheckedDocumentPartialAggregateSide
    (checked : CheckedNumberEntityOperand model)
    (document : CheckedDocument model) (outer : Env)
    (scope : ValidationRelevanceScope) :
    Except CheckedAddressingError
      (Sum (ResolvedValueListSide .number)
        PartialValidationNumberAggregateResult) :=
  match checked with
  | .field source =>
      if scope.coversCell model source.declaration.path [] then do
        match ← resolvedCheckedDocumentSide document .validation source.field
            [[]] false false with
        | .inl side => pure (.inl side)
        | .inr result => pure (.inr (.evaluated result))
      else
        pure (.inr .nonRelevant)
  | .star source => do
      let resolved ←
        (source.source.path.resolve document.source.toDocument outer)
          |>.mapError .addressing
      if source.source.allRowsRelevant scope then do
        match ← resolvedCheckedDocumentSide document .validation source.field
            resolved.environments resolved.domain.hasOpenTail false with
        | .inl side => pure (.inl side)
        | .inr result => pure (.inr (.evaluated result))
      else
        pure (.inr .nonRelevant)
  | .starHaving _ => pure (.inr .skippedHaving)

/-- Resolve one partial-validation aggregate slot. Direct fields require their concrete cell; ordinary stars require complete wildcard/ancestor coverage and retain the established topology-produced side unchanged. Filtered slots return the rule-level skip marker without evaluating their filter. -/
def resolvedPartialAggregateSide (checked : CheckedNumberEntityOperand model)
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (direct : FlatContext) (starRead : Env → FieldId → RawCell) :
    Except StarAddressingError
      (Sum (ResolvedValueListSide .number)
        PartialValidationNumberAggregateResult) :=
  match checked with
  | .field source =>
      if scope.coversCell model source.declaration.path [] then
        pure (.inl (source.resolvedAggregateSide direct))
      else
        pure (.inr .nonRelevant)
  | .star source => do
      match ← source.resolvedPartialAllRowsValueSide document outer scope starRead with
      | .nonRelevant => pure (.inr .nonRelevant)
      | .relevant side => pure (.inl side)
  | .starHaving _ => pure (.inr .skippedHaving)

end CheckedNumberEntityOperand

namespace CheckedNumberEntitySource

/-- Run the sole authored-order aggregate scan after the caller selects the phase-specific operand resolver. Validation and computation therefore share termination, declaration metadata, accumulation, and final operator dispatch. -/
private def evaluateAggregateWith (checked : CheckedNumberEntitySource model)
    (op : NumericAggregateOp)
    (resolve : CheckedNumberEntityOperand model →
      Except Error
        (Sum (ResolvedValueListSide .number) NumericOperand)) :
    Except Error NumericOperand := do
  match ← scanResolvedValueListOperands
      (state := ResolvedNumberEntityAggregateSides)
      (terminal := NumericOperand)
      resolve
      (fun cause => .unknown cause)
      (fun accumulated operand side =>
        accumulated.append operand.declarationSigned side)
      checked.operands {} with
  | .inl accumulated => pure (accumulated.evaluate op)
  | .inr result => pure result

/-- Evaluate a checked ordinary Number entity-list aggregate in authored slot order. Each wildcard occurrence resolves independently. A formally unavailable reached cell returns immediately, so no later star topology, filter, or target reader is sampled. -/
def evaluateAggregate (checked : CheckedNumberEntitySource model)
    (op : NumericAggregateOp) (document : Document) (outer : Env)
    (directRead : RawFlatContext)
    (filterRead : Env → FieldId → CheckedCell)
    (starRead : Env → FieldId → RawCell) :
    Except StarAddressingError NumericOperand :=
  let direct := model.checkContext directRead
  checked.evaluateAggregateWith op fun operand => do
    pure (.inl (← operand.resolvedAggregateSide document outer direct
      filterRead starRead))

/-- Evaluate the same full-validation fold over one caller-prepared checked scalar/repeatable view. Every slot preserves authored order, validation-phase UNKNOWN, declaration-specific missing polarity, and structural address failure. -/
def evaluateValidationAggregateIn (checked : CheckedNumberEntitySource model)
    (op : NumericAggregateOp) (document : Document) (outer : Env)
    (direct : FlatContext) (read : Env → FieldId → CheckedCell) :
    Except StarAddressingError NumericOperand := do
  checked.evaluateAggregateWith op fun operand => do
    pure (.inl (← operand.resolvedValidationAggregateSideIn
      document outer direct read))

/-- Evaluate a checked ordinary Number entity-list aggregate at computation phase. Operand slots remain authored-order lazy, and each filtered star delegates to the shared one-kept-successor iterator rather than selecting its complete row set eagerly. -/
def evaluateComputationAggregate (checked : CheckedNumberEntitySource model)
    (op : NumericAggregateOp) (document : Document) (outer : Env)
    (directRead : FieldId → CheckedCell)
    (filterRead starRead : Env → FieldId → CheckedCell) :
    Except StarAddressingError NumericOperand :=
  let direct : FlatContext := { read := directRead }
  checked.evaluateAggregateWith op fun operand =>
    operand.resolvedComputationAggregateSide document outer direct
      filterRead starRead

/-- Evaluate validation-phase aggregate accumulation from one immutable model-certified checked document. -/
def evaluateCheckedDocumentValidationAggregate
    (checked : CheckedNumberEntitySource model)
    (op : NumericAggregateOp) (document : CheckedDocument model)
    (outer : Env) : Except CheckedAddressingError NumericOperand :=
  checked.evaluateAggregateWith op fun operand =>
    operand.resolvedCheckedDocumentValidationAggregateSide document outer

/-- Evaluate computation-phase aggregate accumulation from the same checked document without changing filter or poison timing. -/
def evaluateCheckedDocumentComputationAggregate
    (checked : CheckedNumberEntitySource model)
    (op : NumericAggregateOp) (document : CheckedDocument model)
    (outer : Env) : Except CheckedAddressingError NumericOperand :=
  checked.evaluateAggregateWith op fun operand =>
    operand.resolvedCheckedDocumentComputationAggregateSide document outer

/-- Run the common partial aggregate fold after the caller selects a raw or checked-document operand resolver. The source-wide filter skip remains before every resolver call. -/
def evaluatePartialAggregateWith
    (checked : CheckedNumberEntitySource model) (op : NumericAggregateOp)
    (resolve : CheckedNumberEntityOperand model →
      Except Error (Sum (ResolvedValueListSide .number)
        PartialValidationNumberAggregateResult)) :
    Except Error PartialValidationNumberAggregateResult :=
  if checked.hasHaving then
    pure .skippedHaving
  else do
    match ← scanResolvedValueListOperands
        (state := ResolvedNumberEntityAggregateSides)
        (terminal := PartialValidationNumberAggregateResult)
        resolve
        (fun cause => .evaluated (.unknown cause))
        (fun accumulated operand side =>
          accumulated.append operand.declarationSigned side)
        checked.operands {} with
    | .inl accumulated => pure (.evaluated (accumulated.evaluate op))
    | .inr result => pure result

/-- Evaluate an unfiltered checked Number aggregate under partial validation. A locally visible `Having` skips the rule before topology, relevance, or reads. Otherwise direct slots use concrete relevance and every star uses the established all-rows wildcard/ancestor gate, with the same authored-order early termination as full validation. A containing whole condition must still discover filters across every branch before invoking any leaf. -/
def evaluatePartialAggregate (checked : CheckedNumberEntitySource model)
    (op : NumericAggregateOp) (document : Document) (outer : Env)
    (scope : ValidationRelevanceScope) (directRead : RawFlatContext)
    (starRead : Env → FieldId → RawCell) :
    Except StarAddressingError PartialValidationNumberAggregateResult :=
  checked.evaluatePartialAggregateWith op fun operand =>
    operand.resolvedPartialAggregateSide document outer scope
      (model.checkContext directRead) starRead

/-- Evaluate partial aggregate accumulation from the immutable checked document with the same filter-skip and relevance gates. -/
def evaluateCheckedDocumentPartialAggregate
    (checked : CheckedNumberEntitySource model)
    (op : NumericAggregateOp) (document : CheckedDocument model)
    (outer : Env) (scope : ValidationRelevanceScope) :
    Except CheckedAddressingError PartialValidationNumberAggregateResult :=
  checked.evaluatePartialAggregateWith op fun operand =>
    operand.resolvedCheckedDocumentPartialAggregateSide document outer scope

/-- Evaluate numeric `NumberOfValueInFields` without an addressed document exactly when every checked operand is direct. This scalar compatibility path never invents topology for a repeatable source. -/
def evaluateDirectValueCountAt? (checked : CheckedNumberEntitySource model)
    (expected : Rat) (phase : Phase) (context : FlatContext) :
    Option NumericOperand := do
  let (first, rest) ← checked.directFields?
  pure (evalValueCountAggregate expected {
    cells := (first :: rest).map fun field => {
      cell := field.valueListCellAt phase context
      selectedByHaving := false }
    hasUninstantiatedTail := false
    hasHaving := false })

/-- Run `NumberOfValueInFields` over the existing checked Number entity-list route. Unlike the other aggregate folds, this accumulator retains whether each matching cell came through a filter because only such a current match can later disappear. -/
private def evaluateValueCountWith (checked : CheckedNumberEntitySource model)
    (expected : Rat)
    (resolve : CheckedNumberEntityOperand model →
      Except Error
        (Sum (ResolvedValueListSide .number) NumericOperand)) :
    Except Error NumericOperand := do
  match ← scanResolvedValueListOperands
      (state := ResolvedValueCountSide .number)
      (terminal := NumericOperand)
      resolve
      (fun cause => .unknown cause)
      (fun accumulated _ side => accumulated.appendResolved side)
      checked.operands ResolvedValueCountSide.empty with
  | .inl accumulated => pure (evalValueCountAggregate expected accumulated)
  | .inr result => pure result

/-- Evaluate numeric `NumberOfValueInFields` in full validation from one already-prepared checked scalar/repeatable view. -/
def evaluateValueCountValidationIn (checked : CheckedNumberEntitySource model)
    (expected : Rat) (document : Document) (outer : Env)
    (direct : FlatContext) (read : Env → FieldId → CheckedCell) :
    Except StarAddressingError NumericOperand :=
  checked.evaluateValueCountWith expected fun operand => do
    pure (.inl (← operand.resolvedValidationAggregateSideIn
      document outer direct read))

/-- Evaluate numeric `NumberOfValueInFields` at computation phase. Filtered slots retain the existing one-kept-successor scan and propagate the first reached filter or target cause. -/
def evaluateValueCountComputation (checked : CheckedNumberEntitySource model)
    (expected : Rat) (document : Document) (outer : Env)
    (directRead : FieldId → CheckedCell)
    (filterRead starRead : Env → FieldId → CheckedCell) :
    Except StarAddressingError NumericOperand :=
  let direct : FlatContext := { read := directRead }
  checked.evaluateValueCountWith expected fun operand =>
    operand.resolvedComputationAggregateSide document outer direct
      filterRead starRead

/-- Evaluate validation-phase numeric value count through the checked-document aggregate resolver, retaining per-selected-cell filter provenance. -/
def evaluateCheckedDocumentValueCountValidation
    (checked : CheckedNumberEntitySource model)
    (expected : Rat) (document : CheckedDocument model) (outer : Env) :
    Except CheckedAddressingError NumericOperand :=
  checked.evaluateValueCountWith expected fun operand =>
    operand.resolvedCheckedDocumentValidationAggregateSide document outer

/-- Evaluate computation-phase numeric value count through the same resolver and its one-kept-successor filter traversal. -/
def evaluateCheckedDocumentValueCountComputation
    (checked : CheckedNumberEntitySource model)
    (expected : Rat) (document : CheckedDocument model) (outer : Env) :
    Except CheckedAddressingError NumericOperand :=
  checked.evaluateValueCountWith expected fun operand =>
    operand.resolvedCheckedDocumentComputationAggregateSide document outer

/-- Run the common partial value-count fold over a raw or checked-document operand resolver. -/
def evaluatePartialValueCountWith
    (checked : CheckedNumberEntitySource model) (expected : Rat)
    (resolve : CheckedNumberEntityOperand model →
      Except Error (Sum (ResolvedValueListSide .number)
        PartialValidationNumberAggregateResult)) :
    Except Error PartialValidationNumberAggregateResult :=
  if checked.hasHaving then
    pure .skippedHaving
  else do
    match ← scanResolvedValueListOperands
        (state := ResolvedValueCountSide .number)
        (terminal := PartialValidationNumberAggregateResult)
        resolve
        (fun cause => .evaluated (.unknown cause))
        (fun accumulated _ side => accumulated.appendResolved side)
        checked.operands ResolvedValueCountSide.empty with
    | .inl accumulated =>
        pure (.evaluated (evalValueCountAggregate expected accumulated))
    | .inr result => pure result

/-- Evaluate the unfiltered numeric value count under partial validation. A locally visible filter skips the rule before topology, relevance, or target reads, matching the other entity-list aggregate leaves. -/
def evaluatePartialValueCount (checked : CheckedNumberEntitySource model)
    (expected : Rat) (document : Document) (outer : Env)
    (scope : ValidationRelevanceScope) (directRead : RawFlatContext)
    (starRead : Env → FieldId → RawCell) :
    Except StarAddressingError PartialValidationNumberAggregateResult :=
  checked.evaluatePartialValueCountWith expected fun operand =>
    operand.resolvedPartialAggregateSide document outer scope
      (model.checkContext directRead) starRead

/-- Evaluate partial numeric value count from the immutable checked document without changing per-cell filter provenance or partial gates. -/
def evaluateCheckedDocumentPartialValueCount
    (checked : CheckedNumberEntitySource model)
    (expected : Rat) (document : CheckedDocument model)
    (outer : Env) (scope : ValidationRelevanceScope) :
    Except CheckedAddressingError PartialValidationNumberAggregateResult :=
  checked.evaluatePartialValueCountWith expected fun operand =>
    operand.resolvedCheckedDocumentPartialAggregateSide document outer scope

end CheckedNumberEntitySource

end A12Kernel
