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

private inductive PartialViewNumberAggregateError where
  | addressing (error : CheckedAddressingError)
  | silentlyUnavailable

private def resolvePartialViewNumberCells
    (read : Env → FieldId →
      Except CheckedAddressingError (Option CheckedCell))
    (field : FieldId)
    (classify : Env → CheckedCell → ValueListCell .number) :
    List Env → List (ValueListCell .number) →
      Except PartialViewNumberAggregateError
        (Sum (List (ValueListCell .number))
          PartialValidationNumberAggregateResult)
  | [], reversed => pure (.inl reversed.reverse)
  | environment :: remaining, reversed => do
      match read environment field with
      | .error error => throw (.addressing error)
      | .ok none => throw .silentlyUnavailable
      | .ok (some checked) =>
          match classify environment checked with
          | .unknown cause => pure (.inr (.evaluated (.unknown cause)))
          | cell =>
              resolvePartialViewNumberCells read field classify
                remaining (cell :: reversed)

private def resolvedPartialViewSide
    (read : Env → FieldId →
      Except CheckedAddressingError (Option CheckedCell))
    (field : FieldId)
    (classify : Env → CheckedCell → ValueListCell .number)
    (environments : List Env) (hasUninstantiatedTail hasHaving : Bool) :
    Except PartialViewNumberAggregateError
      (Sum (ResolvedValueListSide .number)
        PartialValidationNumberAggregateResult) := do
  match ← resolvePartialViewNumberCells read field classify
      environments [] with
  | .inl cells =>
      pure (.inl { cells, hasUninstantiatedTail, hasHaving })
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
  | .group slot => .error (.unsupportedGroupOperand slot.groupPath)

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
  | .group slot => .error (.unsupportedGroupOperand slot.groupPath)

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
  | .group slot => .error (.unsupportedGroupOperand slot.groupPath)

/-- Resolve one validation aggregate slot from the immutable checked document. Validation filters evaluate every candidate before the first target classification; target reads then stop at the first formal cause.

    A plain **star** and a **group** operand each narrow to their declared-capacity extent, for the
    same measured reason: a row beyond its group's declared repeatability is not in the domain the
    operand denotes, so its cell is neither aggregated nor able to make the aggregate unavailable. A
    field and a filtered star keep the complete formal-cell view.

    One resolver serves every validation aggregate consumer — `Sum`, the extrema, the distinct count,
    and the value count. `Sum` and the group form were measured first, and the remaining consumers
    were left holding the complete view as an untested scope limit; the starred-field ladder
    ([checkpoint](../../../docs/sources/group-and-iteration-probes.md#src-starred-field-operand-extent))
    refuted that limit on all four at once. The group form answers identically on its fixed
    ([checkpoint](../../../docs/sources/inbound-group-operand-batches.md#src-group-operand-capacity-consumer-sweep))
    and starred
    ([checkpoint](../../../docs/sources/group-and-iteration-probes.md#src-starred-group-operand-extent))
    spellings.

    A well-formed over-limit cell alone cannot establish the mechanism: the separating observation is
    a **malformed** cell, which poisons the aggregate one index below capacity and is ignored one
    index above it, and that pair is measured on both forms. -/
def resolvedCheckedDocumentValidationAggregateSide
    (checked : CheckedNumberEntityOperand model)
    (document : CheckedDocument model) (outer : Env) :
    Except CheckedAddressingError
      (Sum (ResolvedValueListSide .number) NumericOperand) :=
  do
    let resolved ← checked.resolveCheckedValidationOperand document outer
    let side := match checked with
      | .star _ | .group _ => resolved.inCapacityValueListSideAt .validation
      | .field _ | .starHaving _ =>
          resolved.valueListSideAt .validation
    match side.available with
    | .error cause => pure (.inr (.unknown cause))
    | .ok () => pure (.inl side)

/-- Resolve one computation aggregate slot from the same checked document. A filtered slot retains one-kept-successor lookahead and keeps structural target/filter failure outside formal poison.

    A plain **star** and a **group** operand narrow to their declared-capacity extent here exactly as
    on the full-validation arm, and for the same reason: the over-limit row is not in the domain the
    operand denotes, so it is neither aggregated nor able to poison the computation. The arm boundary
    was measured rather than inherited — the same eight documents observed through `compute` answered
    from the in-capacity domain on both codegen strategies
    ([checkpoint](../../../docs/sources/group-and-iteration-probes.md#src-capacity-projection-computation-arm)),
    and the kernel reported the over-limit index as a formal error in the operand while still
    producing an uncleared computed value.

    The star once resolved its own environments here instead of going through the shared operand
    core. Both routes agreed on every retained computation case, so the capacity projection is the
    only intended behavioural difference; the shared core is kept because it is the one the group
    arm and the whole validation arm already use. -/
def resolvedCheckedDocumentComputationAggregateSide
    (checked : CheckedNumberEntityOperand model)
    (document : CheckedDocument model) (outer : Env) :
    Except CheckedAddressingError
      (Sum (ResolvedValueListSide .number) NumericOperand) :=
  match checked with
  | .field source =>
      resolvedCheckedDocumentSide document .computation source.field
        [[]] false false
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
  | .star _ | .group _ => do
      let resolved ← checked.resolveCheckedValidationOperand document outer
      pure (.inl (resolved.inCapacityValueListSideAt .computation))

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
      if source.source.allRowsRelevant scope outer then do
        match ← resolvedCheckedDocumentSide document .validation source.field
            resolved.environments resolved.domain.hasOpenTail false with
        | .inl side => pure (.inl side)
        | .inr result => pure (.inr (.evaluated result))
      else
        pure (.inr .nonRelevant)
  | .starHaving _ => pure (.inr .skippedHaving)
  | .group slot =>
      .error (.addressing (.unsupportedGroupOperand slot.groupPath))

/-- Resolve one unfiltered partial-validation slot through the caller's call-local checked-cell projection. Topology and all-rows relevance remain document-owned, while target classification observes preliminary index and required annotations instead of rereading the immutable base cells. -/
private def resolvedPartialViewAggregateSide
    (checked : CheckedNumberEntityOperand model)
    (document : CheckedDocument model) (outer : Env)
    (scope : ValidationRelevanceScope)
    (read : Env → FieldId →
      Except CheckedAddressingError (Option CheckedCell)) :
    Except PartialViewNumberAggregateError
      (Sum (ResolvedValueListSide .number)
        PartialValidationNumberAggregateResult) :=
  match checked with
  | .field source =>
      if scope.coversCell model source.declaration.path [] then
        resolvedPartialViewSide read source.field.id
          (fun _ cell =>
            (observeCell .validation cell).asNumberValueListCell)
          [[]] false false
      else
        pure (.inr .nonRelevant)
  | .star source => do
      let resolved ←
        (source.source.path.resolve document.source.toDocument outer)
          |>.mapError fun error =>
            PartialViewNumberAggregateError.addressing (.addressing error)
      if source.source.allRowsRelevant scope outer then
        resolvedPartialViewSide read source.field.id
          (fun environment cell =>
            source.checkedValueListCell .validation cell environment)
          resolved.environments resolved.domain.hasOpenTail false
      else
        pure (.inr .nonRelevant)
  | .starHaving _ => pure (.inr .skippedHaving)
  | .group slot =>
      .error (.addressing (.addressing (.unsupportedGroupOperand slot.groupPath)))

/-- Resolve one partial `NumberOfValueInFields` slot through the local existential value-list account matching the measured outcome pattern. -/
def resolvedCheckedDocumentPartialValueCountSide
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
      if source.source.valueListExtentRelevant scope outer then do
        match ← resolvedCheckedDocumentSide document .validation source.field
            resolved.environments resolved.domain.hasOpenTail false with
        | .inl side => pure (.inl side)
        | .inr result => pure (.inr (.evaluated result))
      else
        pure (.inr .nonRelevant)
  | .starHaving _ => pure (.inr .skippedHaving)
  | .group slot =>
      .error (.addressing (.unsupportedGroupOperand slot.groupPath))

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
  | .group slot => .error (.unsupportedGroupOperand slot.groupPath)

/-- Resolve one raw-document partial `NumberOfValueInFields` slot through the local existential value-list account matching the measured outcome pattern. -/
def resolvedPartialValueCountSide (checked : CheckedNumberEntityOperand model)
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
      let resolved ← source.source.path.resolve document outer
      if source.source.valueListExtentRelevant scope outer then
        pure (.inl (resolved.toResolvedSide (source.valueListCell starRead)))
      else
        pure (.inr .nonRelevant)
  | .starHaving _ => pure (.inr .skippedHaving)
  | .group slot => .error (.unsupportedGroupOperand slot.groupPath)

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

/-- Evaluate validation-phase aggregate accumulation from one immutable model-certified checked document. Every operator resolves through the one capacity-aware side, so `Sum` cannot drift away from the extrema and the distinct count on the extent they share. -/
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

/-- Evaluate partial aggregate accumulation through one call-local checked-cell projection while retaining the immutable document only for model-certified topology. -/
def evaluatePartialViewAggregate
    (checked : CheckedNumberEntitySource model)
    (op : NumericAggregateOp) (document : CheckedDocument model)
    (outer : Env) (scope : ValidationRelevanceScope)
    (read : Env → FieldId →
      Except CheckedAddressingError (Option CheckedCell)) :
    Except CheckedAddressingError
      PartialValidationNumberAggregateViewResult :=
  match checked.evaluatePartialAggregateWith op fun operand =>
      operand.resolvedPartialViewAggregateSide document outer scope read with
  | .ok result => .ok (.result result)
  | .error (.addressing error) => .error error
  | .error .silentlyUnavailable => .ok .silentlyUnavailable

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

/-- Evaluate computation-phase numeric value count through the shared capacity-aware computation resolver and the established one-kept-successor filter traversal. -/
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
    operand.resolvedPartialValueCountSide document outer scope
      (model.checkContext directRead) starRead

/-- Evaluate partial numeric value count from the immutable checked document without changing per-cell filter provenance or partial gates. -/
def evaluateCheckedDocumentPartialValueCount
    (checked : CheckedNumberEntitySource model)
    (expected : Rat) (document : CheckedDocument model)
    (outer : Env) (scope : ValidationRelevanceScope) :
    Except CheckedAddressingError PartialValidationNumberAggregateResult :=
  checked.evaluatePartialValueCountWith expected fun operand =>
    operand.resolvedCheckedDocumentPartialValueCountSide document outer scope

end CheckedNumberEntitySource

end A12Kernel
