import A12Kernel.Elaboration.PartialSemanticIndex
import A12Kernel.Elaboration.NumericAggregate.Products
import A12Kernel.Elaboration.NumericAggregate.Groups

/-! # Checked mixed entity-list numeric aggregates and value counts -/

namespace A12Kernel

/-- The aggregate over an operand that reaches no cell, the same fold every slot runs with nothing
appended. -/
def NumericAggregateOp.overNoCells (op : NumericAggregateOp) : NumericOperand :=
  ({} : ResolvedNumberEntityAggregateSides).evaluate op

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
    (classify : Env → CheckedCell → ValueListCell .number) :
    List (Env × FieldId) → List (ValueListCell .number) →
      Except PartialViewNumberAggregateError
        (Sum (List (ValueListCell .number))
          PartialValidationNumberAggregateResult)
  | [], reversed => pure (.inl reversed.reverse)
  | (environment, fieldId) :: remaining, reversed => do
      match read environment fieldId with
      | .error error => throw (.addressing error)
      | .ok none => throw .silentlyUnavailable
      | .ok (some checked) =>
          match classify environment checked with
          | .unknown cause => pure (.inr (.evaluated (.unknown cause)))
          | cell =>
              resolvePartialViewNumberCells read classify
                remaining (cell :: reversed)

/-- Read each reached `(environment, field)` instance through the call-local view, in the order
    given: one field's rows for a star, a group's in-capacity cells in its expansion order. -/
private def resolvedPartialViewSide
    (read : Env → FieldId →
      Except CheckedAddressingError (Option CheckedCell))
    (classify : Env → CheckedCell → ValueListCell .number)
    (instances : List (Env × FieldId)) (hasUninstantiatedTail hasHaving : Bool) :
    Except PartialViewNumberAggregateError
      (Sum (ResolvedValueListSide .number)
        PartialValidationNumberAggregateResult) := do
  match ← resolvePartialViewNumberCells read classify
      instances [] with
  | .inl cells =>
      pure (.inl { cells, hasUninstantiatedTail, hasHaving })
  | .inr result => pure (.inr result)

/-- Selected aggregates share the index decision but ask their own all-rows extent gate before
reading targets; value-count and prefix consumers have different gates (spec/10 §5). -/
private def resolvedSelectedPartialAggregateSide
    (source : CheckedSelectedNumberEntity model) (document : CheckedDocument model)
    (outer : Env) (scope : ValidationRelevanceScope)
    (read : Env → FieldId → Except CheckedAddressingError (Option CheckedCell)) :
    Except PartialViewNumberAggregateError
      (Sum (ResolvedValueListSide .number) PartialValidationNumberAggregateResult) := do
  let selected ← (resolvePartialSelectedAddresses source.source document scope outer read
    (fun declaration bound reopened environment =>
      scope.coversAggregateExtent model declaration.path bound reopened environment)
    (missingStarIsOmitted := true)).mapError .addressing
  match selected with
  | none => pure (.inr .nonRelevant)
  | some (.unknown cause) | some (.poison cause) => pure (.inr (.evaluated (.unknown cause)))
  | some .empty => pure (.inl { cells := [.empty], hasUninstantiatedTail := false, hasHaving := false })
  | some (.value (addresses, hasTail)) =>
      if addresses.isEmpty then
        let cells := match source.source with | .inl _ => [.empty] | .inr _ => []
        pure (.inl { cells, hasUninstantiatedTail := hasTail, hasHaving := false })
      else
        resolvedPartialViewSide read (fun _ cell => (observeCell .validation cell).asNumberValueListCell)
          (addresses.map fun (declaration, environment) => (environment, declaration.id)) hasTail false

/-- Resolve exactly one authored slot. Plain and filtered stars reuse the general checked topology and filter owners; direct fields reuse the checked flat Number reader. -/
def resolvedAggregateSide (checked : CheckedNumberEntityOperand model)
    (document : Document) (outer : Env) (direct : FlatContext)
    (filterRead : Env → FieldId → CheckedCell)
    (starRead : Env → FieldId → RawCell) :
    Except StarAddressingError (ResolvedValueListSide .number) :=
  match checked with
  | .selected source => .error (.unsupportedGroupOperand source.groupPath)
  | .field source => pure (source.resolvedAggregateSide direct)
  | .star source => source.resolvedValueSide document outer starRead
  | .starHaving source =>
      source.resolvedValueSide (world := direct.world) document outer filterRead starRead
  | .group slot => .error (.unsupportedGroupOperand slot.groupPath)

/-- Resolve one full-validation aggregate slot from a caller-prepared checked view. Direct and repeated cells therefore share one validation phase without resampling declaration checks. A plain or filtered star narrows to its declared-capacity extent, answering as the checked-document route does; this route filters only the in-capacity rows, so an over-limit row is never kept, whichever way the filter would judge it, and cannot make the filter unknown ([checkpoint](../../../docs/sources/group-and-iteration-probes.md#src-filtered-star-capacity-both-arms)). -/
def resolvedValidationAggregateSideIn
    (checked : CheckedNumberEntityOperand model)
    (document : Document) (outer : Env) (direct : FlatContext)
    (read : Env → FieldId → CheckedCell) (traversalMode : FilterTraversalMode := .sparse) :
    Except StarAddressingError (ResolvedValueListSide .number) :=
  match checked with
  | .selected source => .error (.unsupportedGroupOperand source.groupPath)
  | .field source =>
      pure (source.resolvedAggregateSideAt .validation direct)
  | .star source => do
      let resolved ← source.source.path.resolveInCapacity document outer
      pure (resolved.toResolvedSide
        (source.checkedValueListCellAt .validation read))
  | .starHaving source =>
      source.source.source.resolvedValidationHavingValueListSide (traversalMode := traversalMode) document outer
        source.having read (source.source.checkedValueListCellAt .validation read) direct.world
  | .group slot => .error (.unsupportedGroupOperand slot.groupPath)

/-- Resolve one aggregate slot at computation phase. Filtered stars use the runtime iterator's one-kept-successor lookahead and stop at the first reached filter or target poison; plain stars and direct fields preserve the same checked-cell classification without validation's unknown-as-drop projection. A plain or filtered star narrows to its declared-capacity extent, which the Kernel applies on the computation arm too, so an over-limit row neither contributes nor poisons ([checkpoint](../../../docs/sources/group-and-iteration-probes.md#src-capacity-projection-computation-arm); filtered: [checkpoint](../../../docs/sources/group-and-iteration-probes.md#src-filtered-star-capacity-both-arms)). -/
def resolvedComputationAggregateSide
    (checked : CheckedNumberEntityOperand model)
    (document : Document) (outer : Env) (direct : FlatContext)
    (filterRead starRead : Env → FieldId → CheckedCell)
    (selectedRead : CheckedSelectedNumberEntity model → Except StarAddressingError (ResolvedValueListSide .number) := fun source => .error (.unsupportedGroupOperand source.groupPath))
    (filterStoredText : Env → FieldId → Option String := fun _ _ => none)
    (filterNumberText : Env → FieldId → Option String := fun _ _ => none)
    (traversalMode : FilterTraversalMode := .sparse) :
    Except StarAddressingError
      (Sum (ResolvedValueListSide .number) NumericOperand) :=
  match checked with
  | .selected source => .inl <$> selectedRead source
  | .field source =>
      pure (.inl (source.resolvedAggregateSideAt .computation direct))
  | .star source => do
      let resolved ← source.source.path.resolveInCapacity document outer
      pure (.inl (resolved.toResolvedSide
        (source.checkedValueListCellAt .computation starRead)))
  | .starHaving source => do
      let resolved ← source.source.source.path.resolveInCapacity document outer
      let traversal ← model.filterTraversal source.source.source.path
        (document.filterRows.getD document.instantiatedRows) outer traversalMode
      let filterContext := ({ read := model.filterRead document filterRead, storedText := filterStoredText, numberText := filterNumberText, world := direct.world } : CorrelationContext).withModelComputationGroups model document
      let consume := fun cells environment =>
        match source.source.checkedValueListCellAt .computation
            (model.filterRead document starRead) environment with
        | .unknown cause => .inr cause
        | cell => .inl (cell :: cells)
      match ← (source.having.scanComputation filterContext outer consume
          traversal.candidates [] traversal.occupancy).mapError (fun
            | .calendarUnavailable => .unsupportedDateCalendar
            | .valueFailure => .temporalValueFailure
            | .worldUnavailable => .worldUnavailable
            | .typeValidityValueFailure => .typeValidityValueFailure
            | .stringExpressionUnavailable => .stringExpressionUnavailable
            | .storedTextUnavailable fieldId => .storedTextUnavailable fieldId
            | .groupUnavailable path => .unsupportedGroupOperand path) with
      | .exhausted reversed =>
          pure (.inl {
            cells := reversed.reverse
            hasUninstantiatedTail := resolved.domain.hasOpenTail
            hasHaving := true })
      | .terminated cause | .poison cause =>
          pure (.inr (.unknown cause))
  | .group slot => .inl <$> slot.resolvedSideIn .computation document outer starRead

/-- Resolve one validation aggregate slot from the immutable checked document. Validation filters evaluate every candidate before the first target classification; target reads then stop at the first formal cause.

    A plain or filtered **star** and a **group** operand each narrow to their declared-capacity extent:
    a row beyond its group's declared repeatability is not in the domain the operand denotes, so its
    selected value cell is neither aggregated nor able to make the aggregate unavailable. A direct
    field keeps the complete formal-cell view. The filtered Number branch's `Sum` extent is measured
    on both arms ([checkpoint](../../../docs/sources/group-and-iteration-probes.md#src-filtered-star-capacity-both-arms))
    and its other operators on this arm by the peer's `kf230`.

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
    (document : CheckedDocument model) (outer : Env)
    (world : Option World := none) (traversalMode : FilterTraversalMode := .sparse) :
    Except CheckedAddressingError
      (Sum (ResolvedValueListSide .number) NumericOperand) :=
  do
    -- A key selecting no row leaves the starred list absent: an open extent, as spec/10 §4 counts an
    -- uninstantiated tail, so the aggregate stays fillable (generated self-validation rows,
    -- docs/sources/model-structure-and-declaration-probes.md#src-generated-self-validation-k14).
    if let .selected source := checked then
      return .inl (← source.sideIn .validation document outer (missingStarIsOmitted := true))
    let resolved ← checked.resolveCheckedValidationOperand document outer world traversalMode
    let side := match checked with
      | .selected _ | .star _ | .starHaving _ | .group _ =>
          resolved.inCapacityValueListSideAt .validation
      | .field _ => resolved.valueListSideAt .validation
    match side.available with
    | .error cause => pure (.inr (.unknown cause))
    | .ok () => pure (.inl side)

/-- Resolve computation operands with ordered filter lookahead and phase-specific reads.
Filtered stars visit cache-bounded virtual coordinates (KF528); plain stars retain physical topology.
Both domains exclude over-capacity rows before filter or payload evaluation
([capacity checkpoint](../../../docs/sources/group-and-iteration-probes.md#src-filtered-star-capacity-both-arms)). -/
def resolvedCheckedDocumentComputationAggregateSide
    (checked : CheckedNumberEntityOperand model)
    (document : CheckedDocument model) (outer : Env)
    (world : Option World := none) (traversalMode : FilterTraversalMode := .sparse) :
    Except CheckedAddressingError
      (Sum (ResolvedValueListSide .number) NumericOperand) :=
  match checked with
  | .selected source => .inl <$> source.sideIn .computation document outer
  | .field source =>
      resolvedCheckedDocumentSide document .computation source.field
        [[]] false false
  | .starHaving source => do
      let resolved ←
        (source.source.source.path.resolveInCapacity document.source.toDocument outer)
          |>.mapError .addressing
      let consume := fun cells environment => do
        let cell ← document.checkedCellWithRead document.readDeclared environment source.source.field.id
        match (observeCell .computation cell).asNumberValueListCell with
        | .unknown cause => pure (.inr cause)
        | cell => pure (.inl (cell :: cells))
      let traversal ← source.source.source.filterTraversal document outer traversalMode
      match ← source.having.scanComputationResolving
          (document.resolvingCorrelationContextWithRead document.readDeclared world) outer consume
          traversal.candidates [] traversal.occupancy with
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
  | .selected source =>
      match resolvedSelectedPartialAggregateSide source document outer scope
          (fun row field => (fun addressed => some addressed.cell) <$> document.addressedCell row field) with
      | .ok result => pure result
      | .error (.addressing error) => throw error
      | .error .silentlyUnavailable => pure (.inr .nonRelevant)
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
        (source.source.path.resolveInCapacity document.source.toDocument outer)
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
      if slot.allRowsRelevant scope outer then do
        match ← checked.resolvedCheckedDocumentValidationAggregateSide document outer with
        | .inl side => pure (.inl side)
        | .inr result => pure (.inr (.evaluated result))
      else
        pure (.inr .nonRelevant)

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
  | .selected source => resolvedSelectedPartialAggregateSide source document outer scope read
  | .field source =>
      if scope.coversCell model source.declaration.path [] then
        resolvedPartialViewSide read
          (fun _ cell =>
            (observeCell .validation cell).asNumberValueListCell)
          [([], source.field.id)] false false
      else
        pure (.inr .nonRelevant)
  | .star source => do
      let resolved ←
        (source.source.path.resolveInCapacity document.source.toDocument outer)
          |>.mapError fun error =>
            PartialViewNumberAggregateError.addressing (.addressing error)
      if source.source.allRowsRelevant scope outer then
        resolvedPartialViewSide read
          (fun environment cell =>
            source.checkedValueListCell .validation cell environment)
          (resolved.environments.map (·, source.field.id))
          resolved.domain.hasOpenTail false
      else
        pure (.inr .nonRelevant)
  | .starHaving _ => pure (.inr .skippedHaving)
  | .group slot =>
      if slot.allRowsRelevant scope outer then do
        let resolved ← (checked.resolveCheckedValidationOperand document outer).mapError
          PartialViewNumberAggregateError.addressing
        resolvedPartialViewSide read
          (fun _ cell => (observeCell .validation cell).asNumberValueListCell)
          (resolved.core.inCapacityAddressedCells.map fun addressed =>
            (addressed.environment, addressed.address.field))
          resolved.hasUninstantiatedTail false
      else
        pure (.inr .nonRelevant)

/-- Resolve one partial `NumberOfValueInFields` slot through the local existential value-list account matching the measured outcome pattern. -/
def resolvedCheckedDocumentPartialValueCountSide
    (checked : CheckedNumberEntityOperand model)
    (document : CheckedDocument model) (outer : Env)
    (scope : ValidationRelevanceScope) :
    Except CheckedAddressingError
      (Sum (ResolvedValueListSide .number)
        PartialValidationNumberAggregateResult) :=
  match checked with
  | .selected source => .error (.addressing (.unsupportedGroupOperand source.groupPath))
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
        (source.source.path.resolveInCapacity document.source.toDocument outer)
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
      if slot.valueListExtentRelevant scope outer then do
        match ← checked.resolvedCheckedDocumentValidationAggregateSide document outer with
        | .inl side => pure (.inl side)
        | .inr result => pure (.inr (.evaluated result))
      else
        pure (.inr .nonRelevant)

/-- Resolve one partial-validation aggregate slot. Direct fields require their concrete cell; ordinary stars require complete wildcard/ancestor coverage and retain the established topology-produced side unchanged. Filtered slots return the rule-level skip marker without evaluating their filter. -/
def resolvedPartialAggregateSide (checked : CheckedNumberEntityOperand model)
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (direct : FlatContext) (starRead : Env → FieldId → RawCell) :
    Except StarAddressingError
      (Sum (ResolvedValueListSide .number)
        PartialValidationNumberAggregateResult) :=
  match checked with
  | .selected source => .error (.unsupportedGroupOperand source.groupPath)
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
  | .selected source => .error (.unsupportedGroupOperand source.groupPath)
  | .field source =>
      if scope.coversCell model source.declaration.path [] then
        pure (.inl (source.resolvedAggregateSide direct))
      else
        pure (.inr .nonRelevant)
  | .star source => do
      let resolved ← source.source.path.resolveInCapacity document outer
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
        (Sum ResolvedNumberEntityAggregateSides NumericOperand)) :
    Except Error NumericOperand := do
  match ← scanResolvedValueListOperandsBy ResolvedNumberEntityAggregateSides.values
      (state := ResolvedNumberEntityAggregateSides)
      (terminal := NumericOperand)
      resolve
      (fun cause => .unknown cause)
      (fun accumulated _ side => accumulated.appendResolved side)
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
  checked.evaluateAggregateWith op fun operand =>
    operand.resolveAggregateSidesWith
      (fun source => .inl <$> source.resolvedAggregateSide document outer direct filterRead starRead)
      (fun group => .error (.unsupportedGroupOperand group.groupPath))

/-- Evaluate the same full-validation fold over one caller-prepared checked scalar/repeatable view. Every slot preserves authored order, validation-phase UNKNOWN, declaration-specific missing polarity, and structural address failure. -/
def evaluateValidationAggregateIn (checked : CheckedNumberEntitySource model)
    (op : NumericAggregateOp) (document : Document) (outer : Env)
    (direct : FlatContext) (read : Env → FieldId → CheckedCell) :
    Except StarAddressingError NumericOperand := do
  checked.evaluateAggregateWith op fun operand =>
    operand.resolveAggregateSidesWith
      (fun source => .inl <$> source.resolvedValidationAggregateSideIn document outer direct read)
      (fun group => .error (.unsupportedGroupOperand group.groupPath))

/-- Evaluate a checked ordinary Number entity-list aggregate at computation phase. Operand slots remain authored-order lazy, and each filtered star delegates to the shared one-kept-successor iterator rather than selecting its complete row set eagerly. -/
def evaluateComputationAggregate (checked : CheckedNumberEntitySource model)
    (op : NumericAggregateOp) (document : Document) (outer : Env)
    (directRead : FieldId → CheckedCell)
    (filterRead starRead : Env → FieldId → CheckedCell)
    (world : Option World := none)
    (selectedRead : CheckedSelectedNumberEntity model → Except StarAddressingError (ResolvedValueListSide .number) := fun source => .error (.unsupportedGroupOperand source.groupPath))
    (filterStoredText : Env → FieldId → Option String := fun _ _ => none)
    (filterNumberText : Env → FieldId → Option String := fun _ _ => none) :
    Except StarAddressingError NumericOperand :=
  let direct : FlatContext := { read := directRead, world }
  checked.evaluateAggregateWith op fun operand =>
    operand.resolveAggregateSidesWith
      (fun source => source.resolvedComputationAggregateSide document outer direct
        filterRead starRead selectedRead filterStoredText filterNumberText)
      (fun group => .inl <$> group.resolvedAggregateSides document outer id
        (fun row field => pure (observeCell .computation (starRead row field)).asNumberValueListCell))

/-- Evaluate validation-phase aggregate accumulation from one immutable model-certified checked document. Every operator resolves through the one capacity-aware side, so `Sum` cannot drift away from the extrema and the distinct count on the extent they share. -/
def evaluateCheckedDocumentValidationAggregate
    (checked : CheckedNumberEntitySource model)
    (op : NumericAggregateOp) (document : CheckedDocument model)
    (outer : Env)
    (world : Option World := none) : Except CheckedAddressingError NumericOperand :=
  checked.evaluateAggregateWith op fun operand =>
    operand.resolveAggregateSidesWith
      (fun source => source.resolvedCheckedDocumentValidationAggregateSide document outer world)
      (fun group => .inl <$> group.resolvedAggregateSides document.source.toDocument outer
        CheckedAddressingError.addressing (fun row field => do
          pure (observeCell .validation (← document.addressedCell row field).cell).asNumberValueListCell))

/-- Evaluate computation-phase aggregate accumulation from the same checked document without changing filter or poison timing. -/
def evaluateCheckedDocumentComputationAggregate
    (checked : CheckedNumberEntitySource model)
    (op : NumericAggregateOp) (document : CheckedDocument model)
    (outer : Env)
    (world : Option World := none) : Except CheckedAddressingError NumericOperand :=
  checked.evaluateAggregateWith op fun operand =>
    operand.resolveAggregateSidesWith
      (fun source => source.resolvedCheckedDocumentComputationAggregateSide document outer world)
      (fun group => .inl <$> group.resolvedAggregateSides document.source.toDocument outer
        CheckedAddressingError.addressing (fun row field => do
          pure (observeCell .computation (← document.addressedCell row field).cell).asNumberValueListCell))

/-- Run the common partial aggregate fold after the caller selects a raw or checked-document operand resolver. The source-wide filter skip remains before every resolver call. -/
def evaluatePartialAggregateWith
    (checked : CheckedNumberEntitySource model) (op : NumericAggregateOp)
    (resolve : CheckedNumberEntityOperand model →
      Except Error (Sum ResolvedNumberEntityAggregateSides
        PartialValidationNumberAggregateResult)) :
    Except Error PartialValidationNumberAggregateResult :=
  if checked.hasHaving then
    pure .skippedHaving
  else do
    match ← scanResolvedValueListOperandsBy ResolvedNumberEntityAggregateSides.values
        (state := ResolvedNumberEntityAggregateSides)
        (terminal := PartialValidationNumberAggregateResult)
        resolve
        (fun cause => .evaluated (.unknown cause))
        (fun accumulated _ side => accumulated.appendResolved side)
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
    operand.resolveAggregateSidesWith
      (fun source => source.resolvedPartialAggregateSide document outer scope
        (model.checkContext directRead) starRead)
      (fun group => .error (.unsupportedGroupOperand group.groupPath))

/-- Evaluate partial aggregate accumulation from the immutable checked document with the same filter-skip and relevance gates. -/
def evaluateCheckedDocumentPartialAggregate
    (checked : CheckedNumberEntitySource model)
    (op : NumericAggregateOp) (document : CheckedDocument model)
    (outer : Env) (scope : ValidationRelevanceScope) :
    Except CheckedAddressingError PartialValidationNumberAggregateResult :=
  checked.evaluatePartialAggregateWith op fun operand =>
    operand.resolveAggregateSidesWith
      (fun source => source.resolvedCheckedDocumentPartialAggregateSide document outer scope)
      (fun group => if group.allRowsRelevant scope outer then
        .inl <$> group.resolvedAggregateSides document.source.toDocument outer
          CheckedAddressingError.addressing (fun row field => do
            pure (observeCell .validation (← document.addressedCell row field).cell).asNumberValueListCell)
        else pure (.inr .nonRelevant))

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
      operand.resolveAggregateSidesWith
        (fun source => source.resolvedPartialViewAggregateSide document outer scope read)
        (fun group => if group.allRowsRelevant scope outer then
          .inl <$> group.resolvedAggregateSides document.source.toDocument outer
            (fun error => CheckedNumberEntityOperand.PartialViewNumberAggregateError.addressing (.addressing error))
            (fun row field => do
              let cell ← (read row field).mapError CheckedNumberEntityOperand.PartialViewNumberAggregateError.addressing
              match cell with
              | none => throw .silentlyUnavailable
              | some cell => pure (observeCell .validation cell).asNumberValueListCell)
          else pure (.inr .nonRelevant)) with
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
    pure (.inl (← operand.resolvedValidationAggregateSideIn (traversalMode := .dense)
      document outer direct read))

/-- Evaluate numeric `NumberOfValueInFields` at computation phase. Filtered slots retain the existing one-kept-successor scan and propagate the first reached filter or target cause. -/
def evaluateValueCountComputation (checked : CheckedNumberEntitySource model)
    (expected : Rat) (document : Document) (outer : Env)
    (directRead : FieldId → CheckedCell)
    (filterRead starRead : Env → FieldId → CheckedCell)
    (world : Option World := none)
    (selectedRead : CheckedSelectedNumberEntity model → Except StarAddressingError (ResolvedValueListSide .number) := fun source => .error (.unsupportedGroupOperand source.groupPath))
    (filterStoredText : Env → FieldId → Option String := fun _ _ => none)
    (filterNumberText : Env → FieldId → Option String := fun _ _ => none) :
    Except StarAddressingError NumericOperand :=
  let direct : FlatContext := { read := directRead, world }
  checked.evaluateValueCountWith expected fun operand =>
    operand.resolvedComputationAggregateSide (traversalMode := .dense) document outer direct
      filterRead starRead selectedRead filterStoredText filterNumberText

/-- Evaluate validation-phase numeric value count through the checked-document aggregate resolver, retaining per-selected-cell filter provenance. -/
def evaluateCheckedDocumentValueCountValidation
    (checked : CheckedNumberEntitySource model)
    (expected : Rat) (document : CheckedDocument model) (outer : Env)
    (world : Option World := none) :
    Except CheckedAddressingError NumericOperand :=
  checked.evaluateValueCountWith expected fun operand =>
    operand.resolvedCheckedDocumentValidationAggregateSide (traversalMode := .dense) document outer world

/-- Evaluate computation-phase numeric value count through the shared capacity-aware computation resolver and the established one-kept-successor filter traversal. -/
def evaluateCheckedDocumentValueCountComputation
    (checked : CheckedNumberEntitySource model)
    (expected : Rat) (document : CheckedDocument model) (outer : Env)
    (world : Option World := none) :
    Except CheckedAddressingError NumericOperand :=
  checked.evaluateValueCountWith expected fun operand =>
    operand.resolvedCheckedDocumentComputationAggregateSide (traversalMode := .dense) document outer world

/-- Run the common partial value-count fold over a raw or checked-document operand resolver. -/
def evaluatePartialValueCountWith
    (checked : CheckedNumberEntitySource model) (expected : Rat)
    (resolve : CheckedNumberEntityOperand model →
      Except Error (Sum (ResolvedValueListSide .number)
        PartialValidationNumberAggregateResult)) :
    Except Error PartialValidationNumberAggregateResult :=
  evalPartialResolvedValueCountOperands expected checked.operands checked.hasHaving resolve

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
