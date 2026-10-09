import A12Kernel.Elaboration.IteratedDateRangeCondition
import A12Kernel.Semantics.ComputationOverlap

namespace A12Kernel

/-- Only overlap certificates enter this computation family; validation reuses those same
certificates with its own phase-specific cell and message semantics. -/
inductive CheckedComputationOverlap (model : FlatModel) where
  | anyPair (source : CheckedDateRangesOverlapSource model)
  | scalar (source : CheckedAtLeastOneDateRangeOverlapsSource model)
  | yearlessAnyPair (source : CheckedYearlessDateRangesOverlapSource model)
  | yearlessScalar (source : CheckedYearlessAtLeastOneDateRangeOverlapsSource model)

inductive ComputationOverlapError where
  | contextRequired
  | addressing (error : StarAddressingError)
  | selection (error : CheckedAddressingError)
  | fieldKindMismatch (field : FieldId)
  deriving Repr, DecidableEq

namespace CheckedComputationOverlap

def toValidation : CheckedComputationOverlap model → IteratedDateRangeCondition model
  | .anyPair source => .overlap source
  | .scalar source => .pluralOverlap source
  | .yearlessAnyPair source => .yearlessOverlap source
  | .yearlessScalar source => .yearlessPluralOverlap source

def shape : CheckedComputationOverlap model → CheckedFieldEntityShape model
  | .anyPair source => source.shape
  | .scalar source => source.shape
  | .yearlessAnyPair source => source.shape
  | .yearlessScalar source => source.shape

def referencesField (source : CheckedComputationOverlap model) (field : FieldId)
    (filterReads : CorrelatedHaving → FieldId → Bool := CorrelatedHaving.referencesField) : Bool :=
  source.shape.operands.any (fun operand => match operand with
    | .indexed selected => selected.referencesField field
    | .keyed selected => selected.referencesField field
    | operand => operand.expansionDeclarations.any (·.id == field)) ||
    source.toValidation.filters.any (filterReads · field)

def rowBoundBool (source : CheckedComputationOverlap model) (scope : List RepeatableLevel) : Bool :=
  source.shape.operands.all (fun operand => operand.bindingScopes.all (·.isPrefixOf scope))

private def exactRange : Value → Option ResolvedDateRange
  | .dateRange (.exact range) => range.toResolvedDateRange?
  | _ => none

private def yearlessRange : Value → Option YearlessInterval
  | .dateRange (.yearlessMonth start finish) => some (YearlessInterval.ofMonthPair start finish)
  | .dateRange (.yearlessMonthDay start finish) => some (YearlessInterval.ofMonthDayPair start finish)
  | _ => none

private def projectObservation (project : Value → Option α) (field : FieldId) :
    CellObservation → Except ComputationOverlapError (CellObservation α)
  | .empty => pure .empty
  | .poison cause | .unknown cause => pure (.poison cause)
  | .value value => match project value with
      | some range => pure (.value range)
      | none => throw (.fieldKindMismatch field)

private def observation (project : Value → Option α) (field : FieldId) (cell : CheckedCell) :
    Except ComputationOverlapError (CellObservation α) :=
  projectObservation project field (observeCell .computation cell)

private def indexedObservation (project : Value → Option α)
    (source : CheckedSemanticIndexSource model) (context : ScalarComputationContext) :
    Except ComputationOverlapError (CellObservation α) := do
  let value ← source.observeColumnWith .computation context.semanticIndexColumnReader
    context.row context.read context.storedText |>.mapError .selection
  projectObservation project source.targetDeclaration.id value

private def scanSlots (project : Value → Option α) (overlaps : α → α → Bool)
    (field : FieldId) (read : slot → CheckedCell) : List slot → ComputationOverlapSearch α →
    Except ComputationOverlapError
      (ComputationHavingScanResult (ComputationOverlapSearch α) ComputationConditionResult) :=
  ComputationOverlapSearch.scan overlaps (fun slot => observation project field (read slot))

private def scanOperands
    (scan : operand → ComputationOverlapSearch α → Except ComputationOverlapError
      (ComputationHavingScanResult (ComputationOverlapSearch α) ComputationConditionResult)) :
    List operand → ComputationOverlapSearch α → Except ComputationOverlapError
      (ComputationHavingScanResult (ComputationOverlapSearch α) ComputationConditionResult)
  | [], state => pure (.exhausted state)
  | source :: rest, state => do
      match ← scan source state with
      | .exhausted next => scanOperands scan rest next
      | .terminated result => pure (.terminated result)
      | .poison cause => pure (.poison cause)

private def addressed (context : ScalarComputationContext) :
    Except ComputationOverlapError ComputationFillContext :=
  match context.addressed with
  | some context => pure context
  | none => throw .contextRequired

private def scanStar (project : Value → Option α) (overlaps : α → α → Bool)
    (context : ScalarComputationContext) (filterRead : Env → FieldId → CheckedCell)
    (filterStoredText filterNumberText : Env → FieldId → Option String)
    (path : CheckedStarFieldPath model) (filter : Option CorrelatedHaving)
    (state : ComputationOverlapSearch α) : Except ComputationOverlapError
      (ComputationHavingScanResult (ComputationOverlapSearch α) ComputationConditionResult) := do
  let contextRead ← addressed context
  let resolved ← (path.path.resolveInCapacity contextRead.document context.row).mapError .addressing
  let field := path.declaration.id
  let read := fun row => contextRead.read row field
  match filter with
  | none => scanSlots project overlaps field read resolved.environments state
  | some having => do
      let mode : FilterTraversalMode := match state with
        | .anyPair _ => .dense
        | .against _ => .sparse
      let traversal ← (model.filterTraversal path.path
        (contextRead.document.filterRows.getD contextRead.document.instantiatedRows) context.row mode).mapError .addressing
      let read := fun row => model.filterRead contextRead.document contextRead.read row field
      having.scanComputationResolving
        (({
          read := fun row id => pure (model.filterRead contextRead.document filterRead row id)
          storedText := filterStoredText
          numberText := filterNumberText
          world := context.world
          stringExpressionUnavailable := .addressing .stringExpressionUnavailable
          unsupportedDateCalendar := .addressing .unsupportedDateCalendar
          temporalValueFailure := .addressing .temporalValueFailure
          worldUnavailable := .addressing .worldUnavailable
          typeValidityValueFailure := .addressing .typeValidityValueFailure
          storedTextUnavailable := ComputationOverlapError.addressing ∘ StarAddressingError.storedTextUnavailable
          groupUnavailable := ComputationOverlapError.addressing ∘ StarAddressingError.unsupportedGroupOperand
          bindingError := fun error => .addressing error.toStarAddressingError } : ResolvingCorrelationContext ComputationOverlapError).withModelComputationGroups model contextRead.document)
        context.row (fun state row => state.step overlaps <$> observation project field (read row))
        traversal.candidates state traversal.occupancy

private def scanGroup (project : Value → Option α) (overlaps : α → α → Bool)
    (context : ScalarComputationContext) (source : CheckedEntityGroupSource model)
    (declarations : List FlatFieldDecl) (state : ComputationOverlapSearch α) :
    Except ComputationOverlapError
      (ComputationHavingScanResult (ComputationOverlapSearch α) ComputationConditionResult) :=
  scanOperands (fun declaration state => do
    if declaration.repeatableScope.isEmpty then
      scanSlots project overlaps declaration.id context.read [declaration.id] state
    else
      let contextRead ← addressed context
      let rows ← (model.groupOperandEnvironments contextRead.document context.row
        source.boundLevelCount declaration.repeatableScope).mapError .addressing
      scanSlots project overlaps declaration.id (fun row => contextRead.read row declaration.id) rows state)
    declarations state

private def scanKeyed (project : Value → Option α) (overlaps : α → α → Bool)
    (context : ScalarComputationContext) (source : CheckedKeyedEntityExtent model)
    (state : ComputationOverlapSearch α) : Except ComputationOverlapError
      (ComputationHavingScanResult (ComputationOverlapSearch α) ComputationConditionResult) := do
  let current ← addressed context
  let selected ← source.selectWith .computation context.semanticIndexColumnReader
    context.row context.read context.storedText |>.mapError .selection
  match selected with
  | .empty => pure (.exhausted state)
  | .unknown cause | .poison cause => pure (.poison cause)
  | .value environment =>
      let rows ← source.rows current.document environment |>.mapError .addressing
      scanOperands (fun (declaration, environments, _) state =>
        scanSlots project overlaps declaration.id
          (fun row => current.read row declaration.id) environments state) rows state

private def scanExact (context : ScalarComputationContext) (filterRead : Env → FieldId → CheckedCell)
    (filterStoredText filterNumberText : Env → FieldId → Option String)
    (source : CheckedSingularDateRangesOverlapOperand model) (state : ComputationOverlapSearch ResolvedDateRange) :=
  match source with
  | .canonical (.indexed selection _) | .indexedFragment selection _ =>
      ComputationOverlapSearch.scan ResolvedDateRange.overlaps
        (fun source => indexedObservation exactRange source context) [selection] state
  | .canonical (.keyed selection _) => scanKeyed exactRange ResolvedDateRange.overlaps context selection state
  | .canonical (.star path _ filter) => scanStar exactRange ResolvedDateRange.overlaps context filterRead filterStoredText filterNumberText path filter state
  | source => scanSlots exactRange ResolvedDateRange.overlaps source.declaration.id
      context.read [source.declaration.id] state

private def scanExactList (context : ScalarComputationContext) (filterRead : Env → FieldId → CheckedCell)
    (filterStoredText filterNumberText : Env → FieldId → Option String)
    (source : CheckedAtLeastOneDateRangeOverlapsListOperand model) (state : ComputationOverlapSearch ResolvedDateRange) :=
  match source with
  | .field source => scanExact context filterRead filterStoredText filterNumberText source state
  | .keyed source _ _ => scanKeyed exactRange ResolvedDateRange.overlaps context source state
  | .group source =>
      scanGroup exactRange ResolvedDateRange.overlaps context source.source
        ((source.first :: source.rest).map (fun (field : CheckedCanonicalDateRangeField) => field.declaration)) state

private def scanYearless (context : ScalarComputationContext) (filterRead : Env → FieldId → CheckedCell)
    (filterStoredText filterNumberText : Env → FieldId → Option String)
    (source : CheckedYearlessDateRangeOverlapOperand model) (state : ComputationOverlapSearch YearlessInterval) :=
  match source with
  | .indexed selection _ =>
      ComputationOverlapSearch.scan YearlessInterval.overlaps
        (fun source => indexedObservation yearlessRange source context) [selection] state
  | .keyed selection _ _ => scanKeyed yearlessRange YearlessInterval.overlaps context selection state
  | .direct source => scanSlots yearlessRange YearlessInterval.overlaps source.declaration.id
      context.read [source.declaration.id] state
  | .star path _ filter => scanStar yearlessRange YearlessInterval.overlaps context filterRead filterStoredText filterNumberText path filter state
  | .group source =>
      scanGroup yearlessRange YearlessInterval.overlaps context source.source
        ((source.first :: source.rest).map (fun (field : CheckedYearlessDateRangeOverlapField model) => field.declaration)) state

def evalChecked (source : CheckedComputationOverlap model) (context : ScalarComputationContext)
    (filterRead : Env → FieldId → CheckedCell)
    (filterStoredText : Env → FieldId → Option String := fun _ _ => none)
    (filterNumberText : Env → FieldId → Option String := fun _ _ => none) : Except ComputationOverlapError ComputationConditionResult :=
  match source with
  | .anyPair source => ComputationOverlapSearch.result <$>
      scanOperands (scanExact context filterRead filterStoredText filterNumberText) source.operands (.anyPair [])
  | .yearlessAnyPair source => ComputationOverlapSearch.result <$>
      scanOperands (scanYearless context filterRead filterStoredText filterNumberText) source.operands (.anyPair [])
  | .scalar source => do
      let scalar ← match source.scalarSelection? with
        | some selection => indexedObservation exactRange selection context
        | none => observation exactRange source.scalar.declaration.id (context.read source.scalar.declaration.id)
      ComputationOverlapSearch.scalarUsing scalar fun state => ComputationOverlapSearch.result <$>
        scanOperands (scanExactList context filterRead filterStoredText filterNumberText) source.operands state
  | .yearlessScalar source => do
      let scalar ← match source.scalarSelection? with
        | some selection => indexedObservation yearlessRange selection context
        | none => observation yearlessRange source.scalar.declaration.id (context.read source.scalar.declaration.id)
      ComputationOverlapSearch.scalarUsing scalar fun state => ComputationOverlapSearch.result <$>
        scanOperands (scanYearless context filterRead filterStoredText filterNumberText) source.operands state

end CheckedComputationOverlap
end A12Kernel
