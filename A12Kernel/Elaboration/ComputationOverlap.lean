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

def referencesField (source : CheckedComputationOverlap model) (field : FieldId) : Bool :=
  source.shape.operands.any (fun operand => operand.expansionDeclarations.any (·.id == field)) ||
    source.toValidation.filters.any (·.referencesField field)

def rowBoundBool (source : CheckedComputationOverlap model) (scope : List RepeatableLevel) : Bool :=
  source.shape.operands.all (·.bindingScope.isPrefixOf scope)

private def exactRange : Value → Option ResolvedDateRange
  | .dateRange (.exact range) => range.toResolvedDateRange?
  | _ => none

private def yearlessRange : Value → Option YearlessInterval
  | .dateRange (.yearlessMonth start finish) => some (YearlessInterval.ofMonthPair start finish)
  | .dateRange (.yearlessMonthDay start finish) => some (YearlessInterval.ofMonthDayPair start finish)
  | _ => none

private def observation (project : Value → Option α) (field : FieldId) (cell : CheckedCell) :
    Except ComputationOverlapError (CellObservation α) :=
  match observeCell .computation cell with
  | .empty => pure .empty
  | .poison cause | .unknown cause => pure (.poison cause)
  | .value value => match project value with
      | some range => pure (.value range)
      | none => throw (.fieldKindMismatch field)

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
    (path : CheckedStarFieldPath model) (filter : Option CorrelatedHaving)
    (state : ComputationOverlapSearch α) : Except ComputationOverlapError
      (ComputationHavingScanResult (ComputationOverlapSearch α) ComputationConditionResult) := do
  let contextRead ← addressed context
  let resolved ← (path.path.resolveInCapacity contextRead.document context.row).mapError .addressing
  let field := path.declaration.id
  let read := fun row => contextRead.read row field
  match filter with
  | none => scanSlots project overlaps field read resolved.environments state
  | some having =>
      having.scanComputationResolving
        { read := fun row id => pure (filterRead row id)
          bindingError := fun error => .addressing error.toStarAddressingError }
        context.row (fun state row => state.step overlaps <$> observation project field (read row))
        resolved.environments state

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

private def scanExact (context : ScalarComputationContext) (filterRead : Env → FieldId → CheckedCell)
    (source : CheckedSingularDateRangesOverlapOperand model) (state : ComputationOverlapSearch ResolvedDateRange) :=
  match source with
  | .canonical (.star path _ filter) => scanStar exactRange ResolvedDateRange.overlaps context filterRead path filter state
  | source => scanSlots exactRange ResolvedDateRange.overlaps source.declaration.id
      context.read [source.declaration.id] state

private def scanExactList (context : ScalarComputationContext) (filterRead : Env → FieldId → CheckedCell)
    (source : CheckedAtLeastOneDateRangeOverlapsListOperand model) (state : ComputationOverlapSearch ResolvedDateRange) :=
  match source with
  | .field source => scanExact context filterRead source state
  | .group source =>
      scanGroup exactRange ResolvedDateRange.overlaps context source.source
        ((source.first :: source.rest).map (fun (field : CheckedCanonicalDateRangeField) => field.declaration)) state

private def scanYearless (context : ScalarComputationContext) (filterRead : Env → FieldId → CheckedCell)
    (source : CheckedYearlessDateRangeOverlapOperand model) (state : ComputationOverlapSearch YearlessInterval) :=
  match source with
  | .direct source => scanSlots yearlessRange YearlessInterval.overlaps source.declaration.id
      context.read [source.declaration.id] state
  | .star path _ filter => scanStar yearlessRange YearlessInterval.overlaps context filterRead path filter state
  | .group source =>
      scanGroup yearlessRange YearlessInterval.overlaps context source.source
        ((source.first :: source.rest).map (fun (field : CheckedYearlessDateRangeOverlapField model) => field.declaration)) state

def evalChecked (source : CheckedComputationOverlap model) (context : ScalarComputationContext)
    (filterRead : Env → FieldId → CheckedCell) : Except ComputationOverlapError ComputationConditionResult :=
  match source with
  | .anyPair source => ComputationOverlapSearch.result <$>
      scanOperands (scanExact context filterRead) source.operands (.anyPair [])
  | .yearlessAnyPair source => ComputationOverlapSearch.result <$>
      scanOperands (scanYearless context filterRead) source.operands (.anyPair [])
  | .scalar source => do
      let scalar ← observation exactRange source.scalar.declaration.id (context.read source.scalar.declaration.id)
      ComputationOverlapSearch.scalarUsing scalar fun state => ComputationOverlapSearch.result <$>
        scanOperands (scanExactList context filterRead) source.operands state
  | .yearlessScalar source => do
      let scalar ← observation yearlessRange source.scalar.declaration.id (context.read source.scalar.declaration.id)
      ComputationOverlapSearch.scalarUsing scalar fun state => ComputationOverlapSearch.result <$>
        scanOperands (scanYearless context filterRead) source.operands state

end CheckedComputationOverlap
end A12Kernel
