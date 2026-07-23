import A12Kernel.Elaboration.NumericAggregate
import A12Kernel.Proofs.NumberEntityList

/-! # Checked nonrepeatable Number aggregate lowering laws -/

namespace A12Kernel

/-- The shared resolved Sum atom is definitionally the established declaration-aware aggregate fold. -/
theorem resolvedNumericAggregate_sum_delegates
    (source : ResolvedNumericAggregateFields)
    (observe : FieldId → CellObservation) :
    source.evaluate .sum observe =
      evalDeclaredNumericSumAggregate (source.resolvedSumSide observe) := by
  rfl

/-- Both shared resolved extrema atoms delegate to the established exact selector over the same classified cells. -/
theorem resolvedNumericAggregate_extrema_delegate
    (source : ResolvedNumericAggregateFields)
    (observe : FieldId → CellObservation) :
    source.evaluate .minimum observe =
        evalNumericExtremumAggregate .minimum (source.resolvedValueSide observe) ∧
      source.evaluate .maximum observe =
        evalNumericExtremumAggregate .maximum
          (source.resolvedValueSide observe) := by
  exact ⟨rfl, rfl⟩

/-- The resolved Number distinct-count atom delegates to the shared scale-19 fold over the same classified cells. -/
theorem resolvedNumericAggregate_distinctCount_delegates
    (source : ResolvedNumericAggregateFields)
    (observe : FieldId → CellObservation) :
    source.evaluate .distinctCount observe =
      evalNumericDistinctCountAggregate (source.resolvedValueSide observe) := by
  rfl

/-- A two-field aggregate derives exactly the union of its declaration scales. -/
theorem resolvedNumericAggregate_pair_scaleSummary
    (first second : FlatNumberField) :
    ({ first, rest := [second] : ResolvedNumericAggregateFields }).scaleSummary =
      (NumericScaleSummary.field first.info.scale).union
        (NumericScaleSummary.field second.info.scale) := by
  rfl

/-- NumberOfDifferentValues has integral result scale independently of every contributing declaration scale. -/
theorem resolvedNumericAggregate_distinctCount_scaleSummary
    (source : ResolvedNumericAggregateFields) :
    NumericAggregateOp.distinctCount.scaleSummary source =
      NumericScaleSummary.field 0 := by
  rfl

/-- A checked product pair exposes one path identity; consumers never need to compare independently resolved row streams. -/
theorem checkedNumericProductAggregate_samePath
    (checked : CheckedNumericProductAggregate model) :
    checked.left.source.path = checked.right.source.path :=
  checked.samePath

/-- The checked pair's result scale is exactly the existing multiplication summary of its two declaration scales. -/
theorem checkedNumericProductAggregate_scaleSummary
    (checked : CheckedNumericProductAggregate model) :
    checked.scaleSummary = NumericScaleSummary.binary .multiply
      (NumericScaleSummary.field checked.left.field.info.scale)
      (NumericScaleSummary.field checked.right.field.info.scale) := by
  rfl

/-- Once the common path resolves, phase-specific checked evaluation delegates exactly to one shared-topology product side and the pure fold. -/
theorem checkedNumericProductAggregate_evaluateAt_of_resolved
    (checked : CheckedNumericProductAggregate model) (phase : Phase)
    (document : Document) (outer : Env)
    (read : Env → FieldId → CheckedCell) (resolved : ResolvedStarTopology)
    (resolvedPath : checked.left.source.path.resolve document outer = .ok resolved) :
    checked.evaluateAt phase document outer read =
      .ok (evalNumericProductAggregate
        (checked.selectedSideAt phase resolved read)) := by
  unfold CheckedNumericProductAggregate.evaluateAt
  rw [resolvedPath]
  rfl

/-- Both resolved views classify the same explicit cells in the same order. -/
theorem checkedNumericAggregate_sameCells
    (checked : CheckedNumericAggregateFields model) (raw : RawFlatContext) :
    (checked.resolvedSumSide raw).valueCells =
      (checked.resolvedValueSide raw).cells := by
  simp [CheckedNumericAggregateFields.resolvedSumSide,
    CheckedNumericAggregateFields.resolvedValueSide,
    ResolvedNumericAggregateFields.resolvedSumSide,
    ResolvedNumericAggregateFields.resolvedValueSide,
    ResolvedNumericSumSide.valueCells]

/-- This checked subset never invents an uninstantiated extremum source. -/
theorem checkedNumericAggregate_noUninstantiatedTail
    (checked : CheckedNumericAggregateFields model) (raw : RawFlatContext) :
    (checked.resolvedValueSide raw).hasUninstantiatedTail = false := by
  rfl

/-- This checked subset never invents an uninstantiated Sum source. -/
theorem checkedNumericAggregate_noUninstantiatedSumSource
    (checked : CheckedNumericAggregateFields model) (raw : RawFlatContext) :
    (checked.resolvedSumSide raw).uninstantiatedSignedness = [] := by
  rfl

/-- Neither resolved view invents a `Having` marker. -/
theorem checkedNumericAggregate_noHaving
    (checked : CheckedNumericAggregateFields model) (raw : RawFlatContext) :
    (checked.resolvedValueSide raw).hasHaving = false ∧
      (checked.resolvedSumSide raw).hasHaving = false := by
  exact ⟨rfl, rfl⟩

/-- Checked Sum evaluation is exactly the established resolved per-declaration evaluator. -/
theorem checkedNumericAggregate_evaluateSum
    (checked : CheckedNumericAggregateFields model) (raw : RawFlatContext) :
    checked.evaluateSum raw =
      evalDeclaredNumericSumAggregate (checked.resolvedSumSide raw) := by
  rfl

/-- Checked extremum evaluation is exactly the established resolved evaluator. -/
theorem checkedNumericAggregate_evaluateExtremum
    (checked : CheckedNumericAggregateFields model) (op : NumericExtremumOp)
    (raw : RawFlatContext) :
    checked.evaluateExtremum op raw =
      evalNumericExtremumAggregate op (checked.resolvedValueSide raw) := by
  cases op <;> rfl

/-- Successful checked Sum evaluation is exactly the established one-declaration aggregate evaluator over the checked resolved side. -/
theorem checkedNumericStarSource_evaluateSum_of_valid
    (checked : CheckedNumericStarSource model) (raw : RawSingleGroupContext)
    (valid : checked.validateContext raw = .ok ()) :
    checked.evaluateSum raw =
      .ok (evalNumericSumAggregate checked.field.info.signed
        (checked.resolvedValueSide raw)) := by
  unfold CheckedNumericStarSource.evaluateSum
  rw [valid]
  rfl

/-- Successful checked extremum evaluation is exactly the established evaluator over the same checked resolved side. -/
theorem checkedNumericStarSource_evaluateExtremum_of_valid
    (checked : CheckedNumericStarSource model) (op : NumericExtremumOp)
    (raw : RawSingleGroupContext) (valid : checked.validateContext raw = .ok ()) :
    checked.evaluateExtremum op raw =
      .ok (evalNumericExtremumAggregate op (checked.resolvedValueSide raw)) := by
  unfold CheckedNumericStarSource.evaluateExtremum
  rw [valid]
  rfl

/-- Direct, plain-star, and filtered-star aggregate slots delegate to their established declaration, topology, and filter owners without another reader or selector. -/
theorem checkedNumberEntityOperand_aggregateSide_delegates
    (directSource : CheckedNumberEntityField model)
    (starSource : CheckedStarNumberSource model)
    (filteredSource : CheckedStarNumberHavingSource model)
    (document : Document) (outer : Env) (context : FlatContext)
    (filterRead : Env → FieldId → CheckedCell)
    (starRead : Env → FieldId → RawCell) :
    (CheckedNumberEntityOperand.field directSource).resolvedAggregateSide
        document outer context filterRead starRead =
        .ok (directSource.resolvedAggregateSide context) ∧
      (CheckedNumberEntityOperand.star starSource).resolvedAggregateSide
        document outer context filterRead starRead =
        starSource.resolvedValueSide document outer starRead ∧
      (CheckedNumberEntityOperand.starHaving filteredSource).resolvedAggregateSide
        document outer context filterRead starRead =
        filteredSource.resolvedValueSide document outer filterRead starRead := by
  exact ⟨rfl, rfl, rfl⟩

/-- A relevant direct partial aggregate slot delegates to the same declaration-owned side, while a nonrelevant one is rejected before its checked value is inspected. -/
theorem checkedNumberEntityField_partialAggregate_relevance
    (source : CheckedNumberEntityField model)
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (direct : FlatContext) (starRead : Env → FieldId → RawCell) :
    (scope.coversCell model source.declaration.path [] = true →
      (CheckedNumberEntityOperand.field source).resolvedPartialAggregateSide
          document outer scope direct starRead =
        .ok (.inl (source.resolvedAggregateSide direct))) ∧
    (scope.coversCell model source.declaration.path [] = false →
      (CheckedNumberEntityOperand.field source).resolvedPartialAggregateSide
          document outer scope direct starRead =
        .ok (.inr .nonRelevant)) := by
  constructor <;> intro relevant <;>
    simp [CheckedNumberEntityOperand.resolvedPartialAggregateSide, relevant] <;>
    rfl

/-- A checked all-rows star that fails wildcard/ancestor coverage returns nonrelevance after topology resolution but before any target classification. -/
theorem checkedNumberEntityStar_partialAggregate_nonRelevant
    (source : CheckedStarNumberSource model)
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (direct : FlatContext) (starRead : Env → FieldId → RawCell)
    (resolved : ResolvedStarTopology)
    (resolvedPath : source.source.path.resolve document outer = .ok resolved)
    (nonRelevant : source.source.allRowsRelevant scope = false) :
    (CheckedNumberEntityOperand.star source).resolvedPartialAggregateSide
        document outer scope direct starRead = .ok (.inr .nonRelevant) := by
  simp [CheckedNumberEntityOperand.resolvedPartialAggregateSide,
    CheckedStarNumberSource.resolvedPartialAllRowsValueSide, resolvedPath,
    CheckedStarNumberSource.selectedPartialAllRowsValueSide, nonRelevant]
  rfl

/-- Any checked filter in the local aggregate source skips partial evaluation before topology, relevance, direct reads, or target reads. -/
theorem checkedNumberEntitySource_partialAggregate_skipsHaving
    (checked : CheckedNumberEntitySource model) (op : NumericAggregateOp)
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (directRead : RawFlatContext) (starRead : Env → FieldId → RawCell)
    (hasHaving : checked.hasHaving = true) :
  checked.evaluatePartialAggregate op document outer scope directRead starRead =
      .ok .skippedHaving := by
  simp [CheckedNumberEntitySource.evaluatePartialAggregate,
    CheckedNumberEntitySource.evaluatePartialAggregateWith, hasHaving,
    pure, Except.pure]

/-- The immutable checked-document route keeps the source-wide partial filter gate ahead of either aggregate fold. -/
theorem checkedNumberEntitySource_checkedDocumentPartial_skipsHaving
    (checked : CheckedNumberEntitySource model) (op : NumericAggregateOp)
    (expected : Rat) (document : CheckedDocument model)
    (outer : Env) (scope : ValidationRelevanceScope)
    (hasHaving : checked.hasHaving = true) :
    checked.evaluateCheckedDocumentPartialAggregate op document outer scope =
        .ok .skippedHaving ∧
      checked.evaluateCheckedDocumentPartialValueCount expected document outer scope =
        .ok .skippedHaving := by
  constructor <;>
    simp [CheckedNumberEntitySource.evaluateCheckedDocumentPartialAggregate,
      CheckedNumberEntitySource.evaluateCheckedDocumentPartialValueCount,
      CheckedNumberEntitySource.evaluatePartialAggregateWith,
      CheckedNumberEntitySource.evaluatePartialValueCountWith, hasHaving,
      pure, Except.pure]

end A12Kernel
