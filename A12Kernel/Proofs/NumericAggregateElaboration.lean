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

/-- A two-field aggregate derives exactly the union of its declaration scales. -/
theorem resolvedNumericAggregate_pair_scaleSummary
    (first second : FlatNumberField) :
    ({ first, rest := [second] : ResolvedNumericAggregateFields }).scaleSummary =
      (NumericScaleSummary.field first.info.scale).union
        (NumericScaleSummary.field second.info.scale) := by
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

end A12Kernel
