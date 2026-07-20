import A12Kernel.Semantics.NumericAggregate
import A12Kernel.Proofs.ValueList

/-! # Resolved Number aggregate laws

These laws characterize one already-expanded and already-filtered Number selection. They do not prove star/path expansion, `Having` evaluation, partial relevance, computation behavior, or external kernel correspondence.
-/

namespace A12Kernel

/-- Every authored all-empty Number aggregate identity is zero and both-directionally fillable. This is the kernel's conservative classification even when the selected field is unsigned. -/
theorem numericExtremumAggregate_allEmpty
    (op : NumericExtremumOp)
    (cells : List (ValueListCell .number))
    (hasUninstantiatedTail hasHaving : Bool)
    (allEmpty : cells.all ValueListCell.isEmpty = true)
    (hasMissingOrHaving :
      ((cells.any ValueListCell.isEmpty || hasUninstantiatedTail) || hasHaving) = true) :
    evalNumericExtremumAggregate op
      { cells, hasUninstantiatedTail, hasHaving } =
        .value 0 .both := by
  unfold evalNumericExtremumAggregate
  have scanEmpty := valueListCell_scanPresent_allEmpty
    op.aggregateStep cells none allEmpty
  rw [show op.scanAggregateCells cells none = .ok none by
    simpa [NumericExtremumOp.scanAggregateCells] using scanEmpty]
  cases hasHaving with
  | false =>
      have missingPotential :
          (ResolvedValueListSide.hasMissingPotential
            { cells := cells
              hasUninstantiatedTail := hasUninstantiatedTail
              hasHaving := false }) = true := by
        simpa [ResolvedValueListSide.hasMissingPotential,
          ResolvedValueListSide.hasEmpty] using hasMissingOrHaving
      simp [missingPotential]
  | true => simp

/-- With one present value and no missingness metadata, both aggregate selectors are fixed. -/
theorem numericExtremumAggregate_singleton_fixed
    (op : NumericExtremumOp) (amount : Rat) :
    evalNumericExtremumAggregate op
      { cells := [.present amount]
        hasUninstantiatedTail := false
        hasHaving := false } =
      .value amount .fixed := by
  cases op <;> rfl

/-- An uninstantiated tail preserves a singleton amount but changes its metadata to the operator's aggregate direction. -/
theorem numericExtremumAggregate_singleton_tail
    (op : NumericExtremumOp) (amount : Rat) :
    evalNumericExtremumAggregate op
      { cells := [.present amount]
        hasUninstantiatedTail := true
        hasHaving := false } =
      .value amount op.presentAggregateFillability := by
  cases op <;> rfl

/-- Equal selected amounts do not imply equal aggregate semantics: an uninstantiated tail changes every singleton result away from fixed. -/
theorem numericExtremumAggregate_tail_metadata_separator
    (op : NumericExtremumOp) (amount : Rat) :
    evalNumericExtremumAggregate op
      { cells := [.present amount]
        hasUninstantiatedTail := false
        hasHaving := false } ≠
    evalNumericExtremumAggregate op
      { cells := [.present amount]
        hasUninstantiatedTail := true
        hasHaving := false } := by
  cases op <;> simp [numericExtremumAggregate_singleton_fixed,
    numericExtremumAggregate_singleton_tail,
    NumericExtremumOp.presentAggregateFillability,
    NumericFillability.fixed, NumericFillability.growOnly,
    NumericFillability.shrinkOnly]

/-- A resolved `Having` marker leaves a singleton amount unchanged and makes its validation movement conservative in both directions. -/
theorem numericExtremumAggregate_singleton_having
    (op : NumericExtremumOp) (amount : Rat)
    (hasUninstantiatedTail : Bool) :
    evalNumericExtremumAggregate op
      { cells := [.present amount]
        hasUninstantiatedTail
        hasHaving := true } =
      .value amount .both := by
  cases op <;> cases hasUninstantiatedTail <;> rfl

/-- Every authored all-empty Number sum is zero and both-directionally fillable, independently of declaration signedness. -/
theorem numericSumAggregate_allEmpty
    (fieldSigned : Bool)
    (cells : List (ValueListCell .number))
    (hasUninstantiatedTail hasHaving : Bool)
    (allEmpty : cells.all ValueListCell.isEmpty = true)
    (hasMissingOrHaving :
      ((cells.any ValueListCell.isEmpty || hasUninstantiatedTail) || hasHaving) = true) :
    evalNumericSumAggregate fieldSigned
      { cells, hasUninstantiatedTail, hasHaving } =
        .value 0 .both := by
  unfold evalNumericSumAggregate scanNumericSumCells
  rw [valueListCell_scanPresent_allEmpty numericSumStep cells none allEmpty]
  cases hasHaving with
  | false =>
      have missingPotential :
          (ResolvedValueListSide.hasMissingPotential
            { cells := cells
              hasUninstantiatedTail := hasUninstantiatedTail
              hasHaving := false }) = true := by
        simpa [ResolvedValueListSide.hasMissingPotential,
          ResolvedValueListSide.hasEmpty] using hasMissingOrHaving
      simp [missingPotential]
  | true => simp

/-- A complete singleton sum is fixed, but its first value still passes through precision-50 addition from zero. -/
theorem numericSumAggregate_singleton_fixed
    (fieldSigned : Bool) (amount : Rat) :
    evalNumericSumAggregate fieldSigned
      { cells := [.present amount]
        hasUninstantiatedTail := false
        hasHaving := false } =
      .value (NumericArithmeticOp.add.eval 0 amount) .fixed := by
  rfl

/-- Missing potential after a present sum uses that missing declaration's signedness. -/
theorem numericSumAggregate_singleton_tail
    (fieldSigned : Bool) (amount : Rat) :
    evalNumericSumAggregate fieldSigned
      { cells := [.present amount]
        hasUninstantiatedTail := true
        hasHaving := false } =
      .value (NumericArithmeticOp.add.eval 0 amount)
        (NumericFillability.emptyNumber fieldSigned) := by
  cases fieldSigned <;> rfl

/-- Equal totals do not erase the unsigned-versus-signed missing-direction distinction. -/
theorem numericSumAggregate_tail_signedness_separator (amount : Rat) :
    evalNumericSumAggregate false
      { cells := [.present amount]
        hasUninstantiatedTail := true
        hasHaving := false } ≠
    evalNumericSumAggregate true
      { cells := [.present amount]
        hasUninstantiatedTail := true
        hasHaving := false } := by
  simp [numericSumAggregate_singleton_tail, NumericFillability.emptyNumber]

/-- A resolved `Having` marker makes every available singleton sum both-directionally fillable. -/
theorem numericSumAggregate_singleton_having
    (fieldSigned hasUninstantiatedTail : Bool) (amount : Rat) :
    evalNumericSumAggregate fieldSigned
      { cells := [.present amount]
        hasUninstantiatedTail
        hasHaving := true } =
      .value (NumericArithmeticOp.add.eval 0 amount) .both := by
  cases fieldSigned <;> cases hasUninstantiatedTail <;> rfl

/-- The first unavailable cell after a known prefix determines the internal suppression cause independently of every suffix cell and metadata flag. -/
theorem numericSumAggregate_firstUnknown
    (fieldSigned hasUninstantiatedTail hasHaving : Bool)
    (before after : List (ValueListCell .number))
    (cause : FormalCause)
    (beforeKnown : before.any ValueListCell.isUnknown = false) :
    evalNumericSumAggregate fieldSigned
      { cells := before ++ .unknown cause :: after
        hasUninstantiatedTail
        hasHaving } = .unknown cause := by
  unfold evalNumericSumAggregate scanNumericSumCells
  rw [valueListCell_scanPresent_firstUnknown
    numericSumStep before after none cause beforeKnown]

end A12Kernel
