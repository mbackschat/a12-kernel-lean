import A12Kernel.Semantics.NumericAggregate
import A12Kernel.Proofs.ValueList
import A12Kernel.Proofs.NumericFillability

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
  unfold evalNumericSumAggregate evalDeclaredNumericSumAggregate
    ResolvedValueListSide.toNumericSumSide ResolvedNumericSumSide.valueCells
    scanNumericSumCells
  simp only [List.map_map, Function.comp_def, List.map_id']
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
      have declaredMissingPotential :
          (ResolvedNumericSumSide.hasMissingPotential
            { cells := cells.map fun cell => { cell, declarationSigned := fieldSigned }
              uninstantiatedSignedness :=
                if hasUninstantiatedTail then [fieldSigned] else []
              hasHaving := false }) = true := by
        simpa [ResolvedNumericSumSide.hasMissingPotential,
          ResolvedNumericSumSide.hasEmpty,
          ResolvedValueListSide.hasMissingPotential,
          ResolvedValueListSide.hasEmpty] using missingPotential
      simp [declaredMissingPotential]
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

/-- After a present value, an explicit empty source contributes its own declaration's
    direction; the present source's signedness is irrelevant. -/
theorem declaredNumericSum_explicitMissing
    (presentSigned missingSigned : Bool) (amount : Rat) :
    evalDeclaredNumericSumAggregate
      { cells :=
          [{ cell := .present amount, declarationSigned := presentSigned },
           { cell := .empty, declarationSigned := missingSigned }]
        uninstantiatedSignedness := []
        hasHaving := false } =
      .value (NumericArithmeticOp.add.eval 0 amount)
        (NumericFillability.emptyNumber missingSigned) := by
  cases presentSigned <;> cases missingSigned <;> rfl

/-- Uninstantiated declarations retain the same per-source direction as explicit empties. -/
theorem declaredNumericSum_uninstantiatedMissing
    (presentSigned missingSigned : Bool) (amount : Rat) :
    evalDeclaredNumericSumAggregate
      { cells := [{ cell := .present amount, declarationSigned := presentSigned }]
        uninstantiatedSignedness := [missingSigned]
        hasHaving := false } =
      .value (NumericArithmeticOp.add.eval 0 amount)
        (NumericFillability.emptyNumber missingSigned) := by
  cases presentSigned <;> cases missingSigned <;> rfl

/-- The former homogeneous API is exactly the constant-signedness embedding. -/
theorem numericSumAggregate_homogeneousEmbedding
    (fieldSigned : Bool) (side : ResolvedValueListSide .number) :
    evalNumericSumAggregate fieldSigned side =
      evalDeclaredNumericSumAggregate (side.toNumericSumSide fieldSigned) := rfl

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
  unfold evalNumericSumAggregate evalDeclaredNumericSumAggregate
    ResolvedValueListSide.toNumericSumSide ResolvedNumericSumSide.valueCells
    scanNumericSumCells
  simp only [List.map_map, Function.comp_def, List.map_id']
  rw [valueListCell_scanPresent_firstUnknown
    numericSumStep before after none cause beforeKnown]

/-- A complete singleton distinct count is the fixed integral value one. -/
theorem numericDistinctCount_singleton_fixed (amount : Rat) :
    evalNumericDistinctCountAggregate
      { cells := [.present amount]
        hasUninstantiatedTail := false
        hasHaving := false } =
      .value 1 .fixed := by
  rfl

/-- A second value equal at the shared scale-19 boundary does not increase the distinct count. -/
theorem numericDistinctCount_equal_pair
    (left right : Rat)
    (equal : ValueListAtom.equal (kind := .number) left right = true) :
    evalNumericDistinctCountAggregate
      { cells := [.present left, .present right]
        hasUninstantiatedTail := false
        hasHaving := false } =
      .value 1 .fixed := by
  simp [evalNumericDistinctCountAggregate, scanDistinctNumericCells,
    ValueListCell.scanPresent, insertDistinctNumericValue, equal,
    ResolvedValueListSide.hasMissingPotential,
    ResolvedValueListSide.hasEmpty, ValueListCell.isEmpty]

/-- An all-empty selected count has the grow-only zero identity whenever the checked source proves an explicit or declared missing cell. -/
theorem numericDistinctCount_allEmpty
    (cells : List (ValueListCell .number))
    (hasUninstantiatedTail : Bool)
    (allEmpty : cells.all ValueListCell.isEmpty = true)
    (missing :
      ResolvedValueListSide.hasMissingPotential
        { cells, hasUninstantiatedTail, hasHaving := false } = true) :
    evalNumericDistinctCountAggregate
      { cells, hasUninstantiatedTail, hasHaving := false } =
      .value 0 .growOnly := by
  unfold evalNumericDistinctCountAggregate scanDistinctNumericCells
  rw [valueListCell_scanPresent_allEmpty
    insertDistinctNumericValue cells [] allEmpty]
  simp [missing]

/-- A reached filter makes an available distinct count both-directionally fillable independently of tail state. -/
theorem numericDistinctCount_having
    (cells : List (ValueListCell .number))
    (seen : List Rat)
    (hasUninstantiatedTail : Bool)
    (scanned : scanDistinctNumericCells cells = .ok seen) :
    evalNumericDistinctCountAggregate
      { cells, hasUninstantiatedTail, hasHaving := true } =
      .value seen.length .both := by
  simp [evalNumericDistinctCountAggregate, scanned]

/-- The first unavailable selected cell determines distinct-count suppression independently of every suffix cell and missingness flag. -/
theorem numericDistinctCount_firstUnknown
    (before after : List (ValueListCell .number))
    (cause : FormalCause)
    (hasUninstantiatedTail hasHaving : Bool)
    (beforeKnown : before.any ValueListCell.isUnknown = false) :
    evalNumericDistinctCountAggregate
      { cells := before ++ .unknown cause :: after
        hasUninstantiatedTail
        hasHaving } = .unknown cause := by
  unfold evalNumericDistinctCountAggregate scanDistinctNumericCells
  rw [valueListCell_scanPresent_firstUnknown insertDistinctNumericValue
    before after [] cause beforeKnown]

/-- One complete present pair is exactly one staged multiplication followed by the fold's zero-seeded addition, with no missing direction. -/
theorem numericProductAggregate_singleton_present (left right : Rat) :
    evalNumericProductAggregate {
      rows := [{ left := .present left, right := .present right }]
      leftSigned := false
      rightSigned := false
      hasUninstantiatedTail := false } =
    .value (NumericArithmeticOp.add.eval 0
      (NumericArithmeticOp.multiply.eval left right)) .fixed := by
  simp [evalNumericProductAggregate, scanNumericProductRows,
    scanNumericProductRowsFrom, numericProductCell, numericProductStep,
    numericArithmetic_fixed_fillability, pure, bind, Except.pure, Except.bind]

/-- An unavailable left cell suppresses its row before the right cell and every later row, retaining the exact first cause. -/
theorem numericProductAggregate_leftUnknown
    (cause : FormalCause) (right : ValueListCell .number)
    (remaining : List ResolvedNumericProductRow)
    (leftSigned rightSigned hasUninstantiatedTail : Bool) :
    evalNumericProductAggregate {
      rows := { left := .unknown cause, right } :: remaining
      leftSigned
      rightSigned
      hasUninstantiatedTail } = .unknown cause := by
  rfl

/-- A declared omitted row dominates the successful pair fold's arithmetic direction without changing its amount. -/
theorem numericProductAggregate_singleton_tail
    (left right : Rat) (leftSigned rightSigned : Bool) :
    evalNumericProductAggregate {
      rows := [{ left := .present left, right := .present right }]
      leftSigned
      rightSigned
      hasUninstantiatedTail := true } =
    .value (NumericArithmeticOp.add.eval 0
      (NumericArithmeticOp.multiply.eval left right)) .both := by
  cases leftSigned <;> cases rightSigned <;> rfl

end A12Kernel
