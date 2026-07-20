import A12Kernel.Semantics.NumericAggregate

/-! # Resolved Number aggregate laws

These laws characterize one already-expanded and already-filtered Number selection. They do not prove star/path expansion, `Having` evaluation, partial relevance, computation behavior, or external kernel correspondence.
-/

namespace A12Kernel

/-- A scan is unavailable exactly when its selected stream contains an unavailable cell. -/
theorem numericExtremumAggregate_scan_error_iff
    (op : NumericExtremumOp)
    (cells : List (ValueListCell .number))
    (selected : Option Rat) :
    (∃ cause, op.scanAggregateCells cells selected = .error cause) ↔
      cells.any ValueListCell.isUnknown = true := by
  induction cells generalizing selected with
  | nil => simp [NumericExtremumOp.scanAggregateCells]
  | cons cell cells inductionHypothesis =>
      cases cell with
      | present amount =>
          cases selected <;>
            simp [NumericExtremumOp.scanAggregateCells,
              ValueListCell.isUnknown, inductionHypothesis]
      | empty =>
          simp [NumericExtremumOp.scanAggregateCells,
            ValueListCell.isUnknown, inductionHypothesis]
      | unknown cause =>
          simp [NumericExtremumOp.scanAggregateCells, ValueListCell.isUnknown]

/-- A stream consisting only of empty cells leaves the selection accumulator unchanged. -/
theorem numericExtremumAggregate_scan_allEmpty
    (op : NumericExtremumOp)
    (cells : List (ValueListCell .number))
    (selected : Option Rat)
    (allEmpty : cells.all ValueListCell.isEmpty = true) :
    op.scanAggregateCells cells selected = .ok selected := by
  induction cells generalizing selected with
  | nil => rfl
  | cons cell cells inductionHypothesis =>
      cases cell with
      | present amount => simp [ValueListCell.isEmpty] at allEmpty
      | empty =>
          simp only [List.all_cons, ValueListCell.isEmpty, Bool.true_and] at allEmpty
          exact inductionHypothesis selected allEmpty
      | unknown cause => simp [ValueListCell.isEmpty] at allEmpty

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
  rw [numericExtremumAggregate_scan_allEmpty op cells none allEmpty]
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

end A12Kernel
