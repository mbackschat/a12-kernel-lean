import A12Kernel.Semantics.NumericAggregate

/-! # Resolved Number aggregate executable locks

These cases begin after one Number field-list or star has been expanded, filtered, and classified. They distinguish aggregate `Sum`/`MinValue`/`MaxValue` from operand-list arithmetic without adding path lowering, row selection, partial relevance, or computation.
-/

namespace A12Kernel.Conformance.NumericAggregate

open A12Kernel

private def side
    (cells : List (ValueListCell .number))
    (hasUninstantiatedTail : Bool := false)
    (hasHaving : Bool := false) : ResolvedValueListSide .number :=
  { cells, hasUninstantiatedTail, hasHaving }

private def belowComparisonResolution : Rat := 1 / 10 ^ 20
private def tenPow50 : Rat := 10 ^ 50

/- Empty cells are dropped rather than substituted with the operand-list zero. -/
example :
    evalNumericExtremumAggregate .maximum
      (side [.present (-5), .empty]) =
        .value (-5) .growOnly := by
  native_decide

/- A positive `MinValue` independently proves that an empty cell neither competes as zero nor erases Min's shrink-only missingness. -/
example :
    evalNumericExtremumAggregate .minimum
      (side [.present 5, .empty]) =
        .value 5 .shrinkOnly := by
  native_decide

/- Every all-empty Number aggregate has the fillable zero identity, independently of selector direction. -/
example :
    evalNumericExtremumAggregate .minimum (side [.empty]) =
        .value 0 .both ∧
      evalNumericExtremumAggregate .maximum (side [] false true) =
        .value 0 .both ∧
      NumericComparisonOp.less.evalFixedRight
        (evalNumericExtremumAggregate .minimum (side [.empty])) 10 =
        .fired .omission := by
  native_decide

/- A completed present selection is fixed; an uninstantiated tail restores the selector-specific direction. -/
example :
    evalNumericExtremumAggregate .maximum (side [.present 7]) =
        .value 7 .fixed ∧
      evalNumericExtremumAggregate .maximum (side [.present 7] true) =
        .value 7 .growOnly ∧
      evalNumericExtremumAggregate .minimum (side [.present 7] true) =
        .value 7 .shrinkOnly := by
  native_decide

/- A resolved `Having` marker makes every known aggregate result movable in both directions. Filter-dropped rows are absent from this already-filtered stream. -/
example :
    evalNumericExtremumAggregate .maximum
      (side [.present 7] false true) =
        .value 7 .both ∧
      NumericComparisonOp.greater.evalFixedRight
        (evalNumericExtremumAggregate .maximum
          (side [.present 7] false true)) 5 =
        .fired .omission := by
  native_decide

/- Aggregate extrema scan every selected cell rather than stopping at the first value. -/
example :
    evalNumericExtremumAggregate .maximum
      (side [.present 7, .unknown .declaredConstraint]) =
        .unknown .declaredConstraint := by
  native_decide

/- The first reached unavailable cell owns the suppression cause. -/
example :
    evalNumericExtremumAggregate .minimum
      (side [.unknown .required, .unknown .malformed]) =
        .unknown .required := by
  native_decide

/- Selection occurs before the later scale-19 comparison boundary. -/
example :
    evalNumericExtremumAggregate .maximum
      (side [.present 0, .present belowComparisonResolution]) =
        .value belowComparisonResolution .fixed := by
  native_decide

/- This total low-level state is fixed zero; checked star lowering must mark an authored no-row selection as having an uninstantiated tail. -/
example :
    evalNumericExtremumAggregate .minimum (side []) =
      .value 0 .fixed := by
  native_decide

/- `Sum` rounds at every reached addition rather than accumulating one exact rational total. -/
example :
    evalNumericSumAggregate false
      (side [.present (tenPow50 - 1), .present (3 / 5)]) =
        .value tenPow50 .fixed := by
  native_decide

/- `Sum` is an encounter-ordered left fold. A right-associated implementation produces `1` for the first list, while reordering the same values changes the staged result. -/
example :
    evalNumericSumAggregate false
      (side [.present tenPow50, .present (-tenPow50), .present (3 / 5)]) =
        .value (3 / 5) .fixed ∧
      evalNumericSumAggregate false
        (side [.present (-tenPow50), .present (3 / 5), .present tenPow50]) =
        .value 1 .fixed := by
  native_decide

/- A present value does not terminate the scan; the first later unavailable cell still owns suppression. -/
example :
    evalNumericSumAggregate false
      (side [.present 7, .unknown .required, .unknown .malformed]) =
        .unknown .required := by
  native_decide

/- An empty cell records missingness but neither terminates the scan nor contributes a numeric term. -/
example :
    evalNumericSumAggregate false
      (side [.present 2, .empty, .present 5]) =
        .value 7 .growOnly := by
  native_decide

/- Every authored all-empty Number sum has the both-directionally fillable zero identity, independently of signedness. -/
example :
    evalNumericSumAggregate false (side [.empty]) =
        .value 0 .both ∧
      evalNumericSumAggregate true (side [] true) =
        .value 0 .both := by
  native_decide

/- After a value enters an incomplete sum, unsigned declarations grow only while signed declarations may move in both directions. -/
example :
    evalNumericSumAggregate false (side [.present 7] true) =
        .value 7 .growOnly ∧
      evalNumericSumAggregate true (side [.present 7] true) =
        .value 7 .both ∧
      evalNumericSumAggregate true (side [.present 7]) =
        .value 7 .fixed := by
  native_decide

/- A reached resolved `Having` marker escalates an otherwise fixed sum without changing its amount. -/
example :
    evalNumericSumAggregate false (side [.present 7] false true) =
      .value 7 .both := by
  native_decide

end A12Kernel.Conformance.NumericAggregate
