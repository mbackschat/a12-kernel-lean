import A12Kernel.Semantics.DateComparison

/-! # Resolved full-Date comparison locks -/

namespace A12Kernel.Conformance.DateComparison

open A12Kernel

private def holds? (op : DateComparisonOp)
    (leftYear : Int) (leftMonth leftDay : Nat)
    (rightYear : Int) (rightMonth rightDay : Nat) : Option Bool := do
  let left ← FullDate.ofYmd? leftYear leftMonth leftDay
  let right ← FullDate.ofYmd? rightYear rightMonth rightDay
  pure (op.holds left right)

/- Every operator is separated on a strictly earlier pair. -/
example :
    holds? .equal 2024 2 29 2024 3 1 = some false ∧
      holds? .notEqual 2024 2 29 2024 3 1 = some true ∧
      holds? .before 2024 2 29 2024 3 1 = some true ∧
      holds? .beforeOrEqual 2024 2 29 2024 3 1 = some true ∧
      holds? .after 2024 2 29 2024 3 1 = some false ∧
      holds? .afterOrEqual 2024 2 29 2024 3 1 = some false := by
  native_decide

/- Equality separates strict from inclusive ordering in both directions. -/
example :
    holds? .equal 2024 6 15 2024 6 15 = some true ∧
      holds? .notEqual 2024 6 15 2024 6 15 = some false ∧
      holds? .before 2024 6 15 2024 6 15 = some false ∧
      holds? .beforeOrEqual 2024 6 15 2024 6 15 = some true ∧
      holds? .after 2024 6 15 2024 6 15 = some false ∧
      holds? .afterOrEqual 2024 6 15 2024 6 15 = some true := by
  native_decide

/- Chronology uses decoded date identity across year and leap boundaries. -/
example :
    holds? .after 2025 1 1 2024 12 31 = some true ∧
      holds? .before 2000 2 29 2001 2 28 = some true := by
  native_decide

end A12Kernel.Conformance.DateComparison
