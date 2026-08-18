import A12Kernel.Semantics.DateRangeComparison

/-! # Resolved DateRange construction-equality locks -/

namespace A12Kernel.Conformance.DateRangeComparison

open A12Kernel

private def full (year : Int) (month day : Nat)
    (admissible : (FullDate.ofYmd? year month day).isSome) : FullDate :=
  (FullDate.ofYmd? year month day).get admissible

private def june1 := full 2024 6 1 (by native_decide)
private def june29 := full 2024 6 29 (by native_decide)
private def june30 := full 2024 6 30 (by native_decide)

private def constructed : ResolvedDateRangeConstruction :=
  { start := june1, finish := june30 }

private def storedSame : ResolvedDateRange :=
  { start := june1, finish := june30 }

private def storedChangedFinish : ResolvedDateRange :=
  { start := june1, finish := june29 }

/- Construction-versus-field equality and inequality are exact complements on the maintained full-Date source pair. -/
example :
    EqualityOp.equal.evalDateRangeConstruction
        .left constructed storedSame = .fired .value ∧
      EqualityOp.notEqual.evalDateRangeConstruction
        .left constructed storedSame = .notFired := by
  native_decide

/- Changing only the finish endpoint separates whole-range identity from start-only comparison. -/
example :
    EqualityOp.equal.evalDateRangeConstruction
        .left constructed storedChangedFinish = .notFired ∧
      EqualityOp.notEqual.evalDateRangeConstruction
        .right constructed storedChangedFinish = .fired .value := by
  native_decide

/- Exchanging the stored and constructed operands preserves both legal operators. -/
example :
    EqualityOp.equal.evalDateRangeConstruction
        .right constructed storedSame = .fired .value ∧
      EqualityOp.notEqual.evalDateRangeConstruction
        .right constructed storedChangedFinish = .fired .value := by
  native_decide

end A12Kernel.Conformance.DateRangeComparison
