import A12Kernel.Semantics.DateRangeComparison

/-! # Exact-or-yearless DateRange identity locks -/

namespace A12Kernel.Conformance.DateRangeCellEquality

open A12Kernel

private def month (start finish : Nat) : DateRangeCellValue :=
  .yearlessMonth start finish

private def monthDay (startMonth startDay finishMonth finishDay : Nat) :
    DateRangeCellValue :=
  .yearlessMonthDay
    { month := startMonth, day := startDay }
    { month := finishMonth, day := finishDay }

/- Both ordered components independently determine yearless DateRange identity. -/
example :
    EqualityOp.equal.evalDateRangeCellValues
      (.value (month 2 3) true) (.value (month 2 3) true) = .fired .value ∧
    EqualityOp.notEqual.evalDateRangeCellValues
      (.value (month 1 3) true) (.value (month 2 3) true) = .fired .value ∧
    EqualityOp.notEqual.evalDateRangeCellValues
      (.value (month 2 3) true) (.value (month 2 4) true) = .fired .value ∧
    EqualityOp.equal.evalDateRangeCellValues
      (.value (monthDay 2 28 3 1) true)
      (.value (monthDay 2 28 3 1) true) = .fired .value ∧
    EqualityOp.notEqual.evalDateRangeCellValues
      (.value (monthDay 2 27 3 1) true)
      (.value (monthDay 2 28 3 1) true) = .fired .value ∧
    EqualityOp.notEqual.evalDateRangeCellValues
      (.value (monthDay 2 28 3 1) true)
      (.value (monthDay 2 28 3 2) true) = .fired .value := by
  native_decide

/- The total value seam does not equate different component profiles; checked consumers own the earlier static refusal. -/
example :
    EqualityOp.equal.evalDateRangeCellValues
      (.value (month 2 3) true)
      (.value (monthDay 2 1 3 31) true) = .notFired ∧
    EqualityOp.notEqual.evalDateRangeCellValues
      (.value (month 2 3) true)
      (.value (monthDay 2 1 3 31) true) = .fired .value := by
  native_decide

end A12Kernel.Conformance.DateRangeCellEquality
