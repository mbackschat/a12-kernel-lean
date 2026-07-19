import A12Kernel.Semantics.NumericComparison

/-! # Arithmetic fillability separating cases -/

namespace A12Kernel.Conformance.NumericFillability

open A12Kernel

example : NumericArithmeticOp.add.fillability 5 .fixed 0 .growOnly = .growOnly := by
  native_decide

example : NumericArithmeticOp.add.fillability 0 .both 0 .growOnly = .both := by
  native_decide

example : NumericArithmeticOp.subtract.fillability 5 .fixed 0 .growOnly = .shrinkOnly := by
  native_decide

example : NumericArithmeticOp.subtract.fillability 0 .growOnly 5 .fixed = .growOnly := by
  native_decide

/- The same fillable zero changes direction when the fixed factor changes sign. -/
example : NumericArithmeticOp.multiply.fillability 0 .growOnly 4 .fixed = .growOnly := by
  native_decide

example : NumericArithmeticOp.multiply.fillability 0 .growOnly (-4) .fixed = .shrinkOnly := by
  native_decide

example : NumericArithmeticOp.multiply.fillability 0 .growOnly 0 .fixed = .fixed := by
  native_decide

/- Joint movements matter even though both current values have zero sign. -/
example : NumericArithmeticOp.multiply.fillability 0 .growOnly 0 .growOnly = .growOnly := by
  native_decide

example : NumericArithmeticOp.multiply.fillability 0 .shrinkOnly 0 .shrinkOnly = .growOnly := by
  native_decide

example : NumericArithmeticOp.multiply.fillability 0 .growOnly 0 .shrinkOnly = .shrinkOnly := by
  native_decide

example : NumericArithmeticOp.multiply.fillability 0 .both 0 .both = .both := by
  native_decide

private def arithmeticOperand (op : NumericArithmeticOp)
    (leftValue : Rat) (leftFill : NumericFillability)
    (rightValue : Rat) (rightFill : NumericFillability) : NumericOperand :=
  .value (op.eval leftValue rightValue)
    (op.fillability leftValue leftFill rightValue rightFill)

/- The propagated directions are consumed by the existing comparison polarity account. -/
example : NumericComparisonOp.less.evalFixedRight
    (arithmeticOperand .multiply 0 .growOnly 4 .fixed) 100 = .fired .omission := by
  native_decide

example : NumericComparisonOp.greaterEqual.evalFixedRight
    (arithmeticOperand .multiply 0 .growOnly 4 .fixed) 0 = .fired .value := by
  native_decide

example : NumericComparisonOp.greaterEqual.evalFixedRight
    (arithmeticOperand .multiply 0 .growOnly (-4) .fixed) (-100) = .fired .omission := by
  native_decide

example : NumericComparisonOp.less.evalFixedRight
    (arithmeticOperand .multiply 0 .growOnly (-4) .fixed) 100 = .fired .value := by
  native_decide

example : NumericComparisonOp.less.evalFixedRight
    (arithmeticOperand .multiply 0 .growOnly 0 .fixed) 1 = .fired .value := by
  native_decide

end A12Kernel.Conformance.NumericFillability
