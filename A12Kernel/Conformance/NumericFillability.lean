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

/- Division rejects zero before consulting its fillability. -/
example : NumericArithmeticOutcome.divide
    (.value 1 .fixed) (.value 0 .both) = .notEvaluated := by
  native_decide

private def twoThirds50 : Rat := (2 * 10 ^ 50 + 1) / (3 * 10 ^ 50)
private def doubledRoundedThird : Rat := (2 * (10 ^ 50 - 1)) / (3 * 10 ^ 50)

/- The quotient is rounded directly; the reciprocal exists only for fillability propagation. -/
example : NumericArithmeticOutcome.divide
    (.value 2 .fixed) (.value 3 .fixed) = .value twoThirds50 .fixed := by
  native_decide

example : NumericArithmeticOutcome.eval .multiply
    (.value 2 .fixed)
    (NumericArithmeticOutcome.divide
      (.value 1 .fixed) (.value 3 .fixed)) = .value doubledRoundedThird .fixed := by
  native_decide

example : NumericArithmeticOutcome.value twoThirds50 .fixed ≠
    NumericArithmeticOutcome.value doubledRoundedThird .fixed := by
  native_decide

/- Each sign-conditioned term of the reciprocal transformation is observable. -/
example : NumericArithmeticOutcome.divide
    (.value 1 .fixed) (.value 2 .growOnly) = .value (1 / 2) .shrinkOnly := by
  native_decide

example : NumericArithmeticOutcome.divide
    (.value 1 .fixed) (.value 2 .shrinkOnly) = .value (1 / 2) .both := by
  native_decide

example : NumericArithmeticOutcome.divide
    (.value 1 .fixed) (.value (-2) .growOnly) = .value (-1 / 2) .both := by
  native_decide

example : NumericArithmeticOutcome.divide
    (.value 1 .fixed) (.value (-2) .shrinkOnly) = .value (-1 / 2) .growOnly := by
  native_decide

/- The dividend sign remains an independent input to the product table. -/
example : NumericArithmeticOutcome.divide
    (.value (-1) .fixed) (.value 2 .growOnly) = .value (-1 / 2) .growOnly := by
  native_decide

/- The transformed divisor still flows through the complete product table. -/
example : NumericArithmeticOutcome.divide
    (.value 0 .growOnly) (.value 2 .fixed) = .value 0 .growOnly := by
  native_decide

example : NumericArithmeticOutcome.divide
    (.value 0 .growOnly) (.value (-2) .fixed) = .value 0 .shrinkOnly := by
  native_decide

example : NumericArithmeticOutcome.divide
    (.value 0 .fixed) (.value 2 .both) = .value 0 .fixed := by
  native_decide

example : NumericArithmeticOutcome.divide
    (.value 0 .growOnly) (.value 2 .growOnly) = .value 0 .both := by
  native_decide

/- A domain-undefined child absorbs its enclosing arithmetic node, including multiplication by zero. -/
example : NumericArithmeticOutcome.eval .add
    .notEvaluated (.value 1 .fixed) = .notEvaluated := by
  native_decide

example : NumericArithmeticOutcome.eval .multiply
    (.value 0 .fixed) .notEvaluated = .notEvaluated := by
  native_decide

example : NumericArithmeticOutcome.divide
    (.value 1 .fixed) .notEvaluated = .notEvaluated := by
  native_decide

private def arithmeticOperand (op : NumericArithmeticOp)
    (leftValue : Rat) (leftFill : NumericFillability)
    (rightValue : Rat) (rightFill : NumericFillability) : NumericOperand :=
  .value (op.eval leftValue rightValue)
    (op.fillability leftValue leftFill rightValue rightFill)

/- Validation comparisons suppress a domain failure; this is not a computation projection. -/
private def validationComparisonVerdict (op : NumericComparisonOp)
    (outcome : NumericArithmeticOutcome) (expected : Rat) : Verdict :=
  match outcome with
  | .notEvaluated => .notFired
  | .value amount fillability => op.evalFixedRight (.value amount fillability) expected

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

/- A fixed divisor's sign changes the polarity of the same zero-valued quotient. -/
example : validationComparisonVerdict .greaterEqual
    (NumericArithmeticOutcome.divide
      (.value 0 .growOnly) (.value 2 .fixed)) 0 = .fired .value := by
  native_decide

example : validationComparisonVerdict .less
    (NumericArithmeticOutcome.divide
      (.value 0 .growOnly) (.value 2 .fixed)) 1 = .fired .omission := by
  native_decide

example : validationComparisonVerdict .greaterEqual
    (NumericArithmeticOutcome.divide
      (.value 0 .growOnly) (.value (-2) .fixed)) 0 = .fired .omission := by
  native_decide

example : validationComparisonVerdict .less
    (NumericArithmeticOutcome.divide
      (.value 0 .growOnly) (.value (-2) .fixed)) 1 = .fired .value := by
  native_decide

example : validationComparisonVerdict .greaterEqual
    (NumericArithmeticOutcome.divide
      (.value 1 .fixed) (.value 0 .both)) 0 = .notFired := by
  native_decide

end A12Kernel.Conformance.NumericFillability
