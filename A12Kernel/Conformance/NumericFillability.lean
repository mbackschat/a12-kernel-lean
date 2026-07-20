import A12Kernel.Semantics.NumericTolerance

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

/- Absolute value makes either input direction a possible magnitude increase, while only movement toward zero can shrink the result. -/
example : NumericArithmeticOutcome.absolute (.value (-5) .growOnly) =
    .value 5 .both := by
  native_decide

example : NumericArithmeticOutcome.absolute (.value 5 .shrinkOnly) =
    .value 5 .both := by
  native_decide

example : NumericArithmeticOutcome.absolute (.value 0 .both) =
    .value 0 .growOnly := by
  native_decide

example : NumericArithmeticOutcome.absolute .notEvaluated = .notEvaluated := by
  native_decide

/- Operand-list extrema combine directional fillability according to the selected full-precision value. -/
example : NumericExtremumOp.minimum.selectOutcome
    (.value 0 .growOnly) (.value 4 .shrinkOnly) = .value 0 .both := by
  native_decide

example : NumericExtremumOp.minimum.selectOutcome
    (.value 4 .growOnly) (.value 0 .shrinkOnly) = .value 0 .shrinkOnly := by
  native_decide

/- At a tie, Min can grow only if both tied operands can grow. -/
example : NumericExtremumOp.minimum.selectOutcome
    (.value 0 .both) (.value 0 .shrinkOnly) = .value 0 .shrinkOnly := by
  native_decide

/- Max mirrors the tie rule: either operand may grow it, but both tied operands must be able to shrink it. -/
example : NumericExtremumOp.maximum.selectOutcome
    (.value 0 .both) (.value 0 .growOnly) = .value 0 .growOnly := by
  native_decide

example : NumericExtremumOp.maximum.selectOutcome
    (.value (-4) .growOnly) (.value 0 .shrinkOnly) = .value 0 .both := by
  native_decide

example : NumericExtremumOp.minimum.selectOutcome
    .notEvaluated (.value 4 .fixed) = .notEvaluated := by
  native_decide

example : NumericArithmeticOutcome.divide
    (.value 1 .fixed) .notEvaluated = .notEvaluated := by
  native_decide

private def powerOutcome (base : Rat) (baseFill : NumericFillability)
    (exponent : Rat) (exponentFill : NumericFillability) : NumericArithmeticOutcome :=
  NumericArithmeticOutcome.power
    (.value base baseFill) (.value exponent exponentFill)

/- Power absorbs unavailable operands and every numeric domain failure before deriving directions. -/
example :
    NumericArithmeticOutcome.power .notEvaluated (.value 2 .fixed) = .notEvaluated ∧
      NumericArithmeticOutcome.power (.value 2 .fixed) .notEvaluated = .notEvaluated ∧
      powerOutcome 0 .fixed (-1) .fixed = .notEvaluated ∧
      powerOutcome 2 .fixed 1001 .fixed = .notEvaluated ∧
      powerOutcome 2 .fixed (1 / 2) .fixed = .notEvaluated := by
  native_decide

/- A fixed exponent separates zero, odd, and each current-sign route of the even branch. -/
example :
    powerOutcome 7 .both 0 .fixed = .value 1 .fixed ∧
      powerOutcome 2 .fixed 2 .fixed = .value 4 .fixed ∧
      powerOutcome 2 .both 3 .fixed = .value 8 .both ∧
      powerOutcome 2 .shrinkOnly 3 .fixed = .value 8 .shrinkOnly ∧
      powerOutcome (-2) .growOnly 3 .fixed = .value (-8) .growOnly ∧
      powerOutcome 2 .shrinkOnly 2 .fixed = .value 4 .both ∧
      powerOutcome (-2) .growOnly 2 .fixed = .value 4 .both ∧
      powerOutcome 0 .both 2 .fixed = .value 0 .growOnly := by
  native_decide

/- A fixed nonnegative base dispatches around one and through all three zero-base cases. -/
example :
    powerOutcome 2 .fixed 0 .growOnly = .value 1 .growOnly ∧
      powerOutcome 1 .fixed 2 .both = .value 1 .fixed ∧
      powerOutcome (1 / 2) .fixed 0 .growOnly = .value 1 .shrinkOnly ∧
      powerOutcome 0 .fixed 2 .growOnly = .value 0 .fixed ∧
      powerOutcome 0 .fixed 0 .growOnly = .value 1 .shrinkOnly ∧
      powerOutcome 0 .fixed 0 .both = .value 1 .growOnly ∧
      powerOutcome 0 .fixed 2 .both = .value 0 .growOnly := by
  native_decide

/- Fixed negative bases retain all magnitude, parity, and exponent-direction regions. -/
example :
    powerOutcome (-1 / 2) .fixed 2 .growOnly = .value (1 / 4) .shrinkOnly ∧
      powerOutcome (-1 / 2) .fixed 3 .growOnly = .value (-1 / 8) .growOnly ∧
      powerOutcome (-1 / 2) .fixed 2 .both = .value (1 / 4) .both ∧
      powerOutcome (-1) .fixed 2 .growOnly = .value 1 .shrinkOnly ∧
      powerOutcome (-1) .fixed 3 .growOnly = .value (-1) .growOnly ∧
      powerOutcome (-2) .fixed 2 .shrinkOnly = .value 4 .shrinkOnly ∧
      powerOutcome (-2) .fixed 3 .shrinkOnly = .value (-8) .growOnly ∧
      powerOutcome (-2) .fixed 2 .growOnly = .value 4 .both := by
  native_decide

/- The only one-directional both-variable branch requires all three guards. -/
example :
    powerOutcome 2 .growOnly 0 .growOnly = .value 1 .growOnly ∧
      powerOutcome 2 .both 0 .growOnly = .value 1 .both ∧
      powerOutcome 2 .growOnly 0 .both = .value 1 .both ∧
      powerOutcome (1 / 2) .growOnly 0 .growOnly = .value 1 .both := by
  native_decide

/- Negative power uses the rounded reciprocal base and swaps the exponent's directions first. -/
example :
    powerOutcome 2 .growOnly (-1) .fixed = .value (1 / 2) .shrinkOnly ∧
      powerOutcome (-2) .growOnly (-1) .fixed = .value (-1 / 2) .both ∧
      powerOutcome (1 / 2) .fixed (-2) .growOnly = .value 4 .shrinkOnly := by
  native_decide

/- Equal current results do not imply equal polarity: conservative provenance remains observable. -/
example :
    (NumericValidationOp.ordinary .greater).evalArithmetic
        (.ok (powerOutcome 0 .fixed 0 .growOnly)) (.ok (.value 0 .fixed)) =
          .fired .omission ∧
      (NumericValidationOp.ordinary .greater).evalArithmetic
        (.ok (powerOutcome 0 .fixed 0 .both)) (.ok (.value 0 .fixed)) =
          .fired .value ∧
      (NumericValidationOp.ordinary .greater).evalArithmetic
        (.ok (powerOutcome 5 .fixed 0 .growOnly)) (.ok (.value 0 .fixed)) =
          .fired .value ∧
      (NumericValidationOp.ordinary .greater).evalArithmetic
        (.ok (powerOutcome (1 / 2) .fixed 0 .growOnly)) (.ok (.value 0 .fixed)) =
          .fired .omission := by
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

/- A fixed divisor's sign changes the polarity of the same zero-valued quotient. -/
example : (NumericValidationOp.ordinary .greaterEqual).evalArithmetic
    (.ok (NumericArithmeticOutcome.divide
      (.value 0 .growOnly) (.value 2 .fixed))) (.ok (.value 0 .fixed)) = .fired .value := by
  native_decide

example : (NumericValidationOp.ordinary .less).evalArithmetic
    (.ok (NumericArithmeticOutcome.divide
      (.value 0 .growOnly) (.value 2 .fixed))) (.ok (.value 1 .fixed)) = .fired .omission := by
  native_decide

example : (NumericValidationOp.ordinary .greaterEqual).evalArithmetic
    (.ok (NumericArithmeticOutcome.divide
      (.value 0 .growOnly) (.value (-2) .fixed))) (.ok (.value 0 .fixed)) = .fired .omission := by
  native_decide

example : (NumericValidationOp.ordinary .less).evalArithmetic
    (.ok (NumericArithmeticOutcome.divide
      (.value 0 .growOnly) (.value (-2) .fixed))) (.ok (.value 1 .fixed)) = .fired .value := by
  native_decide

example : (NumericValidationOp.ordinary .greaterEqual).evalArithmetic
    (.ok (NumericArithmeticOutcome.divide
      (.value 1 .fixed) (.value 0 .both))) (.ok (.value 0 .fixed)) = .notFired := by
  native_decide

end A12Kernel.Conformance.NumericFillability
