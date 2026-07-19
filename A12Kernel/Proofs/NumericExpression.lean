import A12Kernel.Elaboration.NumericExpression

/-! # Numeric-expression lowering laws -/

namespace A12Kernel

theorem authoredNumericSummary_group
    (atomSummary : Atom → NumericScaleSummary)
    (body : AuthoredNumericExpr Atom) :
    (AuthoredNumericExpr.group body).summary? atomSummary =
      body.summary? atomSummary := by
  rfl

theorem authoredNumericGroup_not_simple_constant
    (body : AuthoredNumericExpr Atom) :
    (AuthoredNumericExpr.group body).isSimpleNonnegativeConstant = false := by
  rfl

theorem authoredNumericLower_group
    (body : AuthoredNumericExpr Atom) :
    (AuthoredNumericExpr.group body).lowerForEvaluation =
      body.lowerForEvaluation := by
  rfl

theorem lowerMultiply_two_divisions
    (leftNumerator leftDenominator rightNumerator rightDenominator :
      LoweredNumericExpr Atom) :
    LoweredNumericExpr.lowerMultiply
      (.binary .divide leftNumerator leftDenominator)
      (.binary .divide rightNumerator rightDenominator) =
        .binary .divide
          (.binary .multiply leftNumerator rightNumerator)
          (.binary .multiply leftDenominator rightDenominator) := by
  rfl

theorem lowerMultiply_left_division
    (numerator denominator right : LoweredNumericExpr Atom)
    (rightNotDivision : right.rootDivision? = none) :
    LoweredNumericExpr.lowerMultiply
      (.binary .divide numerator denominator) right =
        .binary .divide (.binary .multiply right numerator) denominator := by
  unfold LoweredNumericExpr.lowerMultiply
  rw [rightNotDivision]
  rfl

theorem lowerMultiply_right_division
    (left numerator denominator : LoweredNumericExpr Atom)
    (leftNotDivision : left.rootDivision? = none) :
    LoweredNumericExpr.lowerMultiply left
      (.binary .divide numerator denominator) =
        .binary .divide (.binary .multiply left numerator) denominator := by
  unfold LoweredNumericExpr.lowerMultiply
  rw [leftNotDivision]
  rfl

theorem lowerMultiply_without_divisions
    (left right : LoweredNumericExpr Atom)
    (leftNotDivision : left.rootDivision? = none)
    (rightNotDivision : right.rootDivision? = none) :
    LoweredNumericExpr.lowerMultiply left right =
      .binary .multiply left right := by
  unfold LoweredNumericExpr.lowerMultiply
  rw [leftNotDivision, rightNotDivision]

/-- A numerator division extracted into a newly constructed product is deliberately not revisited during the same pass. -/
theorem lowerMultiply_nested_numerator_once
    (factor numerator nestedDenominator denominator : LoweredNumericExpr Atom)
    (factorNotDivision : factor.rootDivision? = none) :
    LoweredNumericExpr.lowerMultiply factor
      (.binary .divide
        (.binary .divide numerator nestedDenominator)
        denominator) =
      .binary .divide
        (.binary .multiply factor
          (.binary .divide numerator nestedDenominator))
        denominator := by
  unfold LoweredNumericExpr.lowerMultiply
  rw [factorNotDivision]
  rfl

theorem authoredNumericEval_uses_lowered_tree
    (expression : AuthoredNumericExpr Atom)
    (read : Atom → NumericArithmeticResult) :
    expression.evalValue read =
      expression.lowerForEvaluation.evalValue read := by
  rfl

end A12Kernel
