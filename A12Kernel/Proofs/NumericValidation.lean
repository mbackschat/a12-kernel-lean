import A12Kernel.Elaboration.NumericValidation

/-! # Checked numeric-validation laws -/

namespace A12Kernel

/-- Eliminate the model-validity certificate carried by a checked comparison. -/
theorem checkedNumericFixedRight_modelWellFormed
    (checked : CheckedNumericFixedRightComparison model) :
    model.validate.isOk = true :=
  checked.modelWellFormed

/-- Eliminate the core static-legality certificate carried by a checked comparison. -/
theorem checkedNumericFixedRight_wellFormed
    (checked : CheckedNumericFixedRightComparison model) :
    checked.core.WellFormed model checked.rowGroup :=
  checked.wellFormed

theorem numericArithmeticFixedRight_formalInvalid_is_unknown
    (op : NumericComparisonOp) (cause : FormalCause) (expected : Rat) :
    op.evalArithmeticFixedRight (.error cause) expected = .unknown := by
  rfl

theorem numericArithmeticFixedRight_domainFailure_is_notFired
    (op : NumericComparisonOp) (expected : Rat) :
    op.evalArithmeticFixedRight (.ok .notEvaluated) expected = .notFired := by
  rfl

theorem numericArithmeticFixedRight_value_delegates
    (op : NumericComparisonOp) (amount expected : Rat)
    (fillability : NumericFillability) :
    op.evalArithmeticFixedRight (.ok (.value amount fillability)) expected =
      op.evalFixedRight (.value amount fillability) expected := by
  rfl

private theorem rootDivision_plain
    (expression numerator denominator : LoweredNumericExpr Atom)
    (plain : expression.isPlainArithmetic = true)
    (division : expression.rootDivision? = some (numerator, denominator)) :
    numerator.isPlainArithmetic = true ∧
      denominator.isPlainArithmetic = true := by
  cases expression with
  | atom | literal | power | round =>
      simp [LoweredNumericExpr.rootDivision?] at division
  | binary op left right =>
      cases op <;>
        simp_all [LoweredNumericExpr.rootDivision?,
          LoweredNumericExpr.isPlainArithmetic, Bool.and_eq_true]

private theorem lowerMultiply_plain
    (left right : LoweredNumericExpr Atom)
    (leftPlain : left.isPlainArithmetic = true)
    (rightPlain : right.isPlainArithmetic = true) :
    (LoweredNumericExpr.lowerMultiply left right).isPlainArithmetic = true := by
  cases leftDivision : left.rootDivision? with
  | none =>
      cases rightDivision : right.rootDivision? with
      | none =>
          simp [LoweredNumericExpr.lowerMultiply, leftDivision, rightDivision,
            LoweredNumericExpr.isPlainArithmetic, leftPlain, rightPlain]
      | some rightPair =>
          obtain ⟨rightNumerator, rightDenominator⟩ := rightPair
          have rightParts :=
            rootDivision_plain right rightNumerator rightDenominator
              rightPlain rightDivision
          simp [LoweredNumericExpr.lowerMultiply, leftDivision, rightDivision,
            LoweredNumericExpr.isPlainArithmetic, leftPlain,
            rightParts.1, rightParts.2]
  | some leftPair =>
      obtain ⟨leftNumerator, leftDenominator⟩ := leftPair
      have leftParts :=
        rootDivision_plain left leftNumerator leftDenominator
          leftPlain leftDivision
      cases rightDivision : right.rootDivision? with
      | none =>
          simp [LoweredNumericExpr.lowerMultiply, leftDivision, rightDivision,
            LoweredNumericExpr.isPlainArithmetic, rightPlain,
            leftParts.1, leftParts.2]
      | some rightPair =>
          obtain ⟨rightNumerator, rightDenominator⟩ := rightPair
          have rightParts :=
            rootDivision_plain right rightNumerator rightDenominator
              rightPlain rightDivision
          simp [LoweredNumericExpr.lowerMultiply, leftDivision, rightDivision,
            LoweredNumericExpr.isPlainArithmetic,
            leftParts.1, leftParts.2, rightParts.1, rightParts.2]

private theorem authoredNumericLower_plain
    (expression : AuthoredNumericExpr Atom)
    (plain : expression.isPlainArithmetic = true) :
    expression.lowerForEvaluation.isPlainArithmetic = true := by
  induction expression with
  | atom | literal => rfl
  | group body ih =>
      exact ih plain
  | binary op left right leftIh rightIh =>
      simp only [AuthoredNumericExpr.isPlainArithmetic, Bool.and_eq_true] at plain
      cases op with
      | add | subtract | divide =>
          simpa only [AuthoredNumericExpr.lowerForEvaluation,
            LoweredNumericExpr.isPlainArithmetic, Bool.and_eq_true]
            using And.intro (leftIh plain.1) (rightIh plain.2)
      | multiply =>
          exact lowerMultiply_plain _ _
            (leftIh plain.1) (rightIh plain.2)
  | power | round =>
      simp [AuthoredNumericExpr.isPlainArithmetic] at plain

private theorem loweredPlainValidation_isSome
    (expression : LoweredNumericExpr Atom)
    (read : Atom → Except FormalCause NumericArithmeticOutcome)
    (plain : expression.isPlainArithmetic = true) :
    (expression.evalPlainValidation? read).isSome = true := by
  induction expression with
  | atom | literal => rfl
  | binary op left right leftIh rightIh =>
      simp only [LoweredNumericExpr.isPlainArithmetic, Bool.and_eq_true] at plain
      have leftSome := leftIh plain.1
      have rightSome := rightIh plain.2
      cases leftResult : left.evalPlainValidation? read with
      | none =>
          simp [leftResult] at leftSome
      | some leftOutcome =>
          cases rightResult : right.evalPlainValidation? read with
          | none =>
              simp [rightResult] at rightSome
          | some rightOutcome =>
              simp [LoweredNumericExpr.evalPlainValidation?,
                leftResult, rightResult]
  | power | round =>
      simp [LoweredNumericExpr.isPlainArithmetic] at plain

private theorem numericFixedRight_wellFormed_isPlain
    (comparison : NumericFixedRightComparison)
    (wellFormed : comparison.WellFormed model rowGroup) :
    comparison.left.isPlainArithmetic = true := by
  simp only [NumericFixedRightComparison.WellFormed,
    NumericFixedRightComparison.wellFormedBool, Bool.and_eq_true] at wellFormed
  exact wellFormed.1.1.1.2

/-- The checked certificate makes the evaluator's unsupported-shape fallback unreachable. -/
theorem checkedNumericFixedRight_evaluation_isSome
    (checked : CheckedNumericFixedRightComparison model)
    (context : FlatContext) :
    (checked.core.left.lowerForEvaluation.evalPlainValidation?
      context.resolveNumericArithmetic).isSome = true := by
  apply loweredPlainValidation_isSome
  apply authoredNumericLower_plain
  exact numericFixedRight_wellFormed_isPlain checked.core checked.wellFormed

/-- A direct atom in the new core evaluates exactly like the older direct Number-field core. -/
theorem numericFixedRight_atom_agrees_flat
    (op : NumericComparisonOp) (field : FlatNumberField)
    (right : DecodedNumericLiteral) (context : FlatContext) :
    ({ op, left := .atom field, right } :
      NumericFixedRightComparison).evalSelected context =
        (FlatComparison.number op field right.value).eval context := by
  cases observed : context.resolveNumberComparisonOperand field <;>
    simp only [NumericFixedRightComparison.evalSelected,
      AuthoredNumericExpr.lowerForEvaluation,
      LoweredNumericExpr.evalPlainValidation?,
      FlatContext.resolveNumericArithmetic, FlatComparison.eval,
      NumericComparisonOp.evalArithmeticFixedRight,
      NumericComparisonOp.evalFixedRight, observed]

/-- Full validation gates a plain comparison before any empty-Number substitution can fire. -/
theorem checkedNumericFixedRight_emptyRow_notFired
    (checked : CheckedNumericFixedRightComparison model)
    (context : FlatContext) :
    checked.evalFull context false = .notFired := by
  rfl

end A12Kernel
