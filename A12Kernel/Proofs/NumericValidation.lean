import A12Kernel.Elaboration.NumericValidation

/-! # Checked numeric-validation laws -/

namespace A12Kernel

/-- Eliminate the model-validity certificate carried by a checked comparison. -/
theorem checkedNumericComparison_modelWellFormed
    (checked : CheckedNumericComparison model) :
    model.validate.isOk = true :=
  checked.modelWellFormed

/-- Eliminate the core static-legality certificate carried by a checked comparison. -/
theorem checkedNumericComparison_wellFormed
    (checked : CheckedNumericComparison model) :
    checked.core.WellFormed model checked.rowGroup :=
  checked.wellFormed

theorem numericArithmetic_formalInvalid_left_is_unknown
    (op : NumericComparisonOp) (cause : FormalCause)
    (right : Except FormalCause NumericArithmeticOutcome) :
    op.evalArithmetic (.error cause) right = .unknown := by
  rfl

theorem numericArithmetic_formalInvalid_right_is_unknown
    (op : NumericComparisonOp) (cause : FormalCause)
    (left : Except FormalCause NumericArithmeticOutcome) :
    op.evalArithmetic left (.error cause) = .unknown := by
  cases left <;> rfl

theorem numericArithmetic_domainFailure_left_is_notFired
    (op : NumericComparisonOp) (right : NumericArithmeticOutcome) :
    op.evalArithmetic (.ok .notEvaluated) (.ok right) = .notFired := by
  rfl

theorem numericArithmetic_domainFailure_right_is_notFired
    (op : NumericComparisonOp) (left : NumericArithmeticOutcome) :
    op.evalArithmetic (.ok left) (.ok .notEvaluated) = .notFired := by
  cases left <;> rfl

theorem numericArithmetic_values_delegate
    (op : NumericComparisonOp) (left right : Rat)
    (leftFill rightFill : NumericFillability) :
    op.evalArithmetic
        (.ok (.value left leftFill)) (.ok (.value right rightFill)) =
      op.eval (.value left leftFill) (.value right rightFill) := by
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

private theorem numericComparison_wellFormed_sidesPlain
    (comparison : NumericComparison)
    (wellFormed : comparison.WellFormed model rowGroup) :
    comparison.left.isPlainArithmetic = true ∧
      comparison.right.isPlainArithmetic = true := by
  simp only [NumericComparison.WellFormed,
    NumericComparison.wellFormedBool, Bool.and_eq_true] at wellFormed
  exact ⟨wellFormed.1.1.1.1.1.1.2, wellFormed.1.1.1.1.1.2⟩

/-- The checked certificate makes both evaluator unsupported-shape fallbacks unreachable. -/
theorem checkedNumericComparison_evaluations_areSome
    (checked : CheckedNumericComparison model)
    (context : FlatContext) :
    (checked.core.left.lowerForEvaluation.evalPlainValidation?
        context.resolveNumericArithmetic).isSome = true ∧
      (checked.core.right.lowerForEvaluation.evalPlainValidation?
        context.resolveNumericArithmetic).isSome = true := by
  have plain :=
    numericComparison_wellFormed_sidesPlain checked.core checked.wellFormed
  exact ⟨
    loweredPlainValidation_isSome _ _
      (authoredNumericLower_plain _ plain.1),
    loweredPlainValidation_isSome _ _
      (authoredNumericLower_plain _ plain.2)⟩

/-- A direct atom and literal evaluate exactly like the shared low-level Number-field evaluator. -/
theorem numericComparison_atom_literal_agrees_flat
    (op : NumericComparisonOp) (field : FlatNumberField)
    (right : DecodedNumericLiteral) (context : FlatContext) :
    ({ op, left := .atom field, right := .literal right } :
      NumericComparison).evalSelected context =
        (FlatComparison.number op field right.value).eval context := by
  cases observed : context.resolveNumberComparisonOperand field <;>
    simp only [NumericComparison.evalSelected,
      AuthoredNumericExpr.lowerForEvaluation,
      LoweredNumericExpr.evalPlainValidation?,
      FlatContext.resolveNumericArithmetic, FlatComparison.eval,
      NumericComparisonOp.evalArithmetic,
      NumericComparisonOp.evalFixedRight,
      NumericComparisonOp.eval, observed]

/-- Full validation gates a plain comparison before any empty-Number substitution can fire. -/
theorem checkedNumericComparison_emptyRow_notFired
    (checked : CheckedNumericComparison model)
    (context : FlatContext) :
    checked.evalFull context false = .notFired := by
  rfl

end A12Kernel
