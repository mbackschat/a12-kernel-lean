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
    (op : NumericValidationOp) (cause : FormalCause)
    (right : Except FormalCause NumericArithmeticOutcome) :
    op.evalArithmetic (.error cause) right = .unknown := by
  rfl

theorem numericArithmetic_formalInvalid_right_is_unknown
    (op : NumericValidationOp) (cause : FormalCause)
    (left : Except FormalCause NumericArithmeticOutcome) :
    op.evalArithmetic left (.error cause) = .unknown := by
  cases left <;> rfl

theorem numericArithmetic_domainFailure_left_is_notFired
    (op : NumericValidationOp) (right : NumericArithmeticOutcome) :
    op.evalArithmetic (.ok .notEvaluated) (.ok right) = .notFired := by
  rfl

theorem numericArithmetic_domainFailure_right_is_notFired
    (op : NumericValidationOp) (left : NumericArithmeticOutcome) :
    op.evalArithmetic (.ok left) (.ok .notEvaluated) = .notFired := by
  cases left <;> rfl

theorem numericArithmetic_values_delegate
    (op : NumericValidationOp) (left right : Rat)
    (leftFill rightFill : NumericFillability) :
    op.evalArithmetic
        (.ok (.value left leftFill)) (.ok (.value right rightFill)) =
      op.eval (.value left leftFill) (.value right rightFill) := by
  rfl

/-- A reached checked-validation power node delegates value and directional metadata together to the shared power outcome. -/
theorem numericValidation_power_values_delegate
    (read : Atom → Except FormalCause NumericArithmeticOutcome)
    (base exponent : LoweredNumericExpr Atom)
    (baseValue exponentValue : Rat)
    (baseFill exponentFill : NumericFillability)
    (baseEvaluated :
      base.evalPlainValidation? read =
        some (.ok (.value baseValue baseFill)))
    (exponentEvaluated :
      exponent.evalPlainValidation? read =
        some (.ok (.value exponentValue exponentFill))) :
    (LoweredNumericExpr.power base exponent).evalPlainValidation? read =
      some (.ok (NumericArithmeticOutcome.power
        (.value baseValue baseFill) (.value exponentValue exponentFill))) := by
  simp only [LoweredNumericExpr.evalPlainValidation?]
  rw [baseEvaluated, exponentEvaluated]
  rfl

/-- The new closed dispatch leaves every ordinary operator's static-scale rule unchanged. -/
theorem ordinaryNumericValidation_acceptsScales
    (op : NumericComparisonOp) (left right : NumericScaleSummary) :
    (NumericValidationOp.ordinary op).acceptsScales left right =
      op.acceptsScales left right := by
  rfl

/-- The new closed dispatch leaves every ordinary primitive verdict unchanged. -/
theorem ordinaryNumericValidation_eval
    (op : NumericComparisonOp) (left right : NumericOperand) :
    (NumericValidationOp.ordinary op).eval left right =
      op.eval left right := by
  rfl

/-- Every fixed tolerance range deliberately bypasses the exact-comparison scale gate. -/
theorem numericTolerance_acceptsScales
    (range : NumericToleranceRange) (left right : NumericScaleSummary) :
    (NumericValidationOp.tolerance range).acceptsScales left right = true := by
  rfl

/-- Suppressing the one supported warning admits every exact-scale pair, including an unknown derived scale. -/
theorem numericValidation_scaleSuppression_accepts
    (op : NumericValidationOp) (left right : NumericScaleSummary) :
    op.acceptsScalesWithSuppression true left right = true := by
  cases op with
  | ordinary comparison => cases comparison <;> rfl
  | tolerance _ => rfl

/-- Without the directive, the checked consumer retains the ordinary scale gate exactly. -/
theorem numericValidation_withoutScaleSuppression
    (op : NumericValidationOp) (left right : NumericScaleSummary) :
    op.acceptsScalesWithSuppression false left right =
      op.acceptsScales left right := by
  cases op with
  | ordinary comparison => cases comparison <;> rfl
  | tolerance _ => rfl

/-- The parser warning directive affects admission only; once checked, it cannot change evaluation. -/
theorem numericComparison_scaleSuppression_runtimeIrrelevant
    (comparison : NumericComparison) (context : FlatContext) (suppressed : Bool) :
    ({ comparison with suppressExactScaleWarning := suppressed }).evalSelected context =
      comparison.evalSelected context := by
  rfl

private theorem rootDivision_plain
    (expression numerator denominator : LoweredNumericExpr Atom)
    (plain : expression.isPlainArithmetic = true)
    (division : expression.rootDivision? = some (numerator, denominator)) :
    numerator.isPlainArithmetic = true ∧
      denominator.isPlainArithmetic = true := by
  cases expression with
  | atom | literal | power | abs | extremum | round =>
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
  | power base exponent baseIh exponentIh =>
      simp only [AuthoredNumericExpr.isPlainArithmetic, Bool.and_eq_true] at plain
      simpa only [AuthoredNumericExpr.lowerForEvaluation,
        LoweredNumericExpr.isPlainArithmetic, Bool.and_eq_true]
        using And.intro (baseIh plain.1) (exponentIh plain.2)
  | abs | extremum | round =>
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
  | power base exponent baseIh exponentIh =>
      simp only [LoweredNumericExpr.isPlainArithmetic, Bool.and_eq_true] at plain
      have baseSome := baseIh plain.1
      have exponentSome := exponentIh plain.2
      cases baseResult : base.evalPlainValidation? read with
      | none => simp [baseResult] at baseSome
      | some baseOutcome =>
          cases exponentResult : exponent.evalPlainValidation? read with
          | none => simp [exponentResult] at exponentSome
          | some exponentOutcome =>
              simp [LoweredNumericExpr.evalPlainValidation?,
                baseResult, exponentResult]
  | abs | extremum | round =>
      simp [LoweredNumericExpr.isPlainArithmetic] at plain

private theorem authoredNumericLower_directExtremumChain
    (expected : NumericExtremumOp)
    (expression : AuthoredNumericExpr Atom)
    (direct : expression.isDirectExtremumChain expected = true) :
    expression.lowerForEvaluation.directExtremumConstantUse? expected =
      expression.directExtremumConstantUse? expected := by
  induction expression with
  | atom | literal => rfl
  | extremum actual left right leftIh rightIh =>
      by_cases same : actual = expected
      · subst actual
        cases leftUse : left.directExtremumConstantUse? expected with
        | none =>
            simp [AuthoredNumericExpr.isDirectExtremumChain,
              AuthoredNumericExpr.directExtremumConstantUse?, leftUse] at direct
        | some constantUsed =>
            have leftDirect : left.isDirectExtremumChain expected = true := by
              simp [AuthoredNumericExpr.isDirectExtremumChain, leftUse]
            have leftPreserved := leftIh leftDirect
            cases right <;>
              simp [AuthoredNumericExpr.isDirectExtremumChain,
                AuthoredNumericExpr.directExtremumConstantUse?,
                LoweredNumericExpr.directExtremumConstantUse?,
                AuthoredNumericExpr.lowerForEvaluation,
                leftUse, leftPreserved] at direct ⊢
      · simp [AuthoredNumericExpr.isDirectExtremumChain,
          AuthoredNumericExpr.directExtremumConstantUse?, same] at direct
  | group | binary | power | abs | round =>
      simp [AuthoredNumericExpr.isDirectExtremumChain,
        AuthoredNumericExpr.directExtremumConstantUse?] at direct

private theorem authoredNumericLower_directValueFunction
    (expression : AuthoredNumericExpr Atom)
    (direct : expression.isDirectValueFunction = true) :
    expression.lowerForEvaluation.isDirectValueFunction = true := by
  cases expression with
  | atom | literal | group | binary | power =>
      simp [AuthoredNumericExpr.isDirectValueFunction] at direct
  | abs body =>
      cases body <;>
        simp [AuthoredNumericExpr.isDirectValueFunction,
          AuthoredNumericExpr.lowerForEvaluation,
          LoweredNumericExpr.isDirectValueFunction] at direct ⊢
  | round mode places body =>
      cases body <;>
        simp [AuthoredNumericExpr.isDirectValueFunction,
          AuthoredNumericExpr.lowerForEvaluation,
          LoweredNumericExpr.isDirectValueFunction] at direct ⊢
  | extremum op left right =>
      have preserved := authoredNumericLower_directExtremumChain op
        (.extremum op left right) direct
      simp only [AuthoredNumericExpr.isDirectValueFunction] at direct
      unfold AuthoredNumericExpr.isDirectExtremumChain at direct
      unfold LoweredNumericExpr.isDirectValueFunction
      unfold LoweredNumericExpr.isDirectExtremumChain
      simp only [AuthoredNumericExpr.lowerForEvaluation]
      simp only [AuthoredNumericExpr.lowerForEvaluation] at preserved
      rw [preserved]
      exact direct

private theorem authoredNumericLower_admittedValidation
    (expression : AuthoredNumericExpr Atom)
    (admitted : expression.isAdmittedNumericOperation = true) :
    expression.lowerForEvaluation.isAdmittedValidation = true := by
  simp only [AuthoredNumericExpr.isAdmittedNumericOperation,
    Bool.or_eq_true] at admitted
  simp only [LoweredNumericExpr.isAdmittedValidation, Bool.or_eq_true]
  cases admitted with
  | inl plain => exact Or.inl (authoredNumericLower_plain expression plain)
  | inr direct =>
      exact Or.inr
        (authoredNumericLower_directValueFunction expression direct)

private theorem loweredDirectExtremum_constantUse_preserved
    (expected : NumericExtremumOp)
    (expression : LoweredNumericExpr Atom)
    (read : Atom → Except FormalCause NumericArithmeticOutcome) :
    (expression.evalDirectExtremumWithConstantUse? expected read).map Prod.snd =
      expression.directExtremumConstantUse? expected := by
  induction expression with
  | atom | literal => rfl
  | extremum actual left right leftIh rightIh =>
      by_cases same : actual = expected
      · subst actual
        cases evaluated : left.evalDirectExtremumWithConstantUse? expected read with
        | none =>
            have leftUse : left.directExtremumConstantUse? expected = none := by
              simpa [evaluated] using leftIh.symm
            simp [LoweredNumericExpr.evalDirectExtremumWithConstantUse?,
              LoweredNumericExpr.directExtremumConstantUse?, evaluated, leftUse]
        | some result =>
            rcases result with ⟨leftOutcome, constantUsed⟩
            have leftUse :
                left.directExtremumConstantUse? expected = some constantUsed := by
              simpa [evaluated] using leftIh.symm
            cases right <;> cases constantUsed <;>
              simp [LoweredNumericExpr.evalDirectExtremumWithConstantUse?,
                LoweredNumericExpr.directExtremumConstantUse?,
                evaluated, leftUse]
      · simp [LoweredNumericExpr.evalDirectExtremumWithConstantUse?,
          LoweredNumericExpr.directExtremumConstantUse?, same]
  | binary | power | abs | round => rfl

private theorem loweredDirectExtremum_isSome
    (expected : NumericExtremumOp)
    (expression : LoweredNumericExpr Atom)
    (read : Atom → Except FormalCause NumericArithmeticOutcome)
    (direct : expression.isDirectExtremumChain expected = true) :
    (expression.evalDirectExtremum? expected read).isSome = true := by
  have preserved :=
    loweredDirectExtremum_constantUse_preserved expected expression read
  cases evaluated : expression.evalDirectExtremumWithConstantUse? expected read with
  | none =>
      rw [evaluated] at preserved
      simp only [Option.map_none] at preserved
      unfold LoweredNumericExpr.isDirectExtremumChain at direct
      rw [← preserved] at direct
      simp at direct
  | some result =>
      simp [LoweredNumericExpr.evalDirectExtremum?, evaluated]

private theorem loweredAdmittedValidation_isSome
    (expression : LoweredNumericExpr Atom)
    (read : Atom → Except FormalCause NumericArithmeticOutcome)
    (admitted : expression.isAdmittedValidation = true) :
    (expression.evalAdmittedValidation? read).isSome = true := by
  simp only [LoweredNumericExpr.isAdmittedValidation,
    Bool.or_eq_true] at admitted
  cases admitted with
  | inl plain =>
      have plainSome := loweredPlainValidation_isSome expression read plain
      cases expression with
      | atom | literal | binary | power =>
          simpa [LoweredNumericExpr.evalAdmittedValidation?] using plainSome
      | abs | extremum | round =>
          simp [LoweredNumericExpr.isPlainArithmetic] at plain
  | inr direct =>
      cases expression with
      | atom | literal | binary | power =>
          simp [LoweredNumericExpr.isDirectValueFunction] at direct
      | abs body =>
          cases body <;>
            simp [LoweredNumericExpr.isDirectValueFunction,
              LoweredNumericExpr.evalAdmittedValidation?] at direct ⊢
      | round mode places body =>
          cases body <;>
            simp [LoweredNumericExpr.isDirectValueFunction,
              LoweredNumericExpr.evalAdmittedValidation?] at direct ⊢
      | extremum op left right =>
          have evaluated := loweredDirectExtremum_isSome op
            (.extremum op left right) read direct
          simpa [LoweredNumericExpr.evalAdmittedValidation?] using evaluated

private theorem numericComparison_wellFormed_sidesAdmitted
    (comparison : NumericComparison)
    (wellFormed : comparison.WellFormed model rowGroup) :
    comparison.left.isAdmittedNumericOperation = true ∧
      comparison.right.isAdmittedNumericOperation = true := by
  simp only [NumericComparison.WellFormed,
    NumericComparison.wellFormedBool, Bool.and_eq_true] at wellFormed
  exact ⟨wellFormed.1.1.1.1.1.1.2, wellFormed.1.1.1.1.1.2⟩

/-- The checked certificate makes both evaluator unsupported-shape fallbacks unreachable. -/
theorem checkedNumericComparison_evaluations_areSome
    (checked : CheckedNumericComparison model)
    (context : FlatContext) :
    (checked.core.left.lowerForEvaluation.evalAdmittedValidation?
        context.resolveNumericArithmetic).isSome = true ∧
      (checked.core.right.lowerForEvaluation.evalAdmittedValidation?
        context.resolveNumericArithmetic).isSome = true := by
  have admitted :=
    numericComparison_wellFormed_sidesAdmitted checked.core checked.wellFormed
  exact ⟨
    loweredAdmittedValidation_isSome _ _
      (authoredNumericLower_admittedValidation _ admitted.1),
    loweredAdmittedValidation_isSome _ _
      (authoredNumericLower_admittedValidation _ admitted.2)⟩

/-- One direct constant is admitted on either side of the first extremum node. -/
theorem numericValidation_extremum_singleConstant_admitted
    (op : NumericExtremumOp) (atom : Atom)
    (constant : DecodedNumericLiteral) :
    (AuthoredNumericExpr.extremum op (.atom atom)
        (.literal constant)).isDirectValueFunction = true ∧
      (AuthoredNumericExpr.extremum op (.literal constant)
        (.atom atom)).isDirectValueFunction = true := by
  simp [AuthoredNumericExpr.isDirectValueFunction,
    AuthoredNumericExpr.isDirectExtremumChain,
    AuthoredNumericExpr.directExtremumConstantUse?]

/-- A direct constant reaches the existing exact extremum selector as a fixed operand. -/
theorem numericValidation_extremum_atom_constant_delegates
    (op : NumericExtremumOp) (atom : Atom) (constant : Rat)
    (read : Atom → Except FormalCause NumericArithmeticOutcome) :
    (LoweredNumericExpr.extremum op (.atom atom)
      (.literal constant)).evalDirectExtremum? op read =
        some (op.selectValidationOutcome (read atom)
          (.ok (.value constant .fixed))) := by
  simp [LoweredNumericExpr.evalDirectExtremum?,
    LoweredNumericExpr.evalDirectExtremumWithConstantUse?]

/-- A second direct constant is rejected rather than silently widening the authored list contract. -/
theorem numericValidation_extremum_twoConstants_rejected
    (op : NumericExtremumOp) (atom : Atom)
    (first second : DecodedNumericLiteral) :
    (AuthoredNumericExpr.extremum op
      (.extremum op (.atom atom) (.literal first))
      (.literal second)).isDirectValueFunction = false := by
  simp [AuthoredNumericExpr.isDirectValueFunction,
    AuthoredNumericExpr.isDirectExtremumChain,
    AuthoredNumericExpr.directExtremumConstantUse?]

/-- A direct atom and literal evaluate exactly like the shared low-level Number-field evaluator. -/
theorem numericComparison_atom_literal_agrees_flat
    (op : NumericComparisonOp) (field : FlatNumberField)
    (right : DecodedNumericLiteral) (context : FlatContext) :
    ({ op := .ordinary op, left := .atom field, right := .literal right } :
      NumericComparison).evalSelected context =
        (FlatComparison.number (.ordinary op) field right.value).eval context := by
  cases observed : context.resolveNumberComparisonOperand field <;>
    simp only [NumericComparison.evalSelected,
      AuthoredNumericExpr.lowerForEvaluation,
      LoweredNumericExpr.evalAdmittedValidation?,
      LoweredNumericExpr.evalPlainValidation?,
      FlatContext.resolveNumericArithmetic, FlatComparison.eval,
      NumericValidationOp.evalArithmetic, NumericValidationOp.eval,
      NumericValidationOp.evalFixedRight,
      NumericComparisonOp.eval, observed]

/-- A rounded left atom against a literal delegates to the existing rounded-operand semantics for every mode and for both ordinary and tolerance consumers. -/
theorem numericValidation_round_atom_literal_delegates
    (op : NumericValidationOp) (mode : DecimalRoundingMode)
    (places : RoundingPlaces) (field : FlatNumberField)
    (right : DecodedNumericLiteral) (context : FlatContext) :
    ({ op, left := .round mode places (.atom field), right := .literal right } :
      NumericComparison).evalSelected context =
        op.eval ((context.resolveNumberComparisonOperand field).round mode places)
          (.value right.value .fixed) := by
  cases op <;>
    cases observed : context.resolveNumberComparisonOperand field <;>
    simp [NumericComparison.evalSelected,
      AuthoredNumericExpr.lowerForEvaluation,
      LoweredNumericExpr.evalAdmittedValidation?,
      LoweredNumericExpr.evalPlainValidation?,
      FlatContext.resolveNumericArithmetic,
      NumericArithmeticOutcome.round, NumericArithmeticOutcome.mapValue,
      NumericOperand.round, NumericOperand.mapValue,
      NumericValidationOp.evalArithmetic,
      NumericValidationOp.eval, NumericComparisonOp.eval,
      NumericToleranceRange.eval, observed]

/-- An absolute-valued left atom against a literal delegates to the shared operand transformation for every ordinary and tolerance consumer. -/
theorem numericValidation_abs_atom_literal_delegates
    (op : NumericValidationOp) (field : FlatNumberField)
    (right : DecodedNumericLiteral) (context : FlatContext) :
    ({ op, left := .abs (.atom field), right := .literal right } :
      NumericComparison).evalSelected context =
        op.eval (context.resolveNumberComparisonOperand field).absolute
          (.value right.value .fixed) := by
  cases op <;>
    cases observed : context.resolveNumberComparisonOperand field <;>
    simp [NumericComparison.evalSelected,
      AuthoredNumericExpr.lowerForEvaluation,
      LoweredNumericExpr.evalAdmittedValidation?,
      LoweredNumericExpr.evalPlainValidation?,
      FlatContext.resolveNumericArithmetic,
      NumericArithmeticOutcome.absolute, NumericArithmeticOutcome.mapValue,
      NumericOperand.absolute, NumericOperand.mapValue,
      NumericValidationOp.evalArithmetic, NumericValidationOp.eval,
      NumericComparisonOp.eval, NumericToleranceRange.eval, observed]

/-- A direct tolerance core atom/literal pair delegates to the existing pure tolerance seam. -/
theorem numericTolerance_atom_literal_delegates
    (range : NumericToleranceRange) (field : FlatNumberField)
    (right : DecodedNumericLiteral) (context : FlatContext) :
    ({ op := .tolerance range, left := .atom field, right := .literal right } :
      NumericComparison).evalSelected context =
        range.eval (context.resolveNumberComparisonOperand field)
          (.value right.value .fixed) := by
  cases observed : context.resolveNumberComparisonOperand field <;>
    simp only [NumericComparison.evalSelected,
      AuthoredNumericExpr.lowerForEvaluation,
      LoweredNumericExpr.evalAdmittedValidation?,
      LoweredNumericExpr.evalPlainValidation?,
      FlatContext.resolveNumericArithmetic,
      NumericValidationOp.evalArithmetic, NumericValidationOp.eval,
      NumericToleranceRange.eval, observed]

/-- Full validation gates a checked numeric condition before any empty-Number substitution can fire. -/
theorem checkedNumericComparison_emptyRow_notFired
    (checked : CheckedNumericComparison model)
    (context : FlatContext) :
    checked.evalFull context false = .notFired := by
  rfl

end A12Kernel
