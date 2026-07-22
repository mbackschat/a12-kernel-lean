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
    checked.core.WellFormedIn model checked.rowGroup checked.operandScope :=
  checked.wellFormed

/-- A resolved validation aggregate atom consumes the shared aggregate fold and only then enters the existing arithmetic-outcome domain. -/
theorem numericValidationAggregate_evaluatesThroughSharedFold
    (context : FlatContext) (op : NumericAggregateOp)
    (source : ResolvedNumericAggregateFields) :
    context.resolveNumericValidationAtom (.aggregate op source) =
      (source.evaluate op context.observeValidationAt).toValidationArithmetic := by
  rfl

/-- A missing checked String source gives `RangeAsNumber` the real zero together with its one possible movement direction. -/
theorem numericValidation_stringRange_empty_growOnly
    (context : FlatContext) (field : FlatStringField) (start finish : Nat)
    (observed : context.observeValidationAt field.id = .empty) :
    context.resolveNumericValidationAtom (.stringRange field start finish) =
      .ok (.value 0 .growOnly) := by
  simp [FlatContext.resolveNumericValidationAtom, observed]

/-- Once the String source is present, digits-only conversion or fallback zero is fixed; substring content does not itself carry omission potential. -/
theorem numericValidation_stringRange_value_fixed
    (context : FlatContext) (field : FlatStringField) (start finish : Nat)
    (value : String)
    (observed : context.observeValidationAt field.id = .value (.str value)) :
    context.resolveNumericValidationAtom (.stringRange field start finish) =
      .ok (.value (utf16RangeAsNatural value start finish) .fixed) := by
  simp [FlatContext.resolveNumericValidationAtom, observed]

/-- A reached formal cause survives the range conversion rather than becoming fallback zero. -/
theorem numericValidation_stringRange_unknown_preservesCause
    (context : FlatContext) (field : FlatStringField) (start finish : Nat)
    (cause : FormalCause)
    (observed : context.observeValidationAt field.id = .unknown cause) :
    context.resolveNumericValidationAtom (.stringRange field start finish) =
      .error cause := by
  simp [FlatContext.resolveNumericValidationAtom, observed]

/-- Missing admitted Enumeration/category conversion is numeric zero with both possible movement directions. -/
theorem numericValidation_fieldValueAsNumber_empty_both
    (context : FlatContext) (source : ResolvedFieldValueAsNumberSource)
    (observed : context.observeValidationAt source.fieldId = .empty) :
    context.resolveNumericValidationAtom (.fieldValueAsNumber source) =
      .ok (.value 0 .both) := by
  simp [FlatContext.resolveNumericValidationAtom, observed]

/-- A present admitted stored token is projected and parsed once; the resulting value is fixed. -/
theorem numericValidation_fieldValueAsNumber_value_fixed
    (context : FlatContext) (source : ResolvedFieldValueAsNumberSource)
    (stored : String) (amount : Rat)
    (observed : context.observeValidationAt source.fieldId =
      .value (.enum stored))
    (converted : source.valueForStored? stored = some amount) :
    context.resolveNumericValidationAtom (.fieldValueAsNumber source) =
      .ok (.value amount .fixed) := by
  simp [FlatContext.resolveNumericValidationAtom, observed, converted]

/-- A reached formal cause survives Enumeration/category conversion unchanged. -/
theorem numericValidation_fieldValueAsNumber_unknown_preservesCause
    (context : FlatContext) (source : ResolvedFieldValueAsNumberSource)
    (cause : FormalCause)
    (observed : context.observeValidationAt source.fieldId = .unknown cause) :
    context.resolveNumericValidationAtom (.fieldValueAsNumber source) =
      .error cause := by
  simp [FlatContext.resolveNumericValidationAtom, observed]

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
      base.evalUnaryArithmetic? read =
        some (.ok (.value baseValue baseFill)))
    (exponentEvaluated :
      exponent.evalUnaryArithmetic? read =
        some (.ok (.value exponentValue exponentFill))) :
    (LoweredNumericExpr.power base exponent).evalUnaryArithmetic? read =
      some (.ok (NumericArithmeticOutcome.power
        (.value baseValue baseFill) (.value exponentValue exponentFill))) := by
  simp only [LoweredNumericExpr.evalUnaryArithmetic?]
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

private theorem lowerMultiply_preserves
    (shape : LoweredNumericExpr Atom → Bool)
    (binaryClosed : ∀ op left right,
      shape left = true → shape right = true →
        shape (.binary op left right) = true)
    (divisionParts : ∀ numerator denominator,
      shape (.binary .divide numerator denominator) = true →
        shape numerator = true ∧ shape denominator = true)
    (left right : LoweredNumericExpr Atom)
    (leftShape : shape left = true)
    (rightShape : shape right = true) :
    shape (LoweredNumericExpr.lowerMultiply left right) = true := by
  have rootParts (expression numerator denominator : LoweredNumericExpr Atom)
      (expressionShape : shape expression = true)
      (division : expression.rootDivision? = some (numerator, denominator)) :
      shape numerator = true ∧ shape denominator = true := by
    cases expression with
    | atom | literal | power | abs | extremum | round =>
        simp [LoweredNumericExpr.rootDivision?] at division
    | binary op actualNumerator actualDenominator =>
        cases op with
        | add | subtract | multiply =>
            simp [LoweredNumericExpr.rootDivision?] at division
        | divide =>
            simp only [LoweredNumericExpr.rootDivision?] at division
            cases division
            exact divisionParts numerator denominator expressionShape
  cases leftDivision : left.rootDivision? with
  | none =>
      cases rightDivision : right.rootDivision? with
      | none =>
          simp only [LoweredNumericExpr.lowerMultiply, leftDivision,
            rightDivision]
          exact binaryClosed .multiply left right leftShape rightShape
      | some rightPair =>
          obtain ⟨rightNumerator, rightDenominator⟩ := rightPair
          have rightParts := rootParts right rightNumerator rightDenominator
            rightShape rightDivision
          simp only [LoweredNumericExpr.lowerMultiply, leftDivision,
            rightDivision]
          exact binaryClosed .divide _ _
            (binaryClosed .multiply left rightNumerator
              leftShape rightParts.1)
            rightParts.2
  | some leftPair =>
      obtain ⟨leftNumerator, leftDenominator⟩ := leftPair
      have leftParts := rootParts left leftNumerator leftDenominator
        leftShape leftDivision
      cases rightDivision : right.rootDivision? with
      | none =>
          simp only [LoweredNumericExpr.lowerMultiply, leftDivision,
            rightDivision]
          exact binaryClosed .divide _ _
            (binaryClosed .multiply right leftNumerator
              rightShape leftParts.1)
            leftParts.2
      | some rightPair =>
          obtain ⟨rightNumerator, rightDenominator⟩ := rightPair
          have rightParts := rootParts right rightNumerator rightDenominator
            rightShape rightDivision
          simp only [LoweredNumericExpr.lowerMultiply, leftDivision,
            rightDivision]
          exact binaryClosed .divide _ _
            (binaryClosed .multiply leftNumerator rightNumerator
              leftParts.1 rightParts.1)
            (binaryClosed .multiply leftDenominator rightDenominator
              leftParts.2 rightParts.2)

private theorem lowerMultiply_plain
    (left right : LoweredNumericExpr Atom)
    (leftPlain : left.isPlainArithmetic = true)
    (rightPlain : right.isPlainArithmetic = true) :
    (LoweredNumericExpr.lowerMultiply left right).isPlainArithmetic = true := by
  apply lowerMultiply_preserves LoweredNumericExpr.isPlainArithmetic
    (fun _ _ _ leftShape rightShape => by
      simpa [LoweredNumericExpr.isPlainArithmetic] using
        And.intro leftShape rightShape)
    (fun _ _ shape => by
      simpa [LoweredNumericExpr.isPlainArithmetic] using shape)
    left right leftPlain rightPlain

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

private theorem authoredPlain_isUnary
    (expression : AuthoredNumericExpr Atom)
    (plain : expression.isPlainArithmetic = true) :
    expression.isUnaryArithmetic = true := by
  induction expression with
  | atom | literal => rfl
  | group body ih => exact ih plain
  | binary op left right leftIh rightIh =>
      simp only [AuthoredNumericExpr.isPlainArithmetic,
        AuthoredNumericExpr.isUnaryArithmetic, Bool.and_eq_true] at plain ⊢
      exact ⟨leftIh plain.1, rightIh plain.2⟩
  | power left right leftIh rightIh =>
      simp only [AuthoredNumericExpr.isPlainArithmetic,
        AuthoredNumericExpr.isUnaryArithmetic, Bool.and_eq_true] at plain ⊢
      exact ⟨leftIh plain.1, rightIh plain.2⟩
  | abs | extremum | round =>
      simp [AuthoredNumericExpr.isPlainArithmetic] at plain

private theorem lowerMultiply_unary
    (left right : LoweredNumericExpr Atom)
    (leftUnary : left.isUnaryArithmetic = true)
    (rightUnary : right.isUnaryArithmetic = true) :
    (LoweredNumericExpr.lowerMultiply left right).isUnaryArithmetic = true := by
  apply lowerMultiply_preserves LoweredNumericExpr.isUnaryArithmetic
    (fun _ _ _ leftShape rightShape => by
      simpa [LoweredNumericExpr.isUnaryArithmetic] using
        And.intro leftShape rightShape)
    (fun _ _ shape => by
      simpa [LoweredNumericExpr.isUnaryArithmetic] using shape)
    left right leftUnary rightUnary

private theorem authoredNumericLower_unary
    (expression : AuthoredNumericExpr Atom)
    (unary : expression.isUnaryArithmetic = true) :
    expression.lowerForEvaluation.isUnaryArithmetic = true := by
  induction expression with
  | atom | literal => rfl
  | group body ih => exact ih unary
  | binary op left right leftIh rightIh =>
      simp only [AuthoredNumericExpr.isUnaryArithmetic,
        Bool.and_eq_true] at unary
      cases op with
      | add | subtract | divide =>
          simpa only [AuthoredNumericExpr.lowerForEvaluation,
            LoweredNumericExpr.isUnaryArithmetic, Bool.and_eq_true]
            using And.intro (leftIh unary.1) (rightIh unary.2)
      | multiply =>
          exact lowerMultiply_unary _ _
            (leftIh unary.1) (rightIh unary.2)
  | power base exponent baseIh exponentIh =>
      simp only [AuthoredNumericExpr.isUnaryArithmetic,
        Bool.and_eq_true] at unary
      simpa only [AuthoredNumericExpr.lowerForEvaluation,
        LoweredNumericExpr.isUnaryArithmetic, Bool.and_eq_true]
        using And.intro (baseIh unary.1) (exponentIh unary.2)
  | abs body ih =>
      simpa only [AuthoredNumericExpr.isUnaryArithmetic,
        AuthoredNumericExpr.lowerForEvaluation,
        LoweredNumericExpr.isUnaryArithmetic] using ih unary
  | round mode places body ih =>
      simpa only [AuthoredNumericExpr.isUnaryArithmetic,
        AuthoredNumericExpr.lowerForEvaluation,
        LoweredNumericExpr.isUnaryArithmetic] using ih unary
  | extremum =>
      simp [AuthoredNumericExpr.isUnaryArithmetic] at unary

private theorem loweredUnaryValidation_isSome
    (expression : LoweredNumericExpr Atom)
    (read : Atom → Except FormalCause NumericArithmeticOutcome)
    (unary : expression.isUnaryArithmetic = true) :
    (expression.evalUnaryArithmetic? read).isSome = true := by
  induction expression with
  | atom | literal => rfl
  | binary op left right leftIh rightIh =>
      simp only [LoweredNumericExpr.isUnaryArithmetic, Bool.and_eq_true] at unary
      have leftSome := leftIh unary.1
      have rightSome := rightIh unary.2
      cases leftResult : left.evalUnaryArithmetic? read with
      | none =>
          simp [leftResult] at leftSome
      | some leftOutcome =>
          cases rightResult : right.evalUnaryArithmetic? read with
          | none =>
              simp [rightResult] at rightSome
          | some rightOutcome =>
              simp [LoweredNumericExpr.evalUnaryArithmetic?,
                leftResult, rightResult]
  | power base exponent baseIh exponentIh =>
      simp only [LoweredNumericExpr.isUnaryArithmetic, Bool.and_eq_true] at unary
      have baseSome := baseIh unary.1
      have exponentSome := exponentIh unary.2
      cases baseResult : base.evalUnaryArithmetic? read with
      | none => simp [baseResult] at baseSome
      | some baseOutcome =>
          cases exponentResult : exponent.evalUnaryArithmetic? read with
          | none => simp [exponentResult] at exponentSome
          | some exponentOutcome =>
              simp [LoweredNumericExpr.evalUnaryArithmetic?,
                baseResult, exponentResult]
  | abs body ih =>
      have bodySome := ih (by
        simpa [LoweredNumericExpr.isUnaryArithmetic] using unary)
      cases evaluated : body.evalUnaryArithmetic? read with
      | none => simp [evaluated] at bodySome
      | some outcome =>
          simp [LoweredNumericExpr.evalUnaryArithmetic?, evaluated]
  | round mode places body ih =>
      have bodySome := ih (by
        simpa [LoweredNumericExpr.isUnaryArithmetic] using unary)
      cases evaluated : body.evalUnaryArithmetic? read with
      | none => simp [evaluated] at bodySome
      | some outcome =>
          simp [LoweredNumericExpr.evalUnaryArithmetic?, evaluated]
  | extremum =>
      simp [LoweredNumericExpr.isUnaryArithmetic] at unary

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
  | atom | literal | group | binary | power | abs | round =>
      simp [AuthoredNumericExpr.isDirectValueFunction] at direct
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
  | inl unary =>
      exact Or.inl (authoredNumericLower_unary expression unary)
  | inr direct =>
      exact Or.inr
        (authoredNumericLower_directValueFunction expression direct)

private theorem admittedResolvedUnary_isUnary
    (expression : AuthoredNumericExpr NumericValidationAtom)
    (admitted : expression.isAdmittedResolvedUnaryArithmetic = true) :
    expression.isUnaryArithmetic = true := by
  induction expression with
  | atom | literal => rfl
  | group body ih => exact ih admitted
  | binary op left right leftIh rightIh =>
      simp only [AuthoredNumericExpr.isAdmittedResolvedUnaryArithmetic,
        AuthoredNumericExpr.isUnaryArithmetic, Bool.and_eq_true] at admitted ⊢
      exact ⟨leftIh admitted.1, rightIh admitted.2⟩
  | power base exponent baseIh exponentIh =>
      simp only [AuthoredNumericExpr.isAdmittedResolvedUnaryArithmetic,
        AuthoredNumericExpr.isUnaryArithmetic, Bool.and_eq_true] at admitted ⊢
      exact ⟨baseIh admitted.1, exponentIh admitted.2⟩
  | abs body ih =>
      simp only [AuthoredNumericExpr.isAdmittedResolvedUnaryArithmetic,
        Bool.and_eq_true] at admitted
      simpa only [AuthoredNumericExpr.isUnaryArithmetic] using
        authoredPlain_isUnary body admitted.1
  | round mode places body ih =>
      simp only [AuthoredNumericExpr.isAdmittedResolvedUnaryArithmetic,
        Bool.and_eq_true] at admitted
      simpa only [AuthoredNumericExpr.isUnaryArithmetic] using
        authoredPlain_isUnary body admitted.1
  | extremum =>
      simp [AuthoredNumericExpr.isAdmittedResolvedUnaryArithmetic] at admitted

private theorem authoredNumericLower_admittedNumericValidation
    (expression : AuthoredNumericExpr NumericValidationAtom)
    (admitted : expression.isAdmittedResolvedNumericOperation = true) :
    expression.lowerForEvaluation.isAdmittedValidation = true := by
  unfold AuthoredNumericExpr.isAdmittedResolvedNumericOperation at admitted
  split at admitted
  · have authoredUnary := admittedResolvedUnary_isUnary expression admitted
    have loweredUnary := authoredNumericLower_unary expression authoredUnary
    simp [LoweredNumericExpr.isAdmittedValidation, loweredUnary]
  · split at admitted
    · have authoredUnary := authoredPlain_isUnary expression admitted
      have loweredUnary := authoredNumericLower_unary expression authoredUnary
      simp [LoweredNumericExpr.isAdmittedValidation, loweredUnary]
    · exact authoredNumericLower_admittedValidation expression admitted

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
  | inl unary =>
      have evaluated := loweredUnaryValidation_isSome expression read unary
      cases expression with
      | atom | literal | binary | power | abs | round =>
          simpa [LoweredNumericExpr.evalAdmittedValidation?] using evaluated
      | extremum =>
          simp [LoweredNumericExpr.isUnaryArithmetic] at unary
  | inr direct =>
      cases expression with
      | atom | literal | binary | power | abs | round =>
          simp [LoweredNumericExpr.isDirectValueFunction] at direct
      | extremum op left right =>
          have evaluated := loweredDirectExtremum_isSome op
            (.extremum op left right) read direct
          simpa [LoweredNumericExpr.evalAdmittedValidation?] using evaluated

private theorem numericComparison_wellFormed_sidesAdmitted
    (comparison : NumericComparison)
    (wellFormed : comparison.WellFormedIn model rowGroup scope) :
    comparison.left.isAdmittedResolvedNumericOperation = true ∧
      comparison.right.isAdmittedResolvedNumericOperation = true := by
  simp only [NumericComparison.WellFormedIn,
    NumericComparison.wellFormedInBool, Bool.and_eq_true] at wellFormed
  exact ⟨wellFormed.1.1.1.1.1.1.2, wellFormed.1.1.1.1.1.2⟩

/-- The checked certificate makes both evaluator unsupported-shape fallbacks unreachable. -/
theorem checkedNumericComparison_evaluations_areSome
    (checked : CheckedNumericComparison model)
    (context : FlatContext) :
    (checked.core.left.lowerForEvaluation.evalAdmittedValidation?
        context.resolveNumericValidationAtom).isSome = true ∧
      (checked.core.right.lowerForEvaluation.evalAdmittedValidation?
        context.resolveNumericValidationAtom).isSome = true := by
  have admitted :=
    numericComparison_wellFormed_sidesAdmitted checked.core checked.wellFormed
  exact ⟨
    loweredAdmittedValidation_isSome _ _
      (authoredNumericLower_admittedNumericValidation _ admitted.1),
    loweredAdmittedValidation_isSome _ _
      (authoredNumericLower_admittedNumericValidation _ admitted.2)⟩

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
    ({ op := .ordinary op, left := .atom (.field field), right := .literal right } :
      NumericComparison).evalSelected context =
        (FlatComparison.number (.ordinary op) field right.value).eval context := by
  cases observed : context.resolveNumberComparisonOperand field <;>
    simp only [NumericComparison.evalSelected,
      AuthoredNumericExpr.lowerForEvaluation,
      LoweredNumericExpr.evalAdmittedValidation?,
      LoweredNumericExpr.evalUnaryArithmetic?,
      FlatContext.resolveNumericValidationAtom,
      FlatContext.resolveNumericArithmetic,
      NumericOperand.toValidationArithmetic, FlatComparison.eval,
      NumericValidationOp.evalArithmetic, NumericValidationOp.eval,
      NumericValidationOp.evalFixedRight,
      NumericComparisonOp.eval, observed]

/-- A rounded left atom against a literal delegates to the existing rounded-operand semantics for every mode and for both ordinary and tolerance consumers. -/
theorem numericValidation_round_atom_literal_delegates
    (op : NumericValidationOp) (mode : DecimalRoundingMode)
    (places : RoundingPlaces) (atom : NumericValidationAtom)
    (right : DecodedNumericLiteral) (context : FlatContext) :
    ({ op, left := .round mode places (.atom atom),
        right := .literal right } :
      NumericComparison).evalSelected context =
        op.evalArithmetic
          (match context.resolveNumericValidationAtom atom with
          | .ok outcome => .ok (outcome.round mode places)
          | .error cause => .error cause)
          (.ok (.value right.value .fixed)) := by
  cases op <;>
    cases observed : context.resolveNumericValidationAtom atom <;>
    simp [NumericComparison.evalSelected,
      AuthoredNumericExpr.lowerForEvaluation,
      LoweredNumericExpr.evalAdmittedValidation?,
      LoweredNumericExpr.evalUnaryArithmetic?, observed]

/-- An absolute-valued left atom against a literal delegates to the shared operand transformation for every ordinary and tolerance consumer. -/
theorem numericValidation_abs_atom_literal_delegates
    (op : NumericValidationOp) (atom : NumericValidationAtom)
    (right : DecodedNumericLiteral) (context : FlatContext) :
    ({ op, left := .abs (.atom atom), right := .literal right } :
      NumericComparison).evalSelected context =
        op.evalArithmetic
          (match context.resolveNumericValidationAtom atom with
          | .ok outcome => .ok outcome.absolute
          | .error cause => .error cause)
          (.ok (.value right.value .fixed)) := by
  cases op <;>
    cases observed : context.resolveNumericValidationAtom atom <;>
    simp [NumericComparison.evalSelected,
      AuthoredNumericExpr.lowerForEvaluation,
      LoweredNumericExpr.evalAdmittedValidation?,
      LoweredNumericExpr.evalUnaryArithmetic?, observed]

/-- Rounding maps the complete result of its evaluated body; it neither rereads atoms nor changes the body's formal-cause priority. -/
theorem numericValidation_round_body_delegates
    (mode : DecimalRoundingMode) (places : RoundingPlaces)
    (body : LoweredNumericExpr Atom)
    (read : Atom → Except FormalCause NumericArithmeticOutcome)
    (bodyOutcome : Except FormalCause NumericArithmeticOutcome)
    (evaluated : body.evalUnaryArithmetic? read = some bodyOutcome) :
    (LoweredNumericExpr.round mode places body).evalAdmittedValidation? read =
      some (match bodyOutcome with
        | .ok outcome => .ok (outcome.round mode places)
        | .error cause => .error cause) := by
  cases bodyOutcome <;>
    simp [LoweredNumericExpr.evalAdmittedValidation?,
      LoweredNumericExpr.evalUnaryArithmetic?, evaluated]

/-- Absolute value transforms the complete arithmetic outcome only after its evaluated body has finished. -/
theorem numericValidation_abs_body_delegates
    (body : LoweredNumericExpr Atom)
    (read : Atom → Except FormalCause NumericArithmeticOutcome)
    (bodyOutcome : Except FormalCause NumericArithmeticOutcome)
    (evaluated : body.evalUnaryArithmetic? read = some bodyOutcome) :
    (LoweredNumericExpr.abs body).evalAdmittedValidation? read =
      some (match bodyOutcome with
        | .ok outcome => .ok outcome.absolute
        | .error cause => .error cause) := by
  cases bodyOutcome <;>
    simp [LoweredNumericExpr.evalAdmittedValidation?,
      LoweredNumericExpr.evalUnaryArithmetic?, evaluated]

/-- A direct tolerance core atom/literal pair delegates to the existing pure tolerance seam. -/
theorem numericTolerance_atom_literal_delegates
    (range : NumericToleranceRange) (field : FlatNumberField)
    (right : DecodedNumericLiteral) (context : FlatContext) :
    ({ op := .tolerance range, left := .atom (.field field),
        right := .literal right } :
      NumericComparison).evalSelected context =
        range.eval (context.resolveNumberComparisonOperand field)
          (.value right.value .fixed) := by
  cases observed : context.resolveNumberComparisonOperand field <;>
    simp only [NumericComparison.evalSelected,
      AuthoredNumericExpr.lowerForEvaluation,
      LoweredNumericExpr.evalAdmittedValidation?,
      LoweredNumericExpr.evalUnaryArithmetic?,
      FlatContext.resolveNumericValidationAtom,
      FlatContext.resolveNumericArithmetic,
      NumericOperand.toValidationArithmetic,
      NumericValidationOp.evalArithmetic, NumericValidationOp.eval,
      NumericToleranceRange.eval, observed]

/-- Numeric Base Year is a fixed scale-0 operand inside the same checked tolerance evaluator used for Number fields. -/
theorem numericTolerance_field_baseYear_delegates
    (range : NumericToleranceRange) (field : FlatNumberField)
    (year : Int) (context : FlatContext) :
    ({ op := .tolerance range, left := .atom (.field field),
        right := .atom (.baseYear year) } : NumericComparison).evalSelected context =
      range.eval (context.resolveNumberComparisonOperand field)
        (.value year .fixed) := by
  cases observed : context.resolveNumberComparisonOperand field <;>
    simp only [NumericComparison.evalSelected,
      AuthoredNumericExpr.lowerForEvaluation,
      LoweredNumericExpr.evalAdmittedValidation?,
      LoweredNumericExpr.evalUnaryArithmetic?,
      FlatContext.resolveNumericValidationAtom,
      FlatContext.resolveNumericArithmetic,
      NumericOperand.toValidationArithmetic,
      NumericValidationOp.evalArithmetic, NumericValidationOp.eval,
      NumericToleranceRange.eval, observed]

/-- A direct Base-Year date-component atom is the selected fixed scale-0 amount inside the same checked tolerance evaluator. -/
theorem numericTolerance_field_baseYearDatePart_delegates
    (range : NumericToleranceRange) (field : FlatNumberField)
    (year : Int) (source : BaseYearDateSource) (part : DateNumericPart)
    (context : FlatContext) :
    ({ op := .tolerance range, left := .atom (.field field),
        right := .atom (.baseYearDatePart year source part) } :
      NumericComparison).evalSelected context =
      range.eval (context.resolveNumberComparisonOperand field)
        (.value (baseYearDateSourceNumericPart year source part) .fixed) := by
  cases observed : context.resolveNumberComparisonOperand field <;>
    simp only [NumericComparison.evalSelected,
      AuthoredNumericExpr.lowerForEvaluation,
      LoweredNumericExpr.evalAdmittedValidation?,
      LoweredNumericExpr.evalUnaryArithmetic?,
      FlatContext.resolveNumericValidationAtom,
      FlatContext.resolveNumericArithmetic,
      NumericOperand.toValidationArithmetic,
      NumericValidationOp.evalArithmetic, NumericValidationOp.eval,
      NumericToleranceRange.eval, observed]

/-- Every direct Date/Time/DateTime component atom delegates to its unified flat payload projection before the ordinary or tolerance evaluator. -/
theorem numericValidation_temporalFieldPart_literal_delegates
    (op : NumericValidationOp) (field : FlatTemporalField)
    (part : TemporalNumericPart) (right : DecodedNumericLiteral)
    (context : FlatContext) :
    ({ op, left := .atom (.temporalFieldPart field part),
        right := .literal right } :
      NumericComparison).evalSelected context =
        op.eval (context.resolveTemporalNumericOperand field part)
          (.value right.value .fixed) := by
  cases op <;>
    cases observed : context.resolveTemporalNumericOperand field part <;>
    simp [NumericComparison.evalSelected,
      AuthoredNumericExpr.lowerForEvaluation,
      LoweredNumericExpr.evalAdmittedValidation?,
      LoweredNumericExpr.evalUnaryArithmetic?,
      FlatContext.resolveNumericValidationAtom,
      NumericOperand.toValidationArithmetic,
      NumericValidationOp.evalArithmetic, NumericValidationOp.eval,
      NumericComparisonOp.eval, NumericToleranceRange.eval, observed]

/-- A supported checked date-difference atom delegates its phase-observed numeric operand to the ordinary or tolerance evaluator without a second arithmetic path. -/
theorem numericValidation_dateDifference_literal_delegates
    (op : NumericValidationOp) (unit : DateDifferenceUnit)
    (left right : ResolvedDateDifferenceOperand)
    (literal : DecodedNumericLiteral) (context : FlatContext)
    (operand : NumericOperand)
    (evaluated : DateDifferenceOperand.evaluate unit
      (left.validationOperand context) (right.validationOperand context) =
        .ok operand) :
    ({ op, left := .atom (.dateDifference unit left right),
        right := .literal literal } : NumericComparison).evalSelected context =
      op.eval operand (.value literal.value .fixed) := by
  cases op <;>
    cases operand <;>
    simp [NumericComparison.evalSelected,
      AuthoredNumericExpr.lowerForEvaluation,
      LoweredNumericExpr.evalAdmittedValidation?,
      LoweredNumericExpr.evalUnaryArithmetic?,
      FlatContext.resolveNumericValidationAtom,
      NumericOperand.toValidationArithmetic,
      NumericValidationOp.evalArithmetic, NumericValidationOp.eval,
      NumericComparisonOp.eval, NumericToleranceRange.eval, evaluated]

/-- Full validation gates a checked numeric condition before any empty-Number substitution can fire. -/
theorem checkedNumericComparison_emptyRow_notFired
    (checked : CheckedNumericComparison model)
    (context : FlatContext) :
    checked.evalFull context false = .notFired := by
  rfl

end A12Kernel
