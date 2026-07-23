import A12Kernel.Elaboration.NumericValidation

/-! # Checked numeric-validation laws -/

namespace A12Kernel

attribute [local simp]
  LoweredNumericExpr.isNumericOperation
  LoweredNumericExpr.isExtremumCall
  LoweredNumericExpr.isAdmittedValidation
  LoweredNumericExpr.evalNumericOperationTree
  LoweredNumericExpr.evalNumericOperation?
  LoweredNumericExpr.evalAdmittedValidation?
  combineNumericValidationOutcomes
  evalPlainBinary
  NumericComparison.evalWith
  NumericComparison.evalSelectedWithGroups
  NumericValidationOp.evalArithmeticWith

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

/-- A relevant present first source terminates direct `FirstFilledValue` before any suffix relevance decision. -/
theorem orderedNumericValidationAtom_firstFilled_presentHead_hidesSuffix
    (source : ResolvedNumericAggregateFields)
    (context : ValidationEvaluationContext) (isRelevant : FlatRelevance) (amount : Rat)
    (relevant : isRelevant source.first.id = true)
    (present : source.first.valueListCell context.fields = .present amount) :
    OrderedNumericValidationAtom.resolveFirstFilledFields
        context isRelevant source.fields {} =
      .ok (.value amount .fixed) := by
  simp [OrderedNumericValidationAtom.resolveFirstFilledFields,
    ResolvedNumericAggregateFields.fields, relevant, present,
    FirstFilledScanState.step, FirstFilledScanResult.asNumber,
    FirstFilledNumberResult.asValidationOperand,
    NumericOperand.toValidationArithmetic]

/-- A resolved validation aggregate atom consumes the shared aggregate fold and only then enters the existing arithmetic-outcome domain. -/
theorem numericValidationAggregate_evaluatesThroughSharedFold
    (context : FlatContext) (op : NumericAggregateOp)
    (source : ResolvedNumericAggregateFields) :
    context.resolveNumericValidationAtom (.aggregate op source) =
      (source.evaluate op context.observeValidationAt).toValidationArithmetic := by
  rfl

/-- A complete clean fixed group source enters ordinary arithmetic as its exact count, with grow-only movement until every listed group is filled. -/
theorem numericValidation_filledGroupCount_value
    (context : ValidationEvaluationContext)
    (groups : List ResolvedGroupReference)
    (states : List GroupPresenceState) (count : Nat)
    (resolved : context.groups.resolveAll groups = some states)
    (counted : numberOfFilledGroups states = .value count) :
    context.resolveNumericValidationAtom (.filledGroupCount groups) =
      .ok (.value count
        (if count < groups.length then .growOnly else .fixed)) := by
  simp [ValidationEvaluationContext.resolveNumericValidationAtom,
    resolved, counted]

/-- An erroneous or not-fully-relevant group makes the whole fixed count cause-free unavailable; it is never rewritten to a fabricated formal cell cause. -/
theorem numericValidation_filledGroupCount_unknown
    (context : ValidationEvaluationContext)
    (groups : List ResolvedGroupReference)
    (states : List GroupPresenceState)
    (resolved : context.groups.resolveAll groups = some states)
    (counted : numberOfFilledGroups states = .unknown) :
    context.resolveNumericValidationAtom (.filledGroupCount groups) =
      .error .groupState := by
  simp [ValidationEvaluationContext.resolveNumericValidationAtom,
    resolved, counted]

/-- Missing checked-document group state is the same explicit cause-free unavailability as an unresolved product state. -/
theorem numericValidation_filledGroupCount_missing
    (context : ValidationEvaluationContext)
    (groups : List ResolvedGroupReference)
    (missing : context.groups.resolveAll groups = none) :
    context.resolveNumericValidationAtom (.filledGroupCount groups) =
      .error .groupState := by
  simp [ValidationEvaluationContext.resolveNumericValidationAtom, missing]

/-- A checked `Length` atom enters the shared arithmetic domain only through the common phase-selected String-length projection. -/
theorem numericValidation_stringLength_delegates
    (context : FlatContext) (field : FlatStringField) :
    context.resolveNumericValidationAtom (.stringLength field) =
      (context.resolveStringLengthOperand field).toValidationArithmetic := by
  rfl

/-- A missing checked String source gives `RangeAsNumber` the real zero together with its one possible movement direction. -/
theorem numericValidation_stringRange_empty_growOnly
    (context : FlatContext) (field : FlatStringField) (start finish : Nat)
    (observed : context.observeValidationAt field.id = .empty) :
  context.resolveNumericValidationAtom (.stringRange field start finish) =
      .ok (.value 0 .growOnly) := by
  simp [FlatContext.resolveNumericValidationAtom,
    ValidationEvaluationContext.resolveNumericValidationAtom, observed]

/-- Once the String source is present, digits-only conversion or fallback zero is fixed; substring content does not itself carry omission potential. -/
theorem numericValidation_stringRange_value_fixed
    (context : FlatContext) (field : FlatStringField) (start finish : Nat)
    (value : String)
    (observed : context.observeValidationAt field.id = .value (.str value)) :
  context.resolveNumericValidationAtom (.stringRange field start finish) =
      .ok (.value (utf16RangeAsNatural value start finish) .fixed) := by
  simp [FlatContext.resolveNumericValidationAtom,
    ValidationEvaluationContext.resolveNumericValidationAtom, observed]

/-- A reached formal cause survives the range conversion rather than becoming fallback zero. -/
theorem numericValidation_stringRange_unknown_preservesCause
    (context : FlatContext) (field : FlatStringField) (start finish : Nat)
    (cause : FormalCause)
    (observed : context.observeValidationAt field.id = .unknown cause) :
    context.resolveNumericValidationAtom (.stringRange field start finish) =
      .error (.formal cause) := by
  simp [FlatContext.resolveNumericValidationAtom,
    ValidationEvaluationContext.resolveNumericValidationAtom, observed]

/-- Missing admitted String or Enumeration/category conversion is numeric zero with both possible movement directions. -/
theorem numericValidation_fieldValueAsNumber_empty_both
    (context : FlatContext) (source : ResolvedFieldValueAsNumberSource)
    (observed : context.observeValidationAt source.fieldId = .empty) :
  context.resolveNumericValidationAtom (.fieldValueAsNumber source) =
      .ok (.value 0 .both) := by
  simp [FlatContext.resolveNumericValidationAtom,
    ValidationEvaluationContext.resolveNumericValidationAtom, observed]

/-- A present admitted String or Enumeration value is projected and parsed once; the resulting value is fixed. -/
theorem numericValidation_fieldValueAsNumber_value_fixed
    (context : FlatContext) (source : ResolvedFieldValueAsNumberSource)
    (value : Value) (amount : Rat)
    (observed : context.observeValidationAt source.fieldId =
      .value value)
    (converted : source.valueFor? value = some amount) :
  context.resolveNumericValidationAtom (.fieldValueAsNumber source) =
      .ok (.value amount .fixed) := by
  simp [FlatContext.resolveNumericValidationAtom,
    ValidationEvaluationContext.resolveNumericValidationAtom,
    observed, converted]

/-- A reached formal cause survives String or Enumeration/category conversion unchanged. -/
theorem numericValidation_fieldValueAsNumber_unknown_preservesCause
    (context : FlatContext) (source : ResolvedFieldValueAsNumberSource)
    (cause : FormalCause)
    (observed : context.observeValidationAt source.fieldId = .unknown cause) :
    context.resolveNumericValidationAtom (.fieldValueAsNumber source) =
      .error (.formal cause) := by
  simp [FlatContext.resolveNumericValidationAtom,
    ValidationEvaluationContext.resolveNumericValidationAtom, observed]

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
      base.evalNumericOperation? read =
        some (.ok (.value baseValue baseFill)))
    (exponentEvaluated :
      exponent.evalNumericOperation? read =
        some (.ok (.value exponentValue exponentFill))) :
    (LoweredNumericExpr.power base exponent).evalNumericOperation? read =
      some (.ok (NumericArithmeticOutcome.power
        (.value baseValue baseFill) (.value exponentValue exponentFill))) := by
  by_cases baseAdmitted : base.isNumericOperation = true
  · simp [LoweredNumericExpr.evalNumericOperation?, baseAdmitted] at baseEvaluated
    by_cases exponentAdmitted : exponent.isNumericOperation = true
    · simp [LoweredNumericExpr.evalNumericOperation?, exponentAdmitted] at exponentEvaluated
      simp [LoweredNumericExpr.evalNumericOperation?,
        LoweredNumericExpr.isNumericOperation, baseAdmitted, exponentAdmitted,
        LoweredNumericExpr.evalNumericOperationTree,
        baseEvaluated, exponentEvaluated]
    · simp [LoweredNumericExpr.evalNumericOperation?, exponentAdmitted] at exponentEvaluated
  · simp [LoweredNumericExpr.evalNumericOperation?, baseAdmitted] at baseEvaluated

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
    | atom | literal | power | abs | extremum | extremumCall | round =>
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
  | abs | extremum | extremumCall | round =>
      simp [AuthoredNumericExpr.isPlainArithmetic] at plain

private theorem lowerMultiply_numericOperation
    (left right : LoweredNumericExpr Atom)
    (leftAdmitted : left.isNumericOperation = true)
    (rightAdmitted : right.isNumericOperation = true) :
    (LoweredNumericExpr.lowerMultiply left right).isNumericOperation = true := by
  apply lowerMultiply_preserves LoweredNumericExpr.isNumericOperation
    (fun _ _ _ leftShape rightShape => by
      simpa [LoweredNumericExpr.isNumericOperation] using
        And.intro leftShape rightShape)
    (fun _ _ shape => by
      simpa [LoweredNumericExpr.isNumericOperation] using shape)
    left right leftAdmitted rightAdmitted

private theorem authoredNumericLower_extremumCall
    (expression : AuthoredNumericExpr Atom)
    (direct : expression.isExtremumCall = true) :
    expression.lowerForEvaluation.isExtremumCall = true := by
  induction expression with
  | group body ih => exact ih direct
  | extremumCall op body ih =>
      simpa [AuthoredNumericExpr.isExtremumCall,
        AuthoredNumericExpr.lowerForEvaluation,
        LoweredNumericExpr.isExtremumCall] using direct
  | atom | literal | binary | power | abs | extremum | round =>
      simp [AuthoredNumericExpr.isExtremumCall] at direct

private theorem authoredNumericLower_numericOperation
    (expression : AuthoredNumericExpr Atom)
    (admitted : expression.isNumericOperation = true) :
    expression.lowerForEvaluation.isNumericOperation = true := by
  induction expression with
  | atom | literal => rfl
  | group body ih => exact ih admitted
  | binary op left right leftIh rightIh =>
      simp only [AuthoredNumericExpr.isNumericOperation,
        Bool.and_eq_true] at admitted
      cases op with
      | add | subtract | divide =>
          simpa only [AuthoredNumericExpr.lowerForEvaluation,
            LoweredNumericExpr.isNumericOperation, Bool.and_eq_true]
            using And.intro (leftIh admitted.1) (rightIh admitted.2)
      | multiply =>
          exact lowerMultiply_numericOperation _ _
            (leftIh admitted.1) (rightIh admitted.2)
  | power base exponent baseIh exponentIh =>
      simp only [AuthoredNumericExpr.isNumericOperation,
        Bool.and_eq_true] at admitted
      simpa only [AuthoredNumericExpr.lowerForEvaluation,
        LoweredNumericExpr.isNumericOperation, Bool.and_eq_true]
        using And.intro (baseIh admitted.1) (exponentIh admitted.2)
  | abs body ih =>
      simp only [AuthoredNumericExpr.isNumericOperation,
        AuthoredNumericExpr.lowerForEvaluation,
        LoweredNumericExpr.isNumericOperation] at admitted ⊢
      exact ih admitted
  | round mode places body ih =>
      simp only [AuthoredNumericExpr.isNumericOperation,
        AuthoredNumericExpr.lowerForEvaluation,
        LoweredNumericExpr.isNumericOperation] at admitted ⊢
      exact ih admitted
  | extremum =>
      simp [AuthoredNumericExpr.isNumericOperation] at admitted
  | extremumCall op body ih =>
      apply authoredNumericLower_extremumCall
        (.extremumCall op body)
      simpa [AuthoredNumericExpr.isNumericOperation,
        AuthoredNumericExpr.isExtremumCall,
        AuthoredNumericExpr.extremumCallConstantUse?] using admitted

private theorem authoredNumericLower_admittedValidation
    (expression : AuthoredNumericExpr Atom)
    (admitted : expression.isAdmittedNumericOperation = true) :
    expression.lowerForEvaluation.isAdmittedValidation = true := by
  change expression.lowerForEvaluation.isNumericOperation = true
  exact authoredNumericLower_numericOperation expression admitted

private theorem authoredNumericLower_admittedNumericValidation
    (expression : AuthoredNumericExpr NumericValidationAtom)
    (admitted : expression.isAdmittedResolvedNumericOperation = true) :
    expression.lowerForEvaluation.isAdmittedValidation = true := by
  simp only [AuthoredNumericExpr.isAdmittedResolvedNumericOperation,
    Bool.and_eq_true] at admitted
  exact authoredNumericLower_admittedValidation expression admitted.1

private theorem loweredAdmittedValidation_isSome
    (expression : LoweredNumericExpr Atom)
    (read : Atom → Except Error NumericArithmeticOutcome)
    (admitted : expression.isAdmittedValidation = true) :
    (expression.evalAdmittedValidation? read).isSome = true := by
  unfold LoweredNumericExpr.isAdmittedValidation at admitted
  unfold LoweredNumericExpr.evalAdmittedValidation?
  unfold LoweredNumericExpr.evalNumericOperation?
  rw [admitted]
  rfl

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
    (AuthoredNumericExpr.extremumCall op
      (.extremum op (.atom atom)
        (.literal constant))).isExtremumCall = true ∧
      (AuthoredNumericExpr.extremumCall op
        (.extremum op (.literal constant)
          (.atom atom))).isExtremumCall = true := by
  cases op <;> constructor <;> rfl

/-- Lowering preserves the source-derived per-call constant certificate even when arithmetic lowering changes the operand topology. -/
theorem numericValidation_extremumCall_lowering_preservesConstantUse
    (op : NumericExtremumOp) (body : AuthoredNumericExpr Atom) :
    LoweredNumericExpr.extremumCallConstantUse? op
        (AuthoredNumericExpr.extremumCall op body).lowerForEvaluation =
      (AuthoredNumericExpr.extremumCall op body).extremumCallConstantUse? op := by
  cases op <;> rfl

/-- Nested calls own independent immediate-constant budgets; flattening the same two constants into one call remains rejected. -/
theorem numericValidation_extremum_nestedConstantBudgets
    (op : NumericExtremumOp) (atom : Atom)
    (first second : DecodedNumericLiteral) :
    (AuthoredNumericExpr.extremumList op
      (AuthoredNumericExpr.extremumList op (.atom atom) [.literal first])
      [.literal second]).isExtremumCall = true ∧
    (AuthoredNumericExpr.extremumList op (.atom atom)
      [.literal first, .literal second]).isExtremumCall = false := by
  cases op <;> constructor <;> rfl

/-- A direct constant reaches the existing exact extremum selector as a fixed operand. -/
theorem numericValidation_extremum_atom_constant_delegates
    (op : NumericExtremumOp) (atom : Atom) (constant : Rat)
    (read : Atom → Except FormalCause NumericArithmeticOutcome) :
    (LoweredNumericExpr.extremumCall op (some true)
      (.extremum op (.atom atom)
        (.literal constant))).evalNumericOperation? read =
        some (op.selectValidationOutcome (read atom)
          (.ok (.value constant .fixed))) := by
  cases op <;> rfl

/-- A second direct constant is rejected rather than silently widening the authored list contract. -/
theorem numericValidation_extremum_twoConstants_rejected
    (op : NumericExtremumOp) (atom : Atom)
    (first second : DecodedNumericLiteral) :
    (AuthoredNumericExpr.extremumCall op
      (.extremum op
        (.extremum op (.atom atom) (.literal first))
        (.literal second))).isExtremumCall = false := by
  cases op <;> rfl

/-- A direct atom and literal evaluate exactly like the shared low-level Number-field evaluator. -/
theorem numericComparison_atom_literal_agrees_flat
    (op : NumericComparisonOp) (field : FlatNumberField)
    (right : DecodedNumericLiteral) (context : FlatContext) :
    ({ op := .ordinary op, left := .atom (.field field), right := .literal right } :
      NumericComparison).evalSelected context =
        (FlatComparison.number (.ordinary op) field right.value).eval context := by
  cases observed : context.resolveNumberComparisonOperand field <;>
    simp [NumericComparisonOf.evalSelected, NumericComparisonOf.evalWith,
      AuthoredNumericExpr.lowerForEvaluation,
      LoweredNumericExpr.evalAdmittedValidation?,
      FlatContext.resolveNumericValidationAtom,
      ValidationEvaluationContext.resolveNumericValidationAtom,
      FlatContext.resolveNumericArithmetic,
      NumericOperand.toValidationArithmetic, FlatComparison.eval,
      NumericValidationOp.eval,
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
        op.evalArithmeticWith
          (match context.resolveNumericValidationAtom atom with
          | .ok outcome => .ok (outcome.round mode places)
          | .error cause => .error cause)
          (.ok (.value right.value .fixed)) := by
  cases op <;>
    cases observed : context.resolveNumericValidationAtom atom <;>
    simp [NumericComparisonOf.evalSelected, NumericComparisonOf.evalWith,
      AuthoredNumericExpr.lowerForEvaluation,
      LoweredNumericExpr.evalAdmittedValidation?,
      observed]

/-- An absolute-valued left atom against a literal delegates to the shared operand transformation for every ordinary and tolerance consumer. -/
theorem numericValidation_abs_atom_literal_delegates
    (op : NumericValidationOp) (atom : NumericValidationAtom)
    (right : DecodedNumericLiteral) (context : FlatContext) :
    ({ op, left := .abs (.atom atom), right := .literal right } :
      NumericComparison).evalSelected context =
        op.evalArithmeticWith
          (match context.resolveNumericValidationAtom atom with
          | .ok outcome => .ok outcome.absolute
          | .error cause => .error cause)
          (.ok (.value right.value .fixed)) := by
  cases op <;>
    cases observed : context.resolveNumericValidationAtom atom <;>
    simp [NumericComparisonOf.evalSelected, NumericComparisonOf.evalWith,
      AuthoredNumericExpr.lowerForEvaluation,
      LoweredNumericExpr.evalAdmittedValidation?,
      observed]

/-- Rounding maps the complete result of its evaluated body; it neither rereads atoms nor changes the body's formal-cause priority. -/
theorem numericValidation_round_body_delegates
    (mode : DecimalRoundingMode) (places : RoundingPlaces)
    (body : LoweredNumericExpr Atom)
    (read : Atom → Except FormalCause NumericArithmeticOutcome)
    (bodyOutcome : Except FormalCause NumericArithmeticOutcome)
    (evaluated : body.evalNumericOperation? read = some bodyOutcome) :
    (LoweredNumericExpr.round mode places body).evalAdmittedValidation? read =
      some (match bodyOutcome with
        | .ok outcome => .ok (outcome.round mode places)
        | .error cause => .error cause) := by
  by_cases bodyAdmitted : body.isNumericOperation = true
  · have treeEvaluated :
        body.evalNumericOperationTree read = bodyOutcome := by
      simpa [LoweredNumericExpr.evalNumericOperation?, bodyAdmitted] using evaluated
    cases bodyOutcome <;>
      simp [LoweredNumericExpr.evalAdmittedValidation?,
        LoweredNumericExpr.isNumericOperation,
        LoweredNumericExpr.evalNumericOperationTree,
        bodyAdmitted, treeEvaluated]
  · simp [LoweredNumericExpr.evalNumericOperation?, bodyAdmitted] at evaluated

/-- Absolute value transforms the complete arithmetic outcome only after its evaluated body has finished. -/
theorem numericValidation_abs_body_delegates
    (body : LoweredNumericExpr Atom)
    (read : Atom → Except FormalCause NumericArithmeticOutcome)
    (bodyOutcome : Except FormalCause NumericArithmeticOutcome)
    (evaluated : body.evalNumericOperation? read = some bodyOutcome) :
    (LoweredNumericExpr.abs body).evalAdmittedValidation? read =
      some (match bodyOutcome with
        | .ok outcome => .ok outcome.absolute
        | .error cause => .error cause) := by
  by_cases bodyAdmitted : body.isNumericOperation = true
  · have treeEvaluated :
        body.evalNumericOperationTree read = bodyOutcome := by
      simpa [LoweredNumericExpr.evalNumericOperation?, bodyAdmitted] using evaluated
    cases bodyOutcome <;>
      simp [LoweredNumericExpr.evalAdmittedValidation?,
        LoweredNumericExpr.isNumericOperation,
        LoweredNumericExpr.evalNumericOperationTree,
        bodyAdmitted, treeEvaluated]
  · simp [LoweredNumericExpr.evalNumericOperation?, bodyAdmitted] at evaluated

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
    simp [NumericComparisonOf.evalSelected, NumericComparisonOf.evalWith,
      AuthoredNumericExpr.lowerForEvaluation,
      LoweredNumericExpr.evalAdmittedValidation?,
      FlatContext.resolveNumericValidationAtom,
      ValidationEvaluationContext.resolveNumericValidationAtom,
      FlatContext.resolveNumericArithmetic,
      NumericOperand.toValidationArithmetic,
      NumericValidationOp.eval,
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
    simp [NumericComparisonOf.evalSelected, NumericComparisonOf.evalWith,
      AuthoredNumericExpr.lowerForEvaluation,
      LoweredNumericExpr.evalAdmittedValidation?,
      FlatContext.resolveNumericValidationAtom,
      ValidationEvaluationContext.resolveNumericValidationAtom,
      FlatContext.resolveNumericArithmetic,
      NumericOperand.toValidationArithmetic,
      NumericValidationOp.eval,
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
    simp [NumericComparisonOf.evalSelected, NumericComparisonOf.evalWith,
      AuthoredNumericExpr.lowerForEvaluation,
      LoweredNumericExpr.evalAdmittedValidation?,
      FlatContext.resolveNumericValidationAtom,
      ValidationEvaluationContext.resolveNumericValidationAtom,
      FlatContext.resolveNumericArithmetic,
      NumericOperand.toValidationArithmetic,
      NumericValidationOp.eval,
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
    simp [NumericComparisonOf.evalSelected, NumericComparisonOf.evalWith,
      AuthoredNumericExpr.lowerForEvaluation,
      LoweredNumericExpr.evalAdmittedValidation?,
      FlatContext.resolveNumericValidationAtom,
      ValidationEvaluationContext.resolveNumericValidationAtom,
      NumericOperand.toValidationArithmetic,
      NumericValidationOp.eval,
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
    simp [NumericComparisonOf.evalSelected, NumericComparisonOf.evalWith,
      AuthoredNumericExpr.lowerForEvaluation,
      LoweredNumericExpr.evalAdmittedValidation?,
      FlatContext.resolveNumericValidationAtom,
      ValidationEvaluationContext.resolveNumericValidationAtom,
      NumericOperand.toValidationArithmetic,
      NumericValidationOp.eval,
      NumericComparisonOp.eval, NumericToleranceRange.eval, evaluated]

/-- Full validation gates a checked numeric condition before any empty-Number substitution can fire. -/
theorem checkedNumericComparison_emptyRow_notFired
    (checked : CheckedNumericComparison model)
    (context : FlatContext) :
    checked.evalFull context false = .notFired := by
  rfl

end A12Kernel
