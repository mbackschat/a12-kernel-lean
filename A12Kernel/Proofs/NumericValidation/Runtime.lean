import A12Kernel.Elaboration.NumericValidation

/-! # Checked numeric-validation runtime laws -/

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

/-- A model-certified direct Number source under a nonempty repeatable declaration cannot silently select the scalar evaluator. -/
theorem orderedNumericValidationAtom_repeatableField_requiresAddressed
    (field : FlatNumberField) (declaration : FlatFieldDecl)
    (lookup : model.lookupUniqueId field.id = .ok declaration)
    (repeatable : declaration.repeatableScope.isEmpty = false) :
    (OrderedNumericValidationAtom.ordinary (.field field)).requiresAddressedValidation
        (model := model) = true := by
  simp [OrderedNumericValidationAtom.requiresAddressedValidation,
    lookup, repeatable]

/-- A model-certified direct temporal component under a nonempty repeatable declaration uses the shared addressed entry requirement without erasing the selected component. -/
theorem orderedNumericValidationAtom_repeatableTemporalFieldPart_requiresAddressed
    (field : FlatTemporalField) (part : TemporalNumericPart)
    (declaration : FlatFieldDecl)
    (lookup : model.lookupUniqueId field.id = .ok declaration)
    (repeatable : declaration.repeatableScope.isEmpty = false) :
    (OrderedNumericValidationAtom.ordinary
        (.temporalFieldPart field part)).requiresAddressedValidation
        (model := model) = true := by
  simp [OrderedNumericValidationAtom.requiresAddressedValidation,
    lookup, repeatable]

/-- A Date completed-period difference cannot fall back to scalar evaluation when its model-certified field operand is repeatable; the other operand may remain model-owned Base Year. -/
theorem orderedNumericValidationAtom_repeatableDateDifference_requiresAddressed
    (unit : DateDifferenceUnit) (field : FlatTemporalField)
    (year : Int) (source : BaseYearDateSource)
    (declaration : FlatFieldDecl)
    (lookup : model.lookupUniqueId field.id = .ok declaration)
    (repeatable : declaration.repeatableScope.isEmpty = false) :
    (OrderedNumericValidationAtom.ordinary
      (.dateDifference unit (.field field)
        (.baseYear year source))).requiresAddressedValidation
        (model := model) = true := by
  simp [OrderedNumericValidationAtom.requiresAddressedValidation,
    lookup, repeatable]

/-- A checked sub-day difference cannot fall back to scalar evaluation when either model-certified DateTime field is repeatable. -/
theorem orderedNumericValidationAtom_repeatableDateTimeDifference_requiresAddressed
    (unit : DateTimeDifferenceUnit)
    (left right : FlatTemporalField) (declaration : FlatFieldDecl)
    (lookup : model.lookupUniqueId left.id = .ok declaration)
    (repeatable : declaration.repeatableScope.isEmpty = false) :
    (OrderedNumericValidationAtom.ordinary
      (.dateTimeDifference unit left right)).requiresAddressedValidation
        (model := model) = true := by
  simp [OrderedNumericValidationAtom.requiresAddressedValidation,
    lookup, repeatable]

/-- A concrete-profile calendar-day difference keeps addressed evaluation when its model-certified Date or DateTime field operand is repeatable. -/
theorem orderedNumericValidationAtom_repeatableDayDifference_requiresAddressed
    (profile : ModelZone.ConcreteProfile) (field : FlatTemporalField)
    (year : Int) (source : BaseYearDateSource)
    (declaration : FlatFieldDecl)
    (lookup : model.lookupUniqueId field.id = .ok declaration)
    (repeatable : declaration.repeatableScope.isEmpty = false) :
    (OrderedNumericValidationAtom.ordinary
      (.dayDifference profile (.field field)
        (.baseYear year source))).requiresAddressedValidation
        (model := model) = true := by
  simp [OrderedNumericValidationAtom.requiresAddressedValidation,
    lookup, repeatable]

/-- A model-certified evaluated-String `Length` source under a nonempty repeatable declaration uses the same addressed entry requirement. -/
theorem orderedNumericValidationAtom_repeatableStringLength_requiresAddressed
    (field : FlatStringField) (declaration : FlatFieldDecl)
    (lookup : model.lookupUniqueId field.id = .ok declaration)
    (repeatable : declaration.repeatableScope.isEmpty = false) :
    (OrderedNumericValidationAtom.ordinary
        (.stringLength field)).requiresAddressedValidation
        (model := model) = true := by
  simp [OrderedNumericValidationAtom.requiresAddressedValidation,
    lookup, repeatable]

/-- A checked `RangeAsNumber` source under a nonempty repeatable String declaration uses the shared addressed entry requirement while retaining its interval. -/
theorem orderedNumericValidationAtom_repeatableStringRange_requiresAddressed
    (field : FlatStringField) (start finish : Nat)
    (declaration : FlatFieldDecl)
    (lookup : model.lookupUniqueId field.id = .ok declaration)
    (repeatable : declaration.repeatableScope.isEmpty = false) :
    (OrderedNumericValidationAtom.ordinary
        (.stringRange field start finish)).requiresAddressedValidation
        (model := model) = true := by
  simp [OrderedNumericValidationAtom.requiresAddressedValidation,
    lookup, repeatable]

/-- A certified conversion source under a nonempty repeatable declaration uses the shared addressed entry requirement without erasing its text projection. -/
theorem orderedNumericValidationAtom_repeatableFieldValueAsNumber_requiresAddressed
    (source : ResolvedFieldValueAsNumberSource) (declaration : FlatFieldDecl)
    (lookup : model.lookupUniqueId source.fieldId = .ok declaration)
    (repeatable : declaration.repeatableScope.isEmpty = false) :
    (OrderedNumericValidationAtom.ordinary
        (.fieldValueAsNumber source)).requiresAddressedValidation
        (model := model) = true := by
  simp [OrderedNumericValidationAtom.requiresAddressedValidation,
    lookup, repeatable]

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

/-- Addressed generated validation delegates an entity-list aggregate to the sole checked validation-phase fold and changes only its numeric-domain projection. -/
theorem orderedNumericValidationAtom_aggregate_addressed_delegates
    (source : CheckedNumberEntitySource model) (op : NumericAggregateOp)
    (scalar : ValidationEvaluationContext) (document : Document)
    (outer : Env) (read : Env → FieldId → CheckedCell) :
    OrderedNumericValidationAtom.resolveAddressed
        (.aggregate op source) {
          scalar, outer, input := .legacy document read
        } =
      ((source.evaluateValidationAggregateIn op document outer
        scalar.fields read).mapError CheckedAddressingError.addressing).map
          NumericOperand.toValidationArithmetic := by
  rfl

/-- Whole-rule addressed validation delegates the same aggregate atom to the immutable checked-document owner and preserves its richer structural error unchanged. -/
theorem orderedNumericValidationAtom_aggregate_checkedDocument_delegates
    (source : CheckedNumberEntitySource model) (op : NumericAggregateOp)
    (scalar : ValidationEvaluationContext) (document : CheckedDocument model)
    (outer : Env) :
    OrderedNumericValidationAtom.resolveAddressed
        (.aggregate op source) {
          scalar, outer, input := .checked document
        } =
      (source.evaluateCheckedDocumentValidationAggregate
        op document outer).map NumericOperand.toValidationArithmetic := by
  rfl

/-- Whole-rule addressed validation preserves `FirstFilledValue`'s checked-document prefix scan and changes only its terminal numeric projection. -/
theorem orderedNumericValidationAtom_firstFilled_checkedDocument_delegates
    (source : CheckedNumberEntitySource model)
    (scalar : ValidationEvaluationContext) (document : CheckedDocument model)
    (outer : Env) :
    OrderedNumericValidationAtom.resolveAddressed
        (.firstFilled source) {
          scalar, outer, input := .checked document
        } =
      (do
        let result ←
          source.evaluateCheckedDocumentValidation document outer .full
        match result with
        | .nonRelevant => pure (.error .nonRelevant)
        | .evaluated result =>
            pure result.asValidationOperand.toValidationArithmetic) := by
  rfl

/-- Addressed generated validation preserves the checked value-count constant and per-selected-cell filter provenance through the sole validation-phase evaluator. -/
theorem orderedNumericValidationAtom_valueCount_addressed_delegates
    (source : CheckedNumberEntitySource model) (expected : Rat)
    (scalar : ValidationEvaluationContext) (document : Document)
    (outer : Env) (read : Env → FieldId → CheckedCell) :
    OrderedNumericValidationAtom.resolveAddressed
        (.valueCount expected source) {
          scalar, outer, input := .legacy document read
        } =
      ((source.evaluateValueCountValidationIn expected document
        outer scalar.fields read).mapError CheckedAddressingError.addressing).map
          NumericOperand.toValidationArithmetic := by
  rfl

/-- Whole-rule addressed validation delegates Number value count to the sole checked-document draining fold without altering its expected value or filter provenance. -/
theorem orderedNumericValidationAtom_valueCount_checkedDocument_delegates
    (source : CheckedNumberEntitySource model) (expected : Rat)
    (scalar : ValidationEvaluationContext) (document : CheckedDocument model)
    (outer : Env) :
    OrderedNumericValidationAtom.resolveAddressed
        (.valueCount expected source) {
          scalar, outer, input := .checked document
        } =
      (source.evaluateCheckedDocumentValueCountValidation
        expected document outer).map NumericOperand.toValidationArithmetic := by
  rfl

/-- Addressed generated validation preserves the complete checked token source and delegates to its sole validation-phase traversal. -/
theorem orderedNumericValidationAtom_tokenValueCount_addressed_delegates
    (source : CheckedTokenValueCountSource model)
    (scalar : ValidationEvaluationContext) (document : Document)
    (outer : Env) (read : Env → FieldId → CheckedCell) :
    OrderedNumericValidationAtom.resolveAddressed
        (.tokenValueCount source) {
          scalar, outer, input := .legacy document read
        } =
      ((source.evaluateValidation document outer
        scalar.fields.read read).mapError CheckedAddressingError.addressing).map
          NumericOperand.toValidationArithmetic := by
  rfl

/-- Whole-rule addressed validation delegates typed token value count to the shared checked-document operand resolver and unchanged projection-aware fold. -/
theorem orderedNumericValidationAtom_tokenValueCount_checkedDocument_delegates
    (source : CheckedTokenValueCountSource model)
    (scalar : ValidationEvaluationContext) (document : CheckedDocument model)
    (outer : Env) :
    OrderedNumericValidationAtom.resolveAddressed
        (.tokenValueCount source) {
          scalar, outer, input := .checked document
        } =
      (source.evaluateCheckedDocumentValidation
        document outer).map NumericOperand.toValidationArithmetic := by
  rfl

/-- Addressed generated validation delegates `SumOfProducts` to the sole checked row-paired fold and changes only its numeric-domain projection. -/
theorem orderedNumericValidationAtom_sumOfProducts_addressed_delegates
    (source : CheckedNumericProductAggregate model)
    (scalar : ValidationEvaluationContext) (document : Document)
    (outer : Env) (read : Env → FieldId → CheckedCell) :
    OrderedNumericValidationAtom.resolveAddressed
        (.sumOfProducts source) {
          scalar, outer, input := .legacy document read
        } =
      ((source.evaluateAt .validation document outer read).mapError
        CheckedAddressingError.addressing).map
          NumericOperand.toValidationArithmetic := by
  rfl

/-- The immutable checked-document branch delegates the same product source without replacing its topology or collapsing structural failure. -/
theorem orderedNumericValidationAtom_sumOfProducts_checked_document_delegates
    (source : CheckedNumericProductAggregate model)
    (scalar : ValidationEvaluationContext)
    (document : CheckedDocument model) (outer : Env) :
    OrderedNumericValidationAtom.resolveAddressed
        (.sumOfProducts source) {
          scalar, outer, input := .checked document
        } =
      (source.evaluateCheckedDocumentAt
        .validation document outer).map
          NumericOperand.toValidationArithmetic := by
  rfl

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

end A12Kernel
