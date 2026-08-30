import A12Kernel.Elaboration.NumericComputation
import A12Kernel.Proofs.GroupPresence
import A12Kernel.Proofs.Observation
import A12Kernel.Proofs.SingleGroupElaboration

/-! # Numeric computation-expression laws -/

namespace A12Kernel

/-- Exact duplication is precisely the overlap case that reports `MVK_DUPLICATE_PARAM1`;
    every proper ancestor overlap remains the distinct `MVK_DUPLICATE_PARAM2` class. -/
theorem numericComputation_groupCount_duplicateParam1_iff
    (left right : GroupPath) :
    NumericComputationElabError.groupCountDiagnostic?
        (.overlappingGroupCountOperands left right) =
      some .duplicateParam1 ↔ left = right := by
  simp [NumericComputationElabError.groupCountDiagnostic?]

/-- A resolved computation aggregate atom consumes the same aggregate fold under computation-phase observation, then erases only validation fillability. -/
theorem numericComputationAggregate_evaluatesThroughSharedFold
    (context : ScalarComputationContext) (op : NumericAggregateOp)
    (source : ResolvedNumericAggregateFields) :
    context.readNumericComputationAtom (.aggregate op source) =
      .ok ((source.evaluate op fun field =>
        observeCell .computation (context.read field)).toComputationResult) := by
  rfl

/-- A checked mixed direct/star computation aggregate delegates to the phase-specific entity-list traversal and erases only validation fillability after that traversal and the established fold succeed. -/
theorem checkedNumberEntitySource_computation_delegates
    (checked : CheckedNumberEntitySource model)
    (op : NumericAggregateOp) (document : Document) (outer : Env)
    (directRead : FieldId → CheckedCell)
    (filterRead starRead : Env → FieldId → CheckedCell) :
    checked.evaluateComputation op document outer directRead filterRead starRead =
      (do
        let operand ← checked.evaluateComputationAggregate op document outer
          directRead filterRead starRead
        pure operand.toComputationResult) := by
  rfl

/-- The full computation context preserves the checked aggregate's document, outer environment, and both readers exactly, mapping only structural addressing failure into the expression fault domain. -/
theorem numericComputationEvaluationContext_aggregate_delegates
    (context : NumericComputationEvaluationContext)
    (source : CheckedNumberEntitySource model) (op : NumericAggregateOp) :
    context.readCheckedNumericComputationAtom (.numeric (.aggregate op source)) =
      (source.evaluateComputation op context.document context.outer
        context.scalar.read context.filterRead context.starRead).mapError
          NumericComputationFault.repeatableAddressing := by
  rfl

/-- A fixed group count acquires no iteration reader and no outer environment.

    This restates a guard that used to say the count delegates to the scalar reader outright and
    so needs no document at all. The measured repeatable-descendant shape falsified the *document*
    half — a group whose only content is a repeatable descendant counts on an instantiated row, and
    only the document carries rows — so the clause reads `document` deliberately. Everything else
    the addressed context adds stays out: the count is invariant in `outer`, `filterRead`, and
    `starRead`, which is what still separates it from an iterated or correlated read. -/
theorem numericComputationEvaluationContext_filledGroupCount_ignoresIteration
    (context : NumericComputationEvaluationContext)
    (groups : List ResolvedGroupReference)
    (outer : Env) (filterRead starRead : Env → FieldId → CheckedCell) :
    ({ context with outer, filterRead, starRead } :
        NumericComputationEvaluationContext).readCheckedNumericComputationAtom
        (model := model) (.numeric (.filledGroupCount groups)) =
      context.readCheckedNumericComputationAtom
        (model := model) (.numeric (.filledGroupCount groups)) := by
  rfl

/-- The full computation context retains the checked value-count source, authored constant, addressed readers, and structural-failure channel exactly. -/
theorem numericComputationEvaluationContext_valueCount_delegates
    (context : NumericComputationEvaluationContext)
    (source : CheckedNumberEntitySource model) (expected : Rat) :
    context.readCheckedNumericComputationAtom (.valueCount expected source) =
      ((source.evaluateValueCountComputation expected context.document
        context.outer context.scalar.read context.filterRead
        context.starRead).map NumericOperand.toComputationResult).mapError
          NumericComputationFault.repeatableAddressing := by
  rfl

/-- The full computation context preserves a checked token count's domain certificate, addressed readers, and structural-failure channel exactly. -/
theorem numericComputationEvaluationContext_tokenValueCount_delegates
    (context : NumericComputationEvaluationContext)
    (source : CheckedTokenValueCountSource model) :
    context.readCheckedNumericComputationAtom (.tokenValueCount source) =
      ((source.evaluateComputation context.document context.outer
        context.scalar.read context.filterRead context.starRead).map
          NumericOperand.toComputationResult).mapError
            NumericComputationFault.repeatableAddressing := by
  rfl

/-- The full computation context preserves the complete direct/star Boolean/Confirm source and erases only validation fillability after the shared exact-token tally. -/
theorem numericComputationEvaluationContext_booleanValueCount_delegates
    (context : NumericComputationEvaluationContext)
    (source : CheckedBooleanValueCountSource model) :
    context.readCheckedNumericComputationAtom (.booleanValueCount source) =
      ((source.evaluateComputation context.document context.outer
        context.scalar.read context.filterRead context.starRead).map
          NumericOperand.toComputationResult).mapError
            NumericComputationFault.repeatableAddressing := by
  rfl

/-- The scalar compatibility evaluator cannot erase repeatable addressing by inventing an empty document. -/
theorem scalarComputationContext_repeatableAggregate_requiresContext
    (context : ScalarComputationContext)
    (source : CheckedNumberEntitySource model) (op : NumericAggregateOp)
    (repeatable : source.directAggregateFields? = none) :
    context.readCheckedNumericComputationAtom (.numeric (.aggregate op source)) =
      .error .repeatableContextRequired := by
  simp [ScalarComputationContext.readCheckedNumericComputationAtom,
    ScalarComputationContext.readNumericComputationAtomWith, repeatable]
  rfl

/-- Scalar computation rejects a repeatable value-count source rather than discarding its topology and filter provenance. -/
theorem scalarComputationContext_repeatableValueCount_requiresContext
    (context : ScalarComputationContext)
    (source : CheckedNumberEntitySource model) (expected : Rat)
    (repeatable : source.directFields? = none) :
    context.readCheckedNumericComputationAtom (.valueCount expected source) =
      .error .repeatableContextRequired := by
  simp [ScalarComputationContext.readCheckedNumericComputationAtom,
    CheckedNumberEntitySource.evaluateDirectValueCountAt?, repeatable]
  rfl

/-- Scalar computation cannot erase a repeatable token count's topology, filter provenance, or Enumeration-domain certificate. -/
theorem scalarComputationContext_repeatableTokenValueCount_requiresContext
    (context : ScalarComputationContext)
    (source : CheckedTokenValueCountSource model)
    (repeatable : source.source.directFields? = none) :
    context.readCheckedNumericComputationAtom (.tokenValueCount source) =
      .error .repeatableContextRequired := by
  simp [ScalarComputationContext.readCheckedNumericComputationAtom,
    CheckedTokenValueCountSource.evaluateDirectAt?, repeatable]
  rfl

/-- A value-count atom has integral scale independently of its selected Number declarations. -/
theorem checkedNumericComputationAtom_valueCount_scaleSummary
    (source : CheckedNumberEntitySource model) (expected : Rat) :
    CheckedNumericComputationAtom.numericScaleSummary
        (.valueCount expected source) =
      NumericScaleSummary.field 0 := by
  rfl

/-- A String/stored-Enumeration value count retains its checked source while exposing the same fixed integral scale. -/
theorem checkedNumericComputationAtom_tokenValueCount_scaleSummary
    (source : CheckedTokenValueCountSource model) :
    CheckedNumericComputationAtom.numericScaleSummary
        (.tokenValueCount source) =
      NumericScaleSummary.field 0 := by
  rfl

/-- A Boolean/Confirm value count exposes the same fixed integral scale independently of its admitted constant and source kinds. -/
theorem checkedNumericComputationAtom_booleanValueCount_scaleSummary
    (source : CheckedBooleanValueCountSource model) :
    CheckedNumericComputationAtom.numericScaleSummary
        (.booleanValueCount source) =
      NumericScaleSummary.field 0 := by
  rfl

/-- The addressed computation context delegates a checked `SumOfProducts` atom to the existing common-row product fold and maps only structural addressing failure. -/
theorem numericComputationEvaluationContext_product_delegates
    (context : NumericComputationEvaluationContext)
    (source : CheckedNumericProductAggregate model) :
    context.readCheckedNumericComputationAtom (.sumOfProducts source) =
      (source.evaluateComputation context.document context.outer
        context.starRead).mapError
          NumericComputationFault.repeatableAddressing := by
  rfl

/-- The scalar compatibility evaluator rejects `SumOfProducts` explicitly because the checked pair requires its certified repeatable topology. -/
theorem scalarComputationContext_product_requiresContext
    (context : ScalarComputationContext)
    (source : CheckedNumericProductAggregate model) :
    context.readCheckedNumericComputationAtom (.sumOfProducts source) =
      .error .repeatableContextRequired := by
  rfl

/-- A checked product atom reports exactly its two owned field references. -/
theorem checkedNumericComputationAtom_product_references
    (source : CheckedNumericProductAggregate model) (field : FieldId) :
    CheckedNumericComputationAtom.references model field
        (.sumOfProducts source) =
      (source.left.field.id == field || source.right.field.id == field) := by
  rfl

/-- A checked product atom derives its result-scale summary from the existing multiplication-shaped pair summary. -/
theorem checkedNumericComputationAtom_product_scaleSummary
    (source : CheckedNumericProductAggregate model) :
    CheckedNumericComputationAtom.numericScaleSummary
        (.sumOfProducts source) =
      source.scaleSummary := by
  rfl

/-- Computation selects its own phase observation before reusing the shared String-length projection. -/
theorem numericComputation_stringLength_delegates
    (context : ScalarComputationContext) (field : FlatStringField) :
    context.readNumericComputationAtom (.stringLength field) =
      .ok ((observeCell .computation
        (context.read field.id)).asStringLengthOperand.toComputationResult) := by
  rfl

/-- Computation erases range fillability but keeps the missing String source's numeric zero value. -/
theorem numericComputation_stringRange_empty_zero
    (context : ScalarComputationContext) (field : FlatStringField)
    (start finish : Nat)
    (observed : observeCell .computation (context.read field.id) = .empty) :
    context.readNumericComputationAtom (.stringRange field start finish) =
      .ok (.value 0) := by
  simp [ScalarComputationContext.readNumericComputationAtom,
    ScalarComputationContext.readNumericComputationAtomWith, observed]
  rfl

/-- A present String source delegates once to the shared normalized UTF-16/digits-only conversion. -/
theorem numericComputation_stringRange_value
    (context : ScalarComputationContext) (field : FlatStringField)
    (start finish : Nat) (value : String)
    (observed : observeCell .computation (context.read field.id) =
      .value (.str value)) :
    context.readNumericComputationAtom (.stringRange field start finish) =
      .ok (.value (utf16RangeAsNatural value start finish)) := by
  simp [ScalarComputationContext.readNumericComputationAtom,
    ScalarComputationContext.readNumericComputationAtomWith, observed]
  rfl

/-- A reached computation poison survives range conversion with its exact cause. -/
theorem numericComputation_stringRange_poison_preservesCause
    (context : ScalarComputationContext) (field : FlatStringField)
    (start finish : Nat) (cause : FormalCause)
    (observed : observeCell .computation (context.read field.id) = .poison cause) :
    context.readNumericComputationAtom (.stringRange field start finish) =
      .ok (.poison cause) := by
  simp [ScalarComputationContext.readNumericComputationAtom,
    ScalarComputationContext.readNumericComputationAtomWith, observed]
  rfl

/-- Computation erases conversion fillability but keeps the missing String or Enumeration/category source's numeric zero. -/
theorem numericComputation_fieldValueAsNumber_empty_zero
    (context : ScalarComputationContext)
    (source : ResolvedFieldValueAsNumberSource)
    (observed : observeCell .computation (context.read source.fieldId) = .empty) :
    context.readNumericComputationAtom (.fieldValueAsNumber source) =
      .ok (.value 0) := by
  simp [ScalarComputationContext.readNumericComputationAtom,
    ScalarComputationContext.readNumericComputationAtomWith, observed]
  rfl

/-- A present admitted String or Enumeration value projects to the same exact rational amount in computation. -/
theorem numericComputation_fieldValueAsNumber_value
    (context : ScalarComputationContext)
    (source : ResolvedFieldValueAsNumberSource) (value : Value) (amount : Rat)
    (observed : observeCell .computation (context.read source.fieldId) =
      .value value)
    (converted : source.valueFor? value = some amount) :
    context.readNumericComputationAtom (.fieldValueAsNumber source) =
      .ok (.value amount) := by
  simp [ScalarComputationContext.readNumericComputationAtom,
    ScalarComputationContext.readNumericComputationAtomWith,
    observed, converted]
  rfl

/-- A reached computation poison survives String or Enumeration/category conversion with its exact cause. -/
theorem numericComputation_fieldValueAsNumber_poison_preservesCause
    (context : ScalarComputationContext)
    (source : ResolvedFieldValueAsNumberSource) (cause : FormalCause)
    (observed : observeCell .computation (context.read source.fieldId) =
      .poison cause) :
    context.readNumericComputationAtom (.fieldValueAsNumber source) =
      .ok (.poison cause) := by
  simp [ScalarComputationContext.readNumericComputationAtom,
    ScalarComputationContext.readNumericComputationAtomWith, observed]
  rfl

/-- A checked Numeric definition retains a syntactically valid computation declaration group even when
its expression has no field operand. -/
theorem checkedNumericComputationOperation_declaringGroup_valid
    (checked : CheckedNumericComputationOperation model) :
    GroupPath.isValid checked.declaringGroup = true :=
  checked.declaringGroupValid

/-- A checked operation contains no direct reference to its own target at any depth of the shared authored tree. -/
theorem checkedNumericComputationOperation_noTargetReference
    (checked : CheckedNumericComputationOperation model) :
    checked.core.expression.anyAtom
      (CheckedNumericComputationAtom.references model
        checked.core.target.id) = false := by
  have admitted := checked.wellFormed
  simp only [NumericComputationOperation.WellFormed,
    NumericComputationOperation.wellFormedBool, Bool.and_eq_true] at admitted
  simpa using admitted.1.1.1.2

/-- Every checked computation operation lies in the shared complete numeric-operation fragment. -/
theorem checkedNumericComputationOperation_admittedShape
    (checked : CheckedNumericComputationOperation model) :
    checked.core.expression.isAdmittedResolvedNumericOperation = true := by
  have admitted := checked.wellFormed
  simp only [NumericComputationOperation.WellFormed,
    NumericComputationOperation.wellFormedBool, Bool.and_eq_true] at admitted
  exact admitted.1.1.2

/-- Every checked operation either carries the explicit warning suppression or satisfies the ordinary exact result-scale gate. -/
theorem checkedNumericComputationOperation_scaleGate
    (checked : CheckedNumericComputationOperation model)
    (summary : NumericScaleSummary)
    (summarized : checked.core.expression.summary?
      CheckedNumericComputationAtom.numericScaleSummary = some summary) :
    exactNumericScaleComparisonAllowedWithSuppression
      checked.core.suppressExactScaleWarning
      (NumericScaleSummary.field checked.core.target.info.scale) summary = true := by
  have admitted := checked.wellFormed
  simp only [NumericComputationOperation.WellFormed,
    NumericComputationOperation.wellFormedBool, Bool.and_eq_true,
    summarized] at admitted
  exact admitted.2

/-- Attaching a target policy with a different scale/signedness summary is rejected before evaluation. -/
theorem checkedNumericComputationOperation_attachTargetPolicy_rejectsMismatch
    (checked : CheckedNumericComputationOperation model)
    (policy : NumericTargetPolicy)
    (mismatch : policy.info ≠ checked.core.target.info) :
    checked.attachTargetPolicy policy =
      .error (.targetPolicyMismatch checked.core.target.info policy.info) := by
  simp [CheckedNumericComputationOperation.attachTargetPolicy, mismatch]
  rfl

/-- A target-attached checked operation retains a policy coherent with its already-resolved target. -/
theorem checkedNumericTargetComputationOperation_policyMatches
    (checked : CheckedNumericTargetComputationOperation model) :
    checked.policy.info = checked.operation.core.target.info :=
  checked.targetMatches

/-- Target-attached evaluation dispatches solely by the certified suppression bit after preserving the exact expression result. -/
theorem checkedNumericTargetComputationOperation_evaluate_routes
    (checked : CheckedNumericTargetComputationOperation model)
    (context : ScalarComputationContext)
    (result : NumericComputationResult)
    (evaluated : checked.operation.evaluate context = .ok result) :
    checked.evaluate context =
      .ok (if checked.operation.core.suppressExactScaleWarning then
        checked.policy.checkWithScaleWarningSuppressed result
      else
        checked.policy.check result) := by
  simp only [CheckedNumericTargetComputationOperation.evaluate]
  rw [evaluated]
  cases checked.operation.core.suppressExactScaleWarning <;> rfl

/-- Target-attached addressed evaluation preserves the same certified suppression dispatch after the unified expression has consumed its repeatable inputs. -/
theorem checkedNumericTargetComputationOperation_evaluateIn_routes
    (checked : CheckedNumericTargetComputationOperation model)
    (context : NumericComputationEvaluationContext)
    (result : NumericComputationResult)
    (evaluated : checked.operation.evaluateIn context = .ok result) :
    checked.evaluateIn context =
      .ok (if checked.operation.core.suppressExactScaleWarning then
        checked.policy.checkWithScaleWarningSuppressed result
      else
        checked.policy.check result) := by
  simp only [CheckedNumericTargetComputationOperation.evaluateIn]
  rw [evaluated]
  cases checked.operation.core.suppressExactScaleWarning <;> rfl

/-- Numeric Base Year is the fixed declared year and performs no context read in a checked computation expression. -/
theorem numericComputation_baseYear_evaluatesYear
    (context : ScalarComputationContext) (year : Int) :
    (AuthoredNumericExpr.atom (.baseYear year) :
      AuthoredNumericExpr NumericComputationAtom).evaluateResolvedComputation context =
        .ok (.value year) := by
  rfl

/-- A Base-Year date-component source is a fixed context-free Number in checked computation expressions. -/
theorem numericComputation_baseYearDatePart_evaluates
    (context : ScalarComputationContext) (year : Int)
    (source : BaseYearDateSource) (part : DateNumericPart) :
    (AuthoredNumericExpr.atom (.baseYearDatePart year source part) :
      AuthoredNumericExpr NumericComputationAtom).evaluateResolvedComputation context =
        .ok (.value (baseYearDateSourceNumericPart year source part)) := by
  rfl

/-- Every clean temporal component projection shares one computation-phase value path; Date and Time specialization is supplied only by the projection function. -/
theorem readTemporalNumeric_value
    (context : ScalarComputationContext) (field : FlatTemporalField)
    (project : TemporalValue → Option Rat) (value : TemporalValue) (amount : Rat)
    (kind : value.kind = field.kind)
    (projected : project value = some amount)
    (observed : observeCell .computation (context.read field.id) =
      .value (.temporal value)) :
    context.readTemporalNumeric field project = .ok (.value amount) := by
  simp [ScalarComputationContext.readTemporalNumeric,
    observed, kind, projected] <;> rfl

/-- A supported date-difference source uses the same phase reads and maps its exact numeric/fault provenance once into computation outcome space. -/
theorem readDateDifference_evaluated
    (context : ScalarComputationContext) (unit : DateDifferenceUnit)
    (left right : ResolvedDateDifferenceOperand) (operand : NumericOperand)
    (evaluated : DateDifferenceOperand.evaluate unit
      (context.readDateDifferenceOperand left)
      (context.readDateDifferenceOperand right) = .ok operand) :
    context.readNumericComputationAtom (.dateDifference unit left right) =
      .ok operand.toComputationResult := by
  simp only [ScalarComputationContext.readNumericComputationAtom,
    ScalarComputationContext.readNumericComputationAtomWith]
  rw [evaluated]
  rfl

/-- A checked sub-day source resolves each admitted field/`Now` operand once and maps their exact instant difference into computation outcome space. -/
theorem readDateTimeDifference_evaluated
    (context : ScalarComputationContext)
    (unit : DateTimeSubdayUnit)
    (left right : FlatTemporalOperand)
    (leftOperand rightOperand : DateTimeDifferenceOperand)
    (leftResolved :
      context.readDateTimeDifferenceOperand left = .ok leftOperand)
    (rightResolved :
      context.readDateTimeDifferenceOperand right = .ok rightOperand) :
    context.readNumericComputationAtom
        (.dateTimeDifference unit left right) =
      .ok ((DateTimeDifferenceOperand.evaluate unit
        leftOperand rightOperand)
        |>.toComputationResult) := by
  simp only [ScalarComputationContext.readNumericComputationAtom,
    ScalarComputationContext.readNumericComputationAtomWith]
  rw [leftResolved, rightResolved]
  rfl

/-- A supported checked calendar-day source preserves its exact resolved instants and maps the selected profile result once into computation outcome space. -/
theorem readCalendarDayDifference_evaluated
    (context : ScalarComputationContext)
    (profile : ModelZone.ConcreteProfile)
    (left right : ResolvedDateDifferenceOperand) (operand : NumericOperand)
    (evaluated : CalendarDayDifferenceOperand.evaluate profile
      (context.readCalendarDayDifferenceOperand profile left)
      (context.readCalendarDayDifferenceOperand profile right) = .ok operand) :
    context.readNumericComputationAtom (.dayDifference profile left right) =
      .ok operand.toComputationResult := by
  simp only [ScalarComputationContext.readNumericComputationAtom,
    ScalarComputationContext.readNumericComputationAtomWith]
  rw [evaluated]
  rfl

/-- A computation-phase empty Number atom evaluates to the real numeric value zero. -/
theorem emptyNumericField_evaluates_zero
    (context : ScalarComputationContext) (declaration : FlatFieldDecl)
    (field : FlatNumberField)
    (resolved : declaration.toNumberField? = some field)
    (emptyRead : observeCell .computation (context.read field.id) = .empty) :
    (AuthoredNumericExpr.atom declaration).evaluateComputation context =
      .ok (.value 0) := by
  simp [AuthoredNumericExpr.evaluateComputation,
    AuthoredNumericExpr.lowerForEvaluation,
    LoweredNumericExpr.computationFault?,
    LoweredNumericExpr.computationFaultWith?,
    FlatFieldDecl.numericComputationFault?,
    LoweredNumericExpr.evalComputation,
    ScalarComputationContext.readNumeric, resolved, emptyRead]
  rfl

/-- Validation-scoped requiredness does not turn a computation-phase empty Number into poison. -/
theorem requiredEmptyNumericField_evaluates_zero
    (context : ScalarComputationContext) (declaration : FlatFieldDecl)
    (field : FlatNumberField)
    (resolved : declaration.toNumberField? = some field)
    (read :
      context.read field.id =
        (formalCheck { kind := .number field.info } .empty).withFinding .required) :
    (AuthoredNumericExpr.atom declaration).evaluateComputation context =
      .ok (.value 0) := by
  apply emptyNumericField_evaluates_zero context declaration field resolved
  rw [read]
  exact required_empty_observes_empty_in_computation
    { kind := .number field.info }

/-- An ordinary formal finding actually read by a numeric computation remains the same poison cause. -/
theorem poisonedNumericField_evaluates_poison
    (context : ScalarComputationContext) (declaration : FlatFieldDecl)
    (field : FlatNumberField)
    (cause : FormalCause)
    (resolved : declaration.toNumberField? = some field)
    (poisonedRead :
      observeCell .computation (context.read field.id) = .poison cause) :
    (AuthoredNumericExpr.atom declaration).evaluateComputation context =
      .ok (.poison cause) := by
  simp [AuthoredNumericExpr.evaluateComputation,
    AuthoredNumericExpr.lowerForEvaluation,
    LoweredNumericExpr.computationFault?,
    LoweredNumericExpr.computationFaultWith?,
    FlatFieldDecl.numericComputationFault?,
    LoweredNumericExpr.evalComputation,
    ScalarComputationContext.readNumeric, resolved, poisonedRead]
  rfl

/-- A direct division by numeric zero projects to computation-domain failure for every numerator. -/
theorem numericComputation_divideByZero_domainFailure
    (numerator : Rat) (numeratorScale zeroScale : Int)
    (context : ScalarComputationContext) :
    (AuthoredNumericExpr.binary .divide
      (.literal { value := numerator, authoredScale := numeratorScale })
      (.literal { value := 0, authoredScale := zeroScale })).evaluateComputation context =
        .ok .domainFailure := by
  simp [AuthoredNumericExpr.evaluateComputation,
    AuthoredNumericExpr.lowerForEvaluation,
    LoweredNumericExpr.computationFault?,
    LoweredNumericExpr.evalComputation]
  rfl

/-- Reached numeric power operands delegate exactly to the shared partial power value semantics. -/
theorem numericComputationResult_evalPower_values
    (base exponent : Rat) :
    NumericComputationResult.evalPower (.value base) (.value exponent) =
      match powerNumeric base exponent with
      | .value amount => .value amount
      | .notEvaluated => .domainFailure := by
  rfl

/-- Zero raised to a negative integral exponent reaches computation-domain failure, not a structural fault or clean no-value. -/
theorem numericComputation_zeroToNegativePower_domainFailure
    (baseScale exponentScale : Int)
    (context : ScalarComputationContext) :
    (AuthoredNumericExpr.power
      (.literal { value := 0, authoredScale := baseScale })
      (.literal { value := -1, authoredScale := exponentScale })).evaluateComputation
        context = .ok .domainFailure := by
  rfl

/-- Rounding preserves a domain-failed lowered child instead of manufacturing a numeric value. -/
theorem numericComputation_round_preserves_domainFailure
    (read : Atom →
      Except NumericComputationFault NumericComputationResult)
    (mode : DecimalRoundingMode) (places : RoundingPlaces)
    (body : LoweredNumericExpr Atom)
    (failed : body.evalComputation read = .ok .domainFailure) :
    (LoweredNumericExpr.round mode places body).evalComputation read =
      .ok .domainFailure := by
  simp only [LoweredNumericExpr.evalComputation]
  rw [failed]
  rfl

/-- Absolute value delegates every evaluated child result to the shared value-only transformation. -/
theorem numericComputation_abs_delegates
    (read : Atom →
      Except NumericComputationFault NumericComputationResult)
    (body : LoweredNumericExpr Atom)
    (result : NumericComputationResult)
    (evaluated : body.evalComputation read = .ok result) :
    (LoweredNumericExpr.abs body).evalComputation read =
      .ok result.absolute := by
  simp only [LoweredNumericExpr.evalComputation]
  rw [evaluated]
  cases result <;> rfl

/-- Every computation-value transformation preserves an arithmetic domain failure. -/
theorem numericComputationResult_mapValue_domainFailure
    (transform : Rat → Rat) :
    NumericComputationResult.domainFailure.mapValue transform = .domainFailure := by
  rfl

/-- Every computation-value transformation preserves the exact reached poison cause. -/
theorem numericComputationResult_mapValue_poison
    (cause : FormalCause) (transform : Rat → Rat) :
    (NumericComputationResult.poison cause).mapValue transform = .poison cause := by
  rfl

/-- The shared reached-result table always retains the left poison and its exact cause. -/
theorem numericComputationResult_combineReached_leftPoison
    (combineValues : Rat → Rat → NumericComputationResult)
    (cause : FormalCause) (right : NumericComputationResult) :
    NumericComputationResult.combineReached combineValues
      (.poison cause) right = .poison cause := by
  rfl

/-- Once the left result is known not to be poison, a reached right poison supplies the result. -/
theorem numericComputationResult_combineReached_rightPoison_of_notPoison
    (combineValues : Rat → Rat → NumericComputationResult)
    (left : NumericComputationResult) (cause : FormalCause)
    (leftNotPoison : ∀ leftCause, left ≠ .poison leftCause) :
    NumericComputationResult.combineReached combineValues
      left (.poison cause) = .poison cause := by
  cases left with
  | value _ => rfl
  | domainFailure => rfl
  | poison leftCause => exact (leftNotPoison leftCause rfl).elim

/-- A reached domain failure absorbs a clean value on its right for every numeric consumer. -/
theorem numericComputationResult_combineReached_leftDomain_value
    (combineValues : Rat → Rat → NumericComputationResult)
    (rightValue : Rat) :
    NumericComputationResult.combineReached combineValues
      .domainFailure (.value rightValue) = .domainFailure := by
  rfl

/-- A reached domain failure absorbs a clean value on its left for every numeric consumer. -/
theorem numericComputationResult_combineReached_value_rightDomain
    (combineValues : Rat → Rat → NumericComputationResult)
    (leftValue : Rat) :
    NumericComputationResult.combineReached combineValues
      (.value leftValue) .domainFailure = .domainFailure := by
  rfl

/-- Ordered evaluation returns a left poison independently of the right thunk. -/
theorem numericComputationResult_evalOrdered_leftPoison
    (right : Unit → Except NumericComputationFault NumericComputationResult)
    (combine : NumericComputationResult → NumericComputationResult →
      NumericComputationResult)
    (cause : FormalCause) :
    NumericComputationResult.evalOrdered
      (.ok (.poison cause)) right combine = .ok (.poison cause) := by
  rfl

/-- A nonpoison left result reaches the supplied right result and delegates both results to the combiner. -/
theorem numericComputationResult_evalOrdered_of_notPoison
    (left rightResult : NumericComputationResult)
    (right : Unit → Except NumericComputationFault NumericComputationResult)
    (combine : NumericComputationResult → NumericComputationResult →
      NumericComputationResult)
    (leftNotPoison : ∀ cause, left ≠ .poison cause)
    (rightEvaluated : right () = .ok rightResult) :
    NumericComputationResult.evalOrdered (.ok left) right combine =
      .ok (combine left rightResult) := by
  cases left with
  | value _ =>
      simp only [NumericComputationResult.evalOrdered]
      rw [rightEvaluated]
      rfl
  | domainFailure =>
      simp only [NumericComputationResult.evalOrdered]
      rw [rightEvaluated]
      rfl
  | poison cause => exact (leftNotPoison cause rfl).elim

/-- Arithmetic domain failure and inherited formal poison are distinct expression results. -/
theorem numericComputation_domainFailure_ne_poison (cause : FormalCause) :
    NumericComputationResult.domainFailure ≠ .poison cause := by
  intro equality
  cases equality

/-- A complete structural fault makes the public result independent of the computation context. -/
theorem numericComputation_structuralFault_contextIndependent
    (expression : AuthoredNumericExpr FlatFieldDecl)
    (context : ScalarComputationContext)
    (fault : NumericComputationFault)
    (invalid :
      expression.lowerForEvaluation.computationFault? = some fault) :
    expression.evaluateComputation context =
      .error fault := by
  simp [AuthoredNumericExpr.evaluateComputation,
    invalid]

/-- Depth is irrelevant to the compute-arm group count: one compute-present cell **anywhere**
    in an admitted operand's subtree makes that group count as filled.

    This is the consumer-visible half of `computationDescendants_admitted_eq_subtreeFields`. A
    re-narrowing of the operand's extent to its direct children breaks it, because a shell
    group — one owning no direct field at all — would then contribute an empty cell list and
    could never be filled. -/
theorem groupPresentForComputation_of_subtreeMember
    (context : ScalarComputationContext) (model : FlatModel)
    {reference : ResolvedGroupReference} {descendants : List FlatFieldDecl}
    (admitted : reference.computationDescendants? model = some descendants)
    {declaration : FlatFieldDecl}
    (member : declaration ∈ model.groupSubtreeFields reference.path)
    (present :
      (observeCell .computation (context.read declaration.id)).presentForComputation = true) :
    groupPresentForComputation
        (descendants.map fun source =>
          observeCell .computation (context.read source.id)) = true := by
  rw [computationDescendants_admitted_eq_subtreeFields admitted]
  exact List.any_eq_true.mpr
    ⟨observeCell .computation (context.read declaration.id),
      List.mem_map_of_mem member, present⟩

/-- Wherever the established fixed-only reader answers, the widened arm answers identically.

    The addressed evaluator now answers one shape the scalar reader refuses — a group whose subtree
    carries a repeatable descendant, whose content the Kernel decides structurally and a cell-list
    projection cannot express. That widening is deliberate, so the two are no longer equal on every
    list: this states the property that survives and is the one that matters, that the new arm
    changes nothing the old one already decided.

    It is stated per operand rather than per list because the widening happens per operand; the
    earlier list-level equality was a lift of exactly this, and lifting it now would need a
    hypothesis on every element that says no more than the conjunction of these. -/
theorem readGroupCountOperand_fixed_eq_scalarDescendants
    {model : FlatModel} (context : NumericComputationEvaluationContext)
    (reference : ResolvedGroupReference) (descendants : List FlatFieldDecl)
    (admitted : reference.computationDescendants? model = some descendants) :
    context.readGroupCountOperand model (.fixed reference) =
      .ok (.fixed (descendants.map fun declaration =>
        observeCell .computation (context.scalar.read declaration.id)) false) := by
  simp [NumericComputationEvaluationContext.readGroupCountOperand,
    NumericComputationEvaluationContext.readGroupContent, admitted, Except.map]

/-- The refusal survives too: a group outside both admitted shapes still refuses, naming its path. -/
theorem readGroupCountOperand_fixed_refuses_outside_both_shapes
    {model : FlatModel} (context : NumericComputationEvaluationContext)
    (reference : ResolvedGroupReference)
    (noCells : reference.computationDescendants? model = none)
    (noRows : reference.repeatableDescendantShape? model = none) :
    context.readGroupCountOperand model (.fixed reference) =
      .error (NumericComputationFault.unsupportedGroupCount reference.path) := by
  simp [NumericComputationEvaluationContext.readGroupCountOperand,
    NumericComputationEvaluationContext.readGroupContent, noCells, noRows, Except.map]

/-- The pre-read structural gate and the operand reader refuse exactly together.

    Two sites decide whether a fixed group-count operand is admitted, and only one of them runs on
    every route, so a widening that reaches the reader alone leaves the gate rejecting an operand
    the reader would have counted — which is how the repeatable-descendant shell stayed refused
    end to end after its reader already answered. Both now decide through
    `computationOperandAdmitted`, and this states that the equivalence is the shared predicate
    rather than a coincidence of two matches. -/
theorem readGroupCountOperand_fixed_error_iff_notAdmitted
    {model : FlatModel} (context : NumericComputationEvaluationContext)
    (reference : ResolvedGroupReference) :
    context.readGroupCountOperand model (.fixed reference) =
        .error (NumericComputationFault.unsupportedGroupCount reference.path) ↔
      reference.computationOperandAdmitted model = false := by
  simp only [NumericComputationEvaluationContext.readGroupCountOperand,
    NumericComputationEvaluationContext.readGroupContent,
    ResolvedGroupReference.computationOperandAdmitted]
  cases cells : reference.computationDescendants? model <;>
    cases rows : reference.repeatableDescendantShape? model <;>
      simp [Except.map]

/-- The two group-count atom shapes gate an all-fixed operand list identically.

    The companion to the reading law below, at the other site that can refuse an operand. Without
    it the mixed atom could stay ungated, and `evalOrdered`'s left-poison short circuit would then
    hide its structural fault behind a branch that is never reached — the fault reported for one
    atom and swallowed for the other over the identical operand. -/
theorem numericComputationFault_filledGroupCount_eq_mixed
    {model : FlatModel} (groups : List ResolvedGroupReference) :
    CheckedNumericComputationAtom.numericComputationFault?
        (model := model) (.numeric (.filledGroupCount groups)) =
      CheckedNumericComputationAtom.numericComputationFault?
        (model := model) (.filledGroupCountMixed (groups.map .fixed)) := by
  simp [CheckedNumericComputationAtom.numericComputationFault?, List.findSome?_map,
    Function.comp_def]

/-- The two group-count atom shapes read an all-fixed operand list identically.

    An authored list reaches `filledGroupCountMixed` only when some operand carries a star, so
    without this law an operand's admissibility could depend on a **sibling's** form: the addressed
    evaluator delegated the starless atom to the scalar reader, which necessarily refuses a
    repeatable-descendant operand, while the mixed atom answered the identical operand from the
    document. This states the invariant that closes that seam — atom shape is a routing detail and
    carries no semantics of its own. -/
theorem readCheckedNumericComputationAtom_filledGroupCount_eq_mixed
    {model : FlatModel} (context : NumericComputationEvaluationContext)
    (groups : List ResolvedGroupReference) :
    context.readCheckedNumericComputationAtom (model := model)
        (.numeric (.filledGroupCount groups)) =
      context.readCheckedNumericComputationAtom (model := model)
        (.filledGroupCountMixed (groups.map .fixed)) := by
  simp [NumericComputationEvaluationContext.readCheckedNumericComputationAtom,
    ScalarComputationContext.readNumericComputationAtomWith,
    NumericComputationEvaluationContext.readFilledGroupCount, List.mapM_map,
    Function.comp_def]

end A12Kernel
