import A12Kernel.Elaboration.NumericComputation
import A12Kernel.Proofs.Observation

/-! # Numeric computation-expression laws -/

namespace A12Kernel

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

end A12Kernel
