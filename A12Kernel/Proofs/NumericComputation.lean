import A12Kernel.Elaboration.NumericComputation
import A12Kernel.Proofs.Observation

/-! # Numeric computation-expression laws -/

namespace A12Kernel

/-- A checked operation contains no direct reference to its own target at any depth of the shared authored tree. -/
theorem checkedNumericComputationOperation_noTargetReference
    (checked : CheckedNumericComputationOperation model) :
    checked.core.expression.anyAtom
      (NumericComputationAtom.references checked.core.target.id) = false := by
  have admitted := checked.wellFormed
  simp only [NumericComputationOperation.WellFormed,
    NumericComputationOperation.wellFormedBool, Bool.and_eq_true] at admitted
  simpa using admitted.1.1.1.2

/-- Every checked computation operation lies in the shared plain-arithmetic or direct root value-function fragment. -/
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
      NumericComputationAtom.numericScaleSummary = some summary) :
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
    (read : FlatFieldDecl →
      Except NumericComputationFault NumericComputationResult)
    (mode : DecimalRoundingMode) (places : RoundingPlaces)
    (body : LoweredNumericExpr FlatFieldDecl)
    (_admitted :
      (LoweredNumericExpr.round mode places body).computationFault? = none)
    (failed : body.evalComputation read = .ok .domainFailure) :
    (LoweredNumericExpr.round mode places body).evalComputation read =
      .ok .domainFailure := by
  simp only [LoweredNumericExpr.evalComputation]
  rw [failed]
  rfl

/-- Absolute value delegates every evaluated child result to the shared value-only transformation. -/
theorem numericComputation_abs_delegates
    (read : FlatFieldDecl →
      Except NumericComputationFault NumericComputationResult)
    (body : LoweredNumericExpr FlatFieldDecl)
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
