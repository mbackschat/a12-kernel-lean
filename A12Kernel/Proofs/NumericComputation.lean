import A12Kernel.Elaboration.NumericComputation
import A12Kernel.Proofs.Observation

/-! # Numeric computation-expression laws -/

namespace A12Kernel

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
    LoweredNumericExpr.evalComputation,
    NumericComputationResult.evalBinary,
    NumericScaleBinaryOp.evalValues, divideNumeric]
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

/-- A poison reached in the left operand fixes the result without consulting the right subtree. -/
theorem numericComputation_leftPoison_shortCircuits
    (read : FlatFieldDecl →
      Except NumericComputationFault NumericComputationResult)
    (op : NumericScaleBinaryOp)
    (left right : LoweredNumericExpr FlatFieldDecl)
    (cause : FormalCause)
    (_admitted :
      (LoweredNumericExpr.binary op left right).computationFault? = none)
    (poisoned : left.evalComputation read = .ok (.poison cause)) :
    (LoweredNumericExpr.binary op left right).evalComputation read =
      .ok (.poison cause) := by
  simp only [LoweredNumericExpr.evalComputation]
  rw [poisoned]
  rfl

/-- A domain-failed left value does not hide a poison reached while evaluating the right operand. -/
theorem numericComputation_rightPoison_after_leftDomain
    (read : FlatFieldDecl →
      Except NumericComputationFault NumericComputationResult)
    (op : NumericScaleBinaryOp)
    (left right : LoweredNumericExpr FlatFieldDecl)
    (cause : FormalCause)
    (_admitted :
      (LoweredNumericExpr.binary op left right).computationFault? = none)
    (leftFailed : left.evalComputation read = .ok .domainFailure)
    (rightPoisoned : right.evalComputation read = .ok (.poison cause)) :
    (LoweredNumericExpr.binary op left right).evalComputation read =
      .ok (.poison cause) := by
  simp only [LoweredNumericExpr.evalComputation]
  rw [leftFailed, rightPoisoned]
  rfl

/-- A clean right value cannot recover a domain-failed left arithmetic subtree. -/
theorem numericComputation_leftDomain_absorbs_value
    (read : FlatFieldDecl →
      Except NumericComputationFault NumericComputationResult)
    (op : NumericScaleBinaryOp)
    (left right : LoweredNumericExpr FlatFieldDecl)
    (rightValue : Rat)
    (_admitted :
      (LoweredNumericExpr.binary op left right).computationFault? = none)
    (leftFailed : left.evalComputation read = .ok .domainFailure)
    (rightEvaluated : right.evalComputation read = .ok (.value rightValue)) :
    (LoweredNumericExpr.binary op left right).evalComputation read =
      .ok .domainFailure := by
  simp only [LoweredNumericExpr.evalComputation]
  rw [leftFailed, rightEvaluated]
  rfl

/-- A clean left value cannot recover a domain-failed right arithmetic subtree. -/
theorem numericComputation_rightDomain_absorbs_value
    (read : FlatFieldDecl →
      Except NumericComputationFault NumericComputationResult)
    (op : NumericScaleBinaryOp)
    (left right : LoweredNumericExpr FlatFieldDecl)
    (leftValue : Rat)
    (_admitted :
      (LoweredNumericExpr.binary op left right).computationFault? = none)
    (leftEvaluated : left.evalComputation read = .ok (.value leftValue))
    (rightFailed : right.evalComputation read = .ok .domainFailure) :
    (LoweredNumericExpr.binary op left right).evalComputation read =
      .ok .domainFailure := by
  simp only [LoweredNumericExpr.evalComputation]
  rw [leftEvaluated, rightFailed]
  rfl

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
