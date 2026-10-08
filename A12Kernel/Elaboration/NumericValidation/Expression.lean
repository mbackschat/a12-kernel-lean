import A12Kernel.Elaboration.NumericValidation.ScalarResolution

/-! # Standalone checked numeric-expression evaluation

Temporal amounts and ordinary comparisons share numeric arithmetic without importing addressed
entity-list comparison assembly. This keeps recursive temporal consumers below that assembly.
-/

namespace A12Kernel

/-- Evaluate a checked standalone operation through the shared one-pass lowering and arithmetic engine. The caller selects the already-checked atom observation policy. -/
def CheckedNumericValidationExpression.evalWith
    (checked : CheckedNumericValidationExpression model)
    (read : NumericValidationAtom →
      Except NumericValidationUnavailable NumericArithmeticOutcome) :
    Except NumericValidationUnavailable NumericArithmeticOutcome :=
  checked.core.lowerForEvaluation.evalNumericOperationTree read

/-- Resolve one direct Number field at its model-owned scalar or repeatable scope in the requested phase. A partial view may suppress the field without fabricating a formal cause; structural addressing failure remains outside numeric unavailability. -/
def AddressedValidationEvaluationContext.resolveDirectNumberAt
    (context : AddressedValidationEvaluationContext model)
    (phase : Phase) (source : FlatNumberField) :
    Except CheckedAddressingError
      (Except NumericValidationUnavailable NumericArithmeticOutcome) := do
  match model.lookupUniqueId source.id with
  | .error _ => pure (.error (.formal .malformed))
  | .ok declaration =>
      let needsAddressedRead :=
        match context.input with
        | .partialView _ _ => true
        | .legacy _ _ | .checked _ =>
            !declaration.repeatableScope.isEmpty
      if !needsAddressedRead then
        pure ((context.scalar.fields.resolveNumberComparisonOperandAt phase source)
          |>.toValidationArithmetic)
      else
        match ← context.readPartialCell context.outer source.id with
        | none => pure (.error .silentlyUnavailable)
        | some cell =>
            pure ((observeCell phase cell).asDirectNumericComparisonOperand source.info
              |>.toValidationArithmetic)

/-- Resolve every direct Number field in one checked expression against an addressed row context in the requested phase, then apply the shared one-pass arithmetic evaluator. The fallback is unreachable through the temporal direct-field certificate. -/
def CheckedNumericValidationExpression.evalAddressedDirectNumbersAt
    (checked : CheckedNumericValidationExpression model)
    (phase : Phase)
    (context : AddressedValidationEvaluationContext model) :
    Except CheckedAddressingError
      (Except NumericValidationUnavailable NumericArithmeticOutcome) := do
  let resolved ← checked.core.mapM fun
    | .field source => context.resolveDirectNumberAt phase source
    | _ => pure (.error .groupState)
  pure (resolved.lowerForEvaluation.evalNumericOperationTree id)

end A12Kernel
