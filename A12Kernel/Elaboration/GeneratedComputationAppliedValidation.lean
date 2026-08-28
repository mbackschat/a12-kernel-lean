import A12Kernel.Elaboration.GeneratedComputationFormalInput
import A12Kernel.Elaboration.NumericComputation.RunApplication

/-! # Generated computation application followed by validation

This bounded composition executes one generated Number table against an immutable source, applies its source-relative actions to a same-model destination, and evaluates the complete generated validation twin over that applied destination. The target remains nonrepeatable, while the checked numeric expression may consume either scalar inputs or its established repeatable-source context. Scheduling, document reconstruction, repeatable targets, and general later-rule orchestration remain separate.
-/

namespace A12Kernel

namespace GeneratedComputationTable

/-- Failure while keeping generated-table admission, execution, application, and later validation as distinct observable phases. -/
inductive AppliedValidationError where
  | admission (cause : GeneratedComputationValidationError)
  | execution (cause : GeneratedNumericComputationRunResultError)
  | application (cause : NumericComputationDocumentApplicationError)
  | validation (cause : CheckedAddressingError)
  deriving Repr

/-- The complete bounded scalar-target result of executing one generated Number table, applying its retained source-relative actions, and explicitly evaluating its generated validation twin over that applied destination. -/
structure AppliedValidationView (model : FlatModel) (Payload : Type) where
  result : NumericComputationRunView
    (ComputationFormalMessage Payload) CellAddr
  applied : NumericComputationApplicationProjection model
  validation : FlatRuleOutcome

/-- Failure while extending selected formal-input preparation through generated execution, application, and later validation. Findings become available only after preparation succeeds and remain attached to every subsequent failure phase. -/
inductive FormalInputAppliedValidationError where
  | admission (cause : GeneratedComputationValidationError)
  | formalInput (cause : ComputationFormalInputPlanError)
  | preliminary (cause : CheckedIndexPreliminaryError)
  | execution (formalErrorsInOperands : List ComputationFormalInputFinding)
      (cause : GeneratedNumericComputationRunResultError)
  | application (formalErrorsInOperands : List ComputationFormalInputFinding)
      (cause : NumericComputationDocumentApplicationError)
  | validation (formalErrorsInOperands : List ComputationFormalInputFinding)
      (cause : CheckedAddressingError)
  deriving Repr

/-- The complete prepared-input result of executing one generated Number table, applying its retained source-relative actions, and explicitly evaluating its generated validation twin over that applied destination. -/
structure FormalInputAppliedValidationView (model : FlatModel) where
  result : NumericComputationFormalInputRunView model CellAddr
  applied : NumericComputationApplicationProjection model
  validation : FlatRuleOutcome

private inductive AppliedValidationContinuationError where
  | application (cause : NumericComputationDocumentApplicationError)
  | validation (cause : CheckedAddressingError)

private def continueNumericAppliedValidation
    (admission : AdmittedGeneratedNumericOperationTable model computation)
    (validationWorld : World)
    (result : NumericComputationRunView
      (ComputationFormalMessage Payload) CellAddr)
    (destination : CheckedDocument model) :
    Except AppliedValidationContinuationError
      (NumericComputationApplicationProjection model × FlatRuleOutcome) := do
  let applied ← result.applyToChecked destination |>.mapError .application
  let appliedFields : FlatContext := {
    read := fun field =>
      match result.validationCellAfterApplication destination [] field with
      | .ok cell => cell
      | .error _ => malformedCheckedCell
    world := some validationWorld
  }
  let context : AddressedValidationEvaluationContext model := {
    scalar := {
      fields := appliedFields
      groups := GroupPresenceContext.unavailable
    }
    outer := []
    input := .partialView destination fun environment field =>
      (result.validationCellAfterApplication destination environment field)
        |>.map some
  }
  let validation ←
    admission.rule.evalAddressedFull context true |>.mapError .validation
  pure (applied, validation)

/-- Execute one admitted scalar-target generated Number table against an immutable source, apply its retained actions to a compatible destination, then evaluate the complete generated validation twin against the applied destination under an independently supplied later world. -/
def executeNumericAppliedValidation (computation : GeneratedComputationTable
    (CheckedNumericComputationOperation model))
    (executionWorld validationWorld : World)
    (source destination : CheckedDocument model)
    (payloadAt : CellAddr → Payload)
    (supplied : List (ComputationFormalMessage Payload)) :
    Except AppliedValidationError (AppliedValidationView model Payload) := do
  let admission ←
    (admitGeneratedNumericOperationTable model computation)
      |>.mapError .admission
  let result ←
    (admission.executeAddressedResultWithRead executionWorld source source.read
      payloadAt supplied)
      |>.mapError .execution
  let continuation ←
    (continueNumericAppliedValidation admission validationWorld result destination)
      |>.mapError fun
        | .application cause => .application cause
        | .validation cause => .validation cause
  pure {
    result
    applied := continuation.1
    validation := continuation.2
  }

/-- Prepare one generated Number table's complete selected input inventory, execute only its selected operation through that exact view, apply the retained source-relative actions to a compatible destination, then evaluate the generated validation twin against the applied destination under an independently supplied later world. -/
def executeNumericFormalInputAppliedValidation
    (computation : GeneratedComputationTable
      (CheckedNumericComputationOperation model))
    (executionWorld validationWorld : World)
    (source destination : CheckedDocument model) :
    Except FormalInputAppliedValidationError
      (FormalInputAppliedValidationView model) := do
  let admission ←
    (admitGeneratedNumericOperationTable model computation)
      |>.mapError .admission
  let inputPlan ← admission.formalInputPlan |>.mapError .formalInput
  let prepared ← inputPlan.prepare source |>.mapError .preliminary
  let numeric ←
    (admission.executeAddressedResultWithRead executionWorld source
      prepared.preliminary.readComputation (fun _ => ()) [])
      |>.mapError (.execution prepared.formalErrorsInOperands)
  let continuation ←
    (continueNumericAppliedValidation admission validationWorld numeric destination)
      |>.mapError fun
        | .application cause =>
            .application prepared.formalErrorsInOperands cause
        | .validation cause =>
            .validation prepared.formalErrorsInOperands cause
  pure {
    result := NumericComputationFormalInputRunView.of numeric
      prepared.formalErrorsInOperands
    applied := continuation.1
    validation := continuation.2
  }

end GeneratedComputationTable

end A12Kernel
