import A12Kernel.Elaboration.GeneratedComputationValidation
import A12Kernel.Elaboration.NumericComputation.RunApplication

/-! # Generated computation application followed by validation

This bounded composition executes one generated Number table against an immutable source, applies its source-relative actions to a same-model destination, and evaluates the complete generated validation twin over that applied destination. The target remains nonrepeatable, while the checked numeric expression may consume either scalar inputs or its established repeatable-source context. Scheduling, document reconstruction, repeatable targets, and general later-rule orchestration remain separate.
-/

namespace A12Kernel

namespace AdmittedGeneratedNumericOperationTable

private def checkedReadAt (input : CheckedDocument model)
    (environment : Env) (field : FieldId) : CheckedCell :=
  match input.checkedCellWithRead input.read environment field with
  | .ok cell => cell
  | .error _ => malformedCheckedCell

private def evaluationContext
    (input : CheckedDocument model) (world : World) :
    NumericComputationEvaluationContext := {
  scalar := input.scalarComputationContext world
  document := input.source.toDocument
  outer := []
  filterRead := checkedReadAt input
  starRead := checkedReadAt input
}

private def executeAddressedTargetResult
    (admission : AdmittedGeneratedNumericOperationTable model computation)
    (world : World) (input : CheckedDocument model) :
    Except GeneratedNumericComputationEvaluationError
      GeneratedNumericComputationTargetResult := do
  let evaluation ← admission.evaluateIn (evaluationContext input world)
  let targetAddress : CellAddr := {
    field := computation.targetField
    path := []
  }
  pure {
    targetAddress
    targetCheck := evaluation.completeNumericTarget admission.targetPolicy
    sourceState := input.numericTargetPlacementStateAt targetAddress
  }

private def executeAddressedResult
    (admission : AdmittedGeneratedNumericOperationTable model computation)
    (world : World) (input : CheckedDocument model)
    (payloadAt : CellAddr → Payload)
    (supplied : List (ComputationFormalMessage Payload)) :
    Except GeneratedNumericComputationRunResultError
      (NumericComputationRunView
        (ComputationFormalMessage Payload) CellAddr) := do
  let completed ←
    (admission.executeAddressedTargetResult world input).mapError .execution
  let sourced ← completed.toSourceOutcome |>.mapError .targetCheck
  pure (NumericComputationRunView.fromSourceOutcomesWithMessages
    MessagePointer.ofCellAddr payloadAt supplied [sourced])

end AdmittedGeneratedNumericOperationTable

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
    (admission.executeAddressedResult executionWorld source payloadAt supplied)
      |>.mapError .execution
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
  pure { result, applied, validation }

end GeneratedComputationTable

end A12Kernel
