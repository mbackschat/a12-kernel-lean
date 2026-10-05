import A12Kernel.Elaboration.GeneratedComputationValidation.Assembly

/-! # Admitted generated computation execution

Generated-rule admission retains the target policy in Assembly. Runtime selection consumes that
certificate through the shared guard and numeric operation evaluators, then delegates target
completion and source-relative result projection to their existing owners.
-/

namespace A12Kernel

/-- Runtime phase boundary for an admitted generated numeric table. Activation no-match and guard poison remain distinct from the selected operation's numeric result so later target projection cannot confuse an unselected table with an evaluated failure. -/
inductive GeneratedNumericComputationEvaluation where
  | noMatch
  | guardPoison (cause : FormalCause)
  | evaluated (suppressExactScaleWarning : Bool)
      (result : NumericComputationResult) (bandedRounding : Option ComputationRoundingMode := none)
  deriving Repr, DecidableEq

namespace GeneratedNumericComputationEvaluation

/-- Complete one admitted generated-table activation through the selected operation's retained target-check mode. A caller must supply the policy certified from the table's own target declaration. -/
def completeNumericTarget (evaluation : GeneratedNumericComputationEvaluation)
    (policy : NumericTargetPolicy) : NumericTargetCheckResult :=
  match evaluation with
  | .noMatch => .supported .noValue
  | .guardPoison cause => .supported (.inheritedPoison cause)
  | .evaluated _ result (some mode) => policy.checkBanded mode result
  | .evaluated false result none => policy.check result
  | .evaluated true result none => policy.checkWithScaleWarningSuppressed result

end GeneratedNumericComputationEvaluation

/-- Failure while admitting or evaluating one generated numeric table. Static generated-table rejection stays separate from a selected operation's structural evaluation fault. -/
inductive GeneratedNumericComputationEvaluationError where
  | validation (cause : GeneratedComputationValidationError)
  | operation (cause : NumericComputationFault)
  deriving Repr

/-- One completed generated Number target paired with its exact immutable source placement. Unsupported target completion remains data at this phase so it cannot be confused with supported no-value or clearing before public-result projection. -/
structure GeneratedNumericComputationTargetResult where
  targetAddress : CellAddr
  targetCheck : NumericTargetCheckResult
  sourceState : NumericTargetState
  deriving Repr, DecidableEq

namespace GeneratedNumericComputationTargetResult

/-- Narrow a supported generated target result to the established source-relative Number result input. Unsupported completion remains an explicit structural refusal. -/
def toSourceOutcome (result : GeneratedNumericComputationTargetResult) :
    Except NumericTargetCheckFault
      (SourcedNumericTargetOutcome CellAddr) :=
  match result.targetCheck with
  | .supported outcome => .ok {
      targetField := result.targetAddress
      outcome
      source := result.sourceState
    }
  | .unsupported cause => .error cause

end GeneratedNumericComputationTargetResult

/-- Failure before a generated scalar target can enter the established public Number result. Evaluation and target-check refusal remain distinct phases. -/
inductive GeneratedNumericComputationRunResultError where
  | execution (cause : GeneratedNumericComputationEvaluationError)
  | targetCheck (cause : NumericTargetCheckFault)
  deriving Repr

namespace AdmittedGeneratedNumericOperationTable

/-- A selected operation cannot fall through after its result is observed. Scalar and addressed
entry points share this projection while supplying their exact source reader to selection. -/
def evaluateSelection
    (_admission : AdmittedGeneratedNumericOperationTable model computation)
    (selection : Except CheckedComputationConditionError
      (ComputationAlternativeSelection (CheckedNumericComputationOperation model × Option ComputationRoundingMode)))
    (evaluateOperation : CheckedNumericComputationOperation model →
      Except NumericComputationFault NumericComputationResult) :
    Except GeneratedNumericComputationEvaluationError
      GeneratedNumericComputationEvaluation := do
  match ← selection.mapError (fun error => .operation error.toNumericFault) with
  | .noMatch => pure .noMatch
  | .poison cause => pure (.guardPoison cause)
  | .selected (operation, rounding) =>
      evaluateOperation operation
        |>.map (fun result => .evaluated operation.core.suppressExactScaleWarning result rounding)
        |>.mapError .operation

/-- Preserve one first-selection decision while delegating the selected checked operation to a caller-supplied scalar or addressed evaluator. -/
def evaluateWith
    (admission : AdmittedGeneratedNumericOperationTable model computation)
    (context : ScalarComputationContext)
    (evaluateOperation : CheckedNumericComputationOperation model →
      Except NumericComputationFault NumericComputationResult) :
    Except GeneratedNumericComputationEvaluationError GeneratedNumericComputationEvaluation :=
  admission.evaluateSelection (CheckedComputationAlternative.selectFirstChecked computation.outputNumericAlternatives context) evaluateOperation

/-- Evaluate only the first selected operation of an already-admitted table through the scalar compatibility boundary. Target completion remains separate. -/
def evaluate (admission : AdmittedGeneratedNumericOperationTable model computation)
    (context : ScalarComputationContext) :
    Except GeneratedNumericComputationEvaluationError
      GeneratedNumericComputationEvaluation :=
  admission.evaluateWith context (fun operation => operation.evaluate context)

/-- Reuse the same first-selection decision while evaluating the selected operation against its complete direct/repeatable checked context. -/
def evaluateIn (admission : AdmittedGeneratedNumericOperationTable model computation)
    (context : NumericComputationEvaluationContext) :
    Except GeneratedNumericComputationEvaluationError
      GeneratedNumericComputationEvaluation :=
  admission.evaluateSelection (CheckedComputationAlternative.selectFirstCheckedIn computation.outputNumericAlternatives context)
    (fun operation => operation.evaluateIn context)

private def checkedReadAtWith
    (input : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (environment : Env) (field : FieldId) : CheckedCell :=
  match input.checkedCellWithRead read environment field with
  | .ok cell => cell
  | .error _ => malformedCheckedCell

private def addressedEvaluationContextWithRead
    (input : CheckedDocument model) (world : World)
    (read : CellAddr → Except CheckedDocumentError CheckedCell) :
    NumericComputationEvaluationContext := {
  scalar := { input.computationContextAt [] with
    read := checkedReadAtWith input read []
    world := some world
  }
  document := input.source.toDocument
  outer := []
  filterRead := checkedReadAtWith input read
  starRead := checkedReadAtWith input read
  indexColumn? := some (input.resolveSemanticIndexColumnWith read)
}

/-- Evaluate one admitted scalar-target table through a caller-supplied exact-address source view. Guards and operations consume the same source view through their checked addressed evaluators, and target placement remains immutable source state. -/
def executeAddressedTargetResultWithRead
    (admission : AdmittedGeneratedNumericOperationTable model computation)
    (world : World) (input : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell) :
    Except GeneratedNumericComputationEvaluationError
      GeneratedNumericComputationTargetResult := do
  let evaluation ← admission.evaluateIn
    (addressedEvaluationContextWithRead input world read)
  let targetAddress : CellAddr := {
    field := computation.targetField
    path := []
  }
  pure {
    targetAddress
    targetCheck := evaluation.completeNumericTarget admission.targetPolicy
    sourceState := input.numericTargetPlacementStateAt targetAddress
  }

/-- Evaluate from one immutable checked document, complete through the admitted declaration policy, and retain the source target state used by later source-relative classification. -/
def executeTargetResult
    (admission : AdmittedGeneratedNumericOperationTable model computation)
    (world : World) (input : CheckedDocument model) :
    Except GeneratedNumericComputationEvaluationError
      GeneratedNumericComputationTargetResult := do
  let evaluation ← admission.evaluate (input.scalarComputationContext world)
  let targetAddress : CellAddr := {
    field := computation.targetField
    path := []
  }
  pure {
    targetAddress
    targetCheck := evaluation.completeNumericTarget admission.targetPolicy
    sourceState := input.numericTargetPlacementStateAt targetAddress
  }

/-- Project one supported checked target result through the established source-relative Number result owner. Target-check refusal stays structural and message association remains caller-supplied at this phase. -/
def executeResult
    (admission : AdmittedGeneratedNumericOperationTable model computation)
    (world : World) (input : CheckedDocument model)
    (payloadAt : CellAddr → Payload)
    (supplied : List (ComputationFormalMessage Payload)) :
    Except GeneratedNumericComputationRunResultError
      (NumericComputationRunView
        (ComputationFormalMessage Payload) CellAddr) := do
  let completed ←
    (admission.executeTargetResult world input).mapError .execution
  let sourced ← completed.toSourceOutcome |>.mapError .targetCheck
  pure (NumericComputationRunView.fromSourceOutcomesWithMessages
    MessagePointer.ofCellAddr payloadAt supplied [sourced])

/-- Project caller-read addressed execution through the established source-relative Number result without moving eager input findings into the typed message channel. -/
def executeAddressedResultWithRead
    (admission : AdmittedGeneratedNumericOperationTable model computation)
    (world : World) (input : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (payloadAt : CellAddr → Payload)
    (supplied : List (ComputationFormalMessage Payload)) :
    Except GeneratedNumericComputationRunResultError
      (NumericComputationRunView
        (ComputationFormalMessage Payload) CellAddr) := do
  let completed ←
    (admission.executeAddressedTargetResultWithRead world input read)
      |>.mapError .execution
  let sourced ← completed.toSourceOutcome |>.mapError .targetCheck
  pure (NumericComputationRunView.fromSourceOutcomesWithMessages
    MessagePointer.ofCellAddr payloadAt supplied [sourced])

end AdmittedGeneratedNumericOperationTable

namespace GeneratedComputationTable

/-- Admit the complete generated table, select through its common/row guard structure, then evaluate only the first selected checked numeric operation. Storage, application, and later generated validation stay in their later phases. -/
def evaluateNumeric (computation : GeneratedComputationTable
    (CheckedNumericComputationOperation model) (CheckedComputationCondition model))
    (context : ScalarComputationContext) :
    Except GeneratedNumericComputationEvaluationError
      GeneratedNumericComputationEvaluation :=
  match admitGeneratedNumericOperationTable model computation context.world with
  | .error cause => .error (.validation cause)
  | .ok admission => admission.evaluate context

/-- Evaluate the admitted generated table and complete its activation through the exact target policy reconstructed from that table's validated model declaration. -/
def evaluateNumericTarget (computation : GeneratedComputationTable
    (CheckedNumericComputationOperation model) (CheckedComputationCondition model))
    (context : ScalarComputationContext) :
    Except GeneratedNumericComputationEvaluationError NumericTargetCheckResult :=
  match admitGeneratedNumericOperationTable model computation context.world with
  | .error cause => .error (.validation cause)
  | .ok admission =>
      (admission.evaluate context).map
        (·.completeNumericTarget admission.targetPolicy)

/-- Admit and execute one scalar generated Number table from an immutable checked document, retaining its exact target check and source placement before public-result classification. -/
def executeNumericTargetResult (computation : GeneratedComputationTable
    (CheckedNumericComputationOperation model) (CheckedComputationCondition model))
    (world : World) (input : CheckedDocument model) :
    Except GeneratedNumericComputationEvaluationError
      GeneratedNumericComputationTargetResult :=
  match admitGeneratedNumericOperationTable model computation (some world) with
  | .error cause => .error (.validation cause)
  | .ok admission => admission.executeTargetResult world input

/-- Admit and execute one scalar generated Number table, then project its supported target result into the established source-relative public result. The returned view applies through `NumericComputationRunView.applyToChecked` without any generated-specific transition. -/
def executeNumericResult (computation : GeneratedComputationTable
    (CheckedNumericComputationOperation model) (CheckedComputationCondition model))
    (world : World) (input : CheckedDocument model)
    (payloadAt : CellAddr → Payload)
    (supplied : List (ComputationFormalMessage Payload)) :
    Except GeneratedNumericComputationRunResultError
      (NumericComputationRunView
        (ComputationFormalMessage Payload) CellAddr) :=
  match admitGeneratedNumericOperationTable model computation (some world) with
  | .error cause => .error (.execution (.validation cause))
  | .ok admission => admission.executeResult world input payloadAt supplied

end GeneratedComputationTable

end A12Kernel
