import A12Kernel.Elaboration.AddressedNumberFirstFilledComputation
import A12Kernel.Elaboration.GeneratedComputationValidation

/-! # Repeatable Number first-filled application followed by generated validation

This bounded composition executes one unconditional addressed Number `FirstFilledValue`, applies its source-relative actions to a same-model destination, and evaluates the generated mismatch at every destination target row. It reuses the checked repeatable rule and ordered numeric comparison owners. The existing-topology route rejects action-created rows; the exact two-level continuation delegates their normalization to the shared materialized topology owner. Guarded alternatives, tolerances, other operations, deeper target scopes, and general later-rule orchestration remain separate.
-/

namespace A12Kernel

inductive AddressedNumberFirstFilledGeneratedRuleError where
  | condition (cause : ValidationConditionAssemblyError)
  | rule (cause : FlatRuleAssemblyError)
  deriving Repr, DecidableEq

inductive AddressedNumberFirstFilledAppliedValidationError where
  | rule (cause : AddressedNumberFirstFilledGeneratedRuleError)
  | execution (cause : AddressedNumberFirstFilledComputationFault)
  | application (cause : NumericComputationDocumentApplicationError)
  | materializedTopology (address : CellAddr)
  | validation (cause : OrdinaryRepeatableRuleEvaluationError)
  deriving Repr, DecidableEq

inductive AddressedNumberFirstFilledMaterializedAppliedValidationError where
  | rule (cause : AddressedNumberFirstFilledGeneratedRuleError)
  | execution (cause : AddressedNumberFirstFilledComputationFault)
  | targetScope (scope : List RepeatableLevel)
  | application (cause : NumericComputationDocumentApplicationError)
  | validation (cause : OrdinaryRepeatableRuleEvaluationError)
  deriving Repr, DecidableEq

/-- The exact repeatable-target phases retained by this bounded composition. -/
structure AddressedNumberFirstFilledAppliedValidationView
    (model : FlatModel) (Payload : Type) where
  result : AddressedNumberFirstFilledComputationRunView model Payload
  applied : NumericComputationApplicationProjection model
  validation : List (Env × FlatRuleOutcome)

/-- The exact two-level materialized-target phases retained by this bounded composition. -/
structure AddressedNumberFirstFilledMaterializedAppliedValidationView
    (model : FlatModel) (Payload : Type) where
  result : AddressedNumberFirstFilledComputationRunView model Payload
  applied : NumericComputationTwoLevelApplicationProjection model
  validation : List (Env × FlatRuleOutcome)

namespace CheckedAddressedNumberFirstFilledComputation

/-- The validation-side Number identity reconstructed from the operation's exact checked target and declaration-owned policy. -/
def generatedValidationTarget
    (operation : CheckedAddressedNumberFirstFilledComputation model) :
    FlatNumberField := {
  id := operation.targetField
  info := operation.target.targetPolicy.info
}

/-- The strict generated mismatch retains the exact checked repeatable source and places the computed target on the stored-value side. -/
def generatedMismatchComparison
    (operation : CheckedAddressedNumberFirstFilledComputation model) :
    OrderedNumericComparison model := {
  op := .ordinary .notEqual
  left := .atom (.ordinary (.field operation.generatedValidationTarget))
  right := .atom (.firstFilled operation.numberSource)
}

/-- Assemble the canonical filled-target gate and strict mismatch for one already-checked unconditional addressed operation. The operation's own target and source certificates discharge the mixed-condition admission rather than reconstructing surface syntax. -/
def generatedValidationRule
    (operation : CheckedAddressedNumberFirstFilledComputation model)
    (errorCode : String) (messagePlan : MessageRenderPlan) :
    Except AddressedNumberFirstFilledGeneratedRuleError
      (CheckedResolvedValidationRule model) := do
  let core := generatedConditionWithGate
    (ValidationCondition.repeatableFieldPresence
      .filled operation.targetDeclaration)
    none
    (ValidationCondition.orderedNumericIn
      .sameGroupAddressed operation.generatedMismatchComparison)
  let condition ←
    (CheckedValidationCondition.checkCore model operation.declaringGroup
      core operation.target.modelWellFormed).mapError .condition
  (assembleResolvedValidationRule model condition operation.targetField
    errorCode .error messagePlan).mapError .rule

private def toOrdinaryRowEnvironmentError :
    ActualRowEnvironmentError → OrdinaryRepeatableRuleEvaluationError
  | .missingScope => .missingIterationScope
  | .unknownLevel level => .incoherentIterationScope [level]
  | .incoherentScope supplied _ => .incoherentIterationScope supplied
  | .incoherentRow row => .incoherentRow row

private def evaluateGeneratedAt
    (rule : CheckedResolvedValidationRule model)
    (result : NumericComputationRunView Message CellAddr)
    (destination : CheckedDocument model) (environment : Env) :
    Except OrdinaryRepeatableRuleEvaluationError
      (Env × FlatRuleOutcome) := do
  let errorPath ←
    (environment.pathForScope rule.errorDeclaration.repeatableScope)
      |>.mapError fun cause => .addressing (.environment cause)
  let context : AddressedValidationEvaluationContext model := {
    scalar := {
      fields := destination.flatContext
      groups := GroupPresenceContext.unavailable
    }
    outer := environment
    input := .partialView destination fun current field =>
      (result.validationCellAfterApplication destination current field).map some
  }
  let verdict ←
    (rule.condition.core.evalAddressedFull context true)
      |>.mapError .conditionAddressing
  pure (environment, rule.core.emitAt errorPath verdict)

private def evaluateGenerated
    (rule : CheckedResolvedValidationRule model)
    (result : NumericComputationRunView Message CellAddr)
    (destination : CheckedDocument model) :
    Except OrdinaryRepeatableRuleEvaluationError
      (List (Env × FlatRuleOutcome)) := do
  if !rule.condition.core.supportsOrdinaryIteration then
    throw .unsupportedCondition
  let scope ← match rule.iterationScope with
    | some scope => pure scope
    | none => throw .missingIterationScope
  let environments ←
    destination.validationRowEnvironments scope
      |>.mapError toOrdinaryRowEnvironmentError
  environments.mapM (evaluateGeneratedAt rule result destination)

private def evaluateGeneratedTwoLevelRows
    (rule : CheckedResolvedValidationRule model)
    (result : NumericComputationRunView Message CellAddr)
    (destination : CheckedDocument model)
    (outer inner : RepeatableLevel) (rows : List RowAddr) :
    Except OrdinaryRepeatableRuleEvaluationError
      (List (Env × FlatRuleOutcome)) :=
  rows.mapM fun row => match row.path with
    | [outerCoordinate, innerCoordinate] =>
        evaluateGeneratedAt rule result destination
          [(outer, outerCoordinate), (inner, innerCoordinate)]
    | _ => throw (.incoherentRow row)

private def createdActionTarget?
    (operation : CheckedAddressedNumberFirstFilledComputation model)
    (result : NumericComputationRunView Message CellAddr)
    (applied : NumericComputationApplicationProjection model) : Option CellAddr :=
  let actionTargets :=
    result.cleared ++ result.withChanges.map (·.targetField)
  actionTargets.find? fun address =>
    (repeatableAncestorRowsFor
      operation.targetDeclaration.repeatableScope address.path).any
        applied.createdRow

/-- Execute against the immutable source, apply source-relative actions to the destination, reject any action that would create destination topology, then recompute and emit the generated rule at every existing destination target row. -/
def executeGeneratedAppliedValidation
    (operation : CheckedAddressedNumberFirstFilledComputation model)
    (source destination : CheckedDocument model)
    (payloadAt : CellAddr → Payload)
    (supplied : List (ComputationFormalMessage Payload))
    (errorCode : String) (messagePlan : MessageRenderPlan) :
    Except AddressedNumberFirstFilledAppliedValidationError
      (AddressedNumberFirstFilledAppliedValidationView model Payload) := do
  let rule ←
    (operation.generatedValidationRule errorCode messagePlan).mapError .rule
  let result ←
    (operation.executeResult source payloadAt supplied).mapError .execution
  let applied ← result.applyToChecked destination |>.mapError .application
  match operation.createdActionTarget? result.numeric applied with
  | some address => throw (.materializedTopology address)
  | none =>
      let validation ←
        (evaluateGenerated rule result.numeric destination).mapError .validation
      pure { result, applied, validation }

/-- Execute against the immutable source, apply through the existing normalized two-level target topology, then recompute and emit the generated rule over every concrete materialized target leaf. -/
def executeGeneratedMaterializedAppliedValidation
    (operation : CheckedAddressedNumberFirstFilledComputation model)
    (source destination : CheckedDocument model)
    (payloadAt : CellAddr → Payload)
    (supplied : List (ComputationFormalMessage Payload))
    (errorCode : String) (messagePlan : MessageRenderPlan) :
    Except AddressedNumberFirstFilledMaterializedAppliedValidationError
      (AddressedNumberFirstFilledMaterializedAppliedValidationView
        model Payload) := do
  let (outer, inner) ← match operation.targetDeclaration.repeatableScope with
    | [outer, inner] => pure (outer, inner)
    | scope => throw (.targetScope scope)
  let rule ←
    (operation.generatedValidationRule errorCode messagePlan).mapError .rule
  let result ←
    (operation.executeResult source payloadAt supplied).mapError .execution
  let applied ←
    (result.numeric.applyToCheckedTwoLevel destination outer inner)
      |>.mapError .application
  let validation ←
    (evaluateGeneratedTwoLevelRows rule result.numeric destination outer inner
      applied.leafRows).mapError .validation
  pure { result, applied, validation }

end CheckedAddressedNumberFirstFilledComputation

end A12Kernel
