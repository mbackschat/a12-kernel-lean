import A12Kernel.Conformance.GeneratedComputationValidation.Support.Core

/-! # Generated-computation validation repeatable support -/

namespace A12Kernel.Conformance.GeneratedComputationValidation.Support.Repeatable

open A12Kernel
open A12Kernel.Conformance.GeneratedComputationValidation.Support.Core

inductive PartialCompileDecision where
  | emitHavingSkip
  | evaluate
  deriving Repr, DecidableEq

/-- Same-context Transform/Compile probe: the consumer asks the checked whole rule whether Kernel 30.8.1 partial validation must return before relevance and execution. It does not inspect a reached branch or reconstruct the computation source. -/
def partialCompileDecision
    (rule : CheckedResolvedValidationRule checkedModel) :
    PartialCompileDecision :=
  if rule.hasHaving then .emitHavingSkip else .evaluate

def repeatablePartialCompileDecision
    (operationResult : Except NumericComputationElabError
      (CheckedNumericComputationOperation repeatableModel))
    (errorCode : String) : Option PartialCompileDecision := do
  let rule ← repeatableGeneratedRule? operationResult errorCode
  pure (partialCompileDecision rule)

def hasAddressedScalarRejection
    (capability :
      Option (Bool × Except ValidationEvaluationError FlatRuleOutcome)) : Bool :=
  match capability with
  | some (true, .error .addressedContextRequired) => true
  | _ => false

def hasScalarOutcome
    (capability :
      Option (Bool × Except ValidationEvaluationError FlatRuleOutcome))
    (expected : FlatRuleOutcome) : Bool :=
  match capability with
  | some (false, .ok actual) => decide (actual = expected)
  | _ => false

def repeatableFirstFilledReferences :
    Option (Bool × Bool × Bool × NumericOperandScope) := do
  let operation ← repeatableFirstFilledOperation.toOption
  let comparison ← (operation.generatedMismatchComparison none).toOption
  pure (
    comparison.core.referencesField target.id,
    comparison.core.referencesField repeatedTarget.id,
    comparison.core.referencesField repeatedGate.id &&
      comparison.core.referencesField gate.id,
    comparison.operandScope)

def repeatableAggregateReferences :
    Option (Bool × Bool × NumericOperandScope) := do
  let operation ← repeatableAggregateOperation.toOption
  let comparison ← (operation.generatedMismatchComparison none).toOption
  pure (
    comparison.core.referencesField target.id,
    comparison.core.referencesField repeatedGate.id,
    comparison.operandScope)

def repeatableValueCountReferences :
    Option (Bool × Bool × Bool × NumericOperandScope) := do
  let operation ← repeatableValueCountOperation.toOption
  let comparison ← (operation.generatedMismatchComparison none).toOption
  pure (
    comparison.core.referencesField target.id,
    comparison.core.referencesField repeatedTarget.id,
    comparison.core.referencesField repeatedGate.id &&
      comparison.core.referencesField gate.id,
    comparison.operandScope)

def repeatableTokenValueCountReferences :
    Option (Bool × Bool × Bool × NumericOperandScope) := do
  let operation ← repeatableTokenValueCountOperation.toOption
  let comparison ← (operation.generatedMismatchComparison none).toOption
  pure (
    comparison.core.referencesField target.id,
    comparison.core.referencesField repeatedCode.id,
    comparison.core.referencesField repeatedGate.id &&
      comparison.core.referencesField gate.id,
    comparison.operandScope)

def productAggregateReferences :
    Option (Bool × Bool × Bool × NumericOperandScope) := do
  let operation ← productAggregateOperation.toOption
  let comparison ← (operation.generatedMismatchComparison none).toOption
  pure (
    comparison.core.referencesField target.id,
    comparison.core.referencesField repeatedGate.id,
    comparison.core.referencesField repeatedTarget.id,
    comparison.operandScope)

def repeatableGeneratedAddressedOutcome
    (operationResult : Except NumericComputationElabError
      (CheckedNumericComputationOperation repeatableModel))
    (errorCode : String)
    (document : Document) (outerGate targetCell : RawCell)
    (filterRows targetRows : RowIndex → CheckedCell) :
    Option (Except CheckedAddressingError FlatRuleOutcome) := do
  let rule ← repeatableGeneratedRule? operationResult errorCode
  let prepared ←
    (prepareFlatStringContext evaluationWorld builtinStringPatternCompiler
      repeatableModel).toOption
  let fields :=
    (prepared.checkContext "en_US" (repeatableRaw outerGate targetCell)).withWorld
      prepared.world
  pure (rule.evalAddressedFull {
    scalar := {
      fields
      groups := GroupPresenceContext.unavailable }
    outer := []
    input := .legacy document
      (repeatableRead (fields.read gate.id) filterRows targetRows)
  } true)

def repeatableFirstFilledAddressedOutcome
    (document : Document) (outerGate targetCell : RawCell)
    (filterRows targetRows : RowIndex → CheckedCell) :
    Option (Except CheckedAddressingError FlatRuleOutcome) :=
  repeatableGeneratedAddressedOutcome repeatableFirstFilledOperation
    "computedRepeatableFirstFilled" document outerGate targetCell
    filterRows targetRows

def repeatableAggregateAddressedOutcome
    (document : Document) (targetCell : RawCell)
    (sourceRows : RowIndex → CheckedCell) :
    Option (Except CheckedAddressingError FlatRuleOutcome) :=
  repeatableGeneratedAddressedOutcome repeatableAggregateOperation
    "computedRepeatableAggregate" document .empty targetCell
    sourceRows (fun _ => checkedNumber .empty)

def repeatableValueCountAddressedOutcome
    (document : Document) (targetCell : RawCell)
    (filterRows targetRows : RowIndex → CheckedCell) :
    Option (Except CheckedAddressingError FlatRuleOutcome) :=
  repeatableGeneratedAddressedOutcome repeatableValueCountOperation
    "computedRepeatableValueCount" document (.parsed (.num 1)) targetCell
    filterRows targetRows

def repeatableTokenValueCountAddressedOutcome
    (document : Document) (targetCell : RawCell)
    (filterRows targetRows : RowIndex → CheckedCell) :
    Option (Except CheckedAddressingError FlatRuleOutcome) :=
  repeatableGeneratedAddressedOutcome repeatableTokenValueCountOperation
    "computedRepeatableTokenValueCount" document (.parsed (.num 1)) targetCell
    filterRows targetRows

def productAggregateAddressedOutcome
    (document : Document) (targetCell : RawCell)
    (leftRows rightRows : RowIndex → CheckedCell) :
    Option (Except CheckedAddressingError FlatRuleOutcome) :=
  repeatableGeneratedAddressedOutcome productAggregateOperation
    "computedProductAggregate" document .empty targetCell leftRows rightRows

def repeatableExpectedMessage
    (errorCode : String) (messageType : Polarity) : FlatRuleMessage :=
  { errorAddress := { field := target.id, path := [] }
    errorCode
    severity := .error
    messageType
    text }

def repeatableFirstFilledExpectedMessage : FlatRuleMessage :=
  repeatableExpectedMessage "computedRepeatableFirstFilled" .omission

def repeatableAggregateExpectedMessage : FlatRuleMessage :=
  repeatableExpectedMessage "computedRepeatableAggregate" .omission

def productAggregateExpectedMessage : FlatRuleMessage :=
  repeatableExpectedMessage "computedProductAggregate" .omission

def hasAddressedOutcome
    (result : Option (Except CheckedAddressingError FlatRuleOutcome))
    (expected : FlatRuleOutcome) : Bool :=
  match result with
  | some (.ok actual) => decide (actual = expected)
  | _ => false

def hasAddressingError
    (result : Option (Except CheckedAddressingError FlatRuleOutcome))
    (expected : StarAddressingError) : Bool :=
  match result with
  | some (.error (.addressing actual)) => decide (actual = expected)
  | _ => false

def evalFlatRule? (checkedModel : FlatModel)
    (rule : CheckedResolvedFlatRule checkedModel) (raw : RawFlatContext)
    (hasContent : Bool) : Option FlatRuleOutcome := do
  let prepared ←
    (prepareFlatStringContext evaluationWorld builtinStringPatternCompiler
      checkedModel).toOption
  pure (rule.evalFull prepared "en_US" raw hasContent)

def evalValidationRule? (checkedModel : FlatModel)
    (rule : CheckedResolvedValidationRule checkedModel)
    (raw : RawFlatContext) (groups : GroupPresenceContext)
    (hasContent : Bool) : Option FlatRuleOutcome := do
  let prepared ←
    (prepareFlatStringContext evaluationWorld builtinStringPatternCompiler
      checkedModel).toOption
  (rule.evalFull prepared "en_US" raw groups hasContent).toOption

def selectionOf (candidate : LiteralNumberComputation)
    (raw : RawFlatContext) :
    ComputationAlternativeSelection DecodedNumericLiteral :=
  GeneratedComputationTable.selectFirst candidate
    { read := (model.checkContext raw).read }

def outcomeOf (candidate : LiteralNumberComputation)
    (raw : RawFlatContext) : Option FlatRuleOutcome :=
  match assembleGeneratedLiteralNumberRule model candidate with
  | .error _ => none
  | .ok rule => evalFlatRule? model rule raw true

def assemblyErrorIn (checkedModel : FlatModel)
    (candidate : LiteralNumberComputation) :
    Option GeneratedComputationValidationError :=
  match assembleGeneratedLiteralNumberRule checkedModel candidate with
  | .ok _ => none
  | .error error => some error

def assemblyErrorOf :=
  assemblyErrorIn model

def generatedRowGroupOf (candidate : LiteralNumberComputation) :
    Option GroupPath :=
  match assembleGeneratedLiteralNumberRule model candidate with
  | .ok rule => some rule.condition.rowGroup
  | .error _ => none

def expectedMessage (messageType : Polarity) : FlatRuleMessage :=
  { errorAddress := { field := target.id, path := [] }
    errorCode := "computedTarget"
    severity := .error
    messageType
    text }


end A12Kernel.Conformance.GeneratedComputationValidation.Support.Repeatable
