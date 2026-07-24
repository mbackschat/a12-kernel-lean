import A12Kernel.Conformance.GeneratedComputationValidation.Support.Repeatable

/-! # Generated-computation validation cross-group support -/

namespace A12Kernel.Conformance.GeneratedComputationValidation.Support.CrossGroup

open A12Kernel
open A12Kernel.Conformance.GeneratedComputationValidation.Support.Core
open A12Kernel.Conformance.GeneratedComputationValidation.Support.Repeatable

def crossGroupRaw (source target : Rat) : RawFlatContext where
  read field :=
    if field = crossGroupSource.id then .parsed (.num source)
    else if field = crossGroupExtra.id then .parsed (.num 2)
    else if field = crossGroupTarget.id then .parsed (.num target)
    else .empty

def crossGroupScalarCapability :
    Option (Bool × Except ValidationEvaluationError FlatRuleOutcome) := do
  let operation ← crossGroupNumberOperation.toOption
  let rule ← (assembleGeneratedNumericOperationRule crossGroupModel operation
    "computedCrossGroup" none messagePlan).toOption
  let prepared ←
    (prepareFlatStringContext evaluationWorld builtinStringPatternCompiler
      crossGroupModel).toOption
  pure (
    rule.requiresAddressedValidation,
    rule.evalFull prepared "en_US" (crossGroupRaw 3 3)
      GroupPresenceContext.unavailable true)

def crossGroupOutcome (source target : Rat) : Option FlatRuleOutcome := do
  let operation ← crossGroupNumberOperation.toOption
  let rule ← (assembleGeneratedNumericOperationRule crossGroupModel operation
    "computedCrossGroup" none messagePlan).toOption
  evalValidationRule? crossGroupModel rule (crossGroupRaw source target)
    GroupPresenceContext.unavailable true

def crossGroupDatePartOutcome (target : Rat) : Option FlatRuleOutcome := do
  let operation ← crossGroupDatePartOperation.toOption
  let rule ← (assembleGeneratedNumericOperationRule crossGroupModel operation
    "computedDatePart" none messagePlan).toOption
  let raw : RawFlatContext := {
    read field :=
      if field = crossGroupDate.id then
        .parsed (.temporal (.date { epochMillis := 1719292867000 }
          { year := 2024, month := 6, day := 25 } .storedGregorian))
      else if field = crossGroupTarget.id then .parsed (.num target)
      else .empty }
  evalValidationRule? crossGroupModel rule raw
    GroupPresenceContext.unavailable true

def crossGroupDayDifferenceOutcome
    (target : Rat) : Option FlatRuleOutcome := do
  let operation ← crossGroupDayDifferenceOperation.toOption
  let rule ← (assembleGeneratedNumericOperationRule crossGroupModel operation
    "computedDayDifference" none messagePlan).toOption
  let instant :=
    (ModelZone.concreteResolveLocal? "Europe/Berlin" 2024 1 2 0 0 0).get
      (by native_decide)
  let raw : RawFlatContext := {
    read field :=
      if field = crossGroupDate.id then
        .parsed (.temporal (.date instant
          { year := 2024, month := 1, day := 2 } .storedGregorian))
      else if field = crossGroupTarget.id then .parsed (.num target)
      else .empty }
  evalValidationRule? crossGroupModel rule raw
    GroupPresenceContext.unavailable true

def crossGroupGeneratedBoundary :
    Option (GroupPath × NumericOperandScope) := do
  let operation ← crossGroupNumberOperation.toOption
  let comparison ← (operation.generatedMismatchComparison none).toOption
  pure (comparison.rowGroup, comparison.operandScope)

def crossGroupTokenCategoryCountReferences :
    Option (Bool × Bool × Bool × NumericOperandScope) := do
  let operation ← crossGroupTokenCategoryCountOperation.toOption
  let comparison ← (operation.generatedMismatchComparison none).toOption
  pure (
    comparison.core.referencesField crossGroupTarget.id,
    comparison.core.referencesField crossGroupNumericChoice.id,
    comparison.core.referencesField crossGroupCode.id,
    comparison.operandScope)

def crossGroupFirstFilledVerdict
    (source extra target : RawCell) (isRelevant : FlatRelevance) :
    Option Verdict := do
  let operation ← crossGroupFirstFilledOperation.toOption
  let comparison ← (operation.generatedMismatchComparison none).toOption
  let prepared ←
    (prepareFlatStringContext evaluationWorld builtinStringPatternCompiler
      crossGroupModel).toOption
  let raw : RawFlatContext := {
    read field :=
      if field = crossGroupSource.id then source
      else if field = crossGroupExtra.id then extra
      else if field = crossGroupTarget.id then target
      else .empty }
  pure (comparison.evalSelected {
    fields := prepared.checkContext "en_US" raw
    groups := GroupPresenceContext.unavailable } isRelevant)

def crossGroupOrdinaryError : Option NumericValidationElabError :=
  match elaborateNumericComparison crossGroupModel ["Output"] {
      op := .ordinary .notEqual
      left := .atom (.field (absolutePath ["Output"] "Target"))
      right := .atom (.field (absolutePath ["Input"] "Source")) } with
  | .ok _ => none
  | .error error => some error

def crossGroupExpectedMessage : FlatRuleMessage :=
  { errorAddress := { field := crossGroupTarget.id, path := [] }
    errorCode := "computedCrossGroup"
    severity := .error
    messageType := .value
    text }

def crossGroupDatePartExpectedMessage : FlatRuleMessage :=
  { errorAddress := { field := crossGroupTarget.id, path := [] }
    errorCode := "computedDatePart"
    severity := .error
    messageType := .value
    text }

def crossGroupDayDifferenceExpectedMessage : FlatRuleMessage :=
  { errorAddress := { field := crossGroupTarget.id, path := [] }
    errorCode := "computedDayDifference"
    severity := .error
    messageType := .value
    text }

def crossGroupExpressionTable
    (secondTolerance : Option NumericToleranceRange := none) :
    Option (GeneratedComputationTable
      (CheckedNumericComputationOperation crossGroupModel)) := do
  let first ← crossGroupNumberOperation.toOption
  let second ← crossGroupOffsetOperation.toOption
  pure {
    targetField := crossGroupTarget.id
    name := "computedExpressionTable"
    alternatives := .guarded {
      first := {
        precondition := .fieldFilled crossGroupSource.id
        operation := first }
      second := {
        precondition := .fieldFilled crossGroupSource.id
        operation := second
        tolerance := secondTolerance } }
    messagePlan }

def selectedCrossGroupExpression :
    Option (AuthoredNumericExpr
      (CheckedNumericComputationAtom crossGroupModel)) := do
  let table ← crossGroupExpressionTable
  match table.selectFirst {
      read := (crossGroupModel.checkContext (crossGroupRaw 3 3)).read } with
  | .selected operation => some operation.core.expression
  | .noMatch | .poison _ => none

def crossGroupExpressionTableOutcome
    (secondTolerance : Option NumericToleranceRange := none)
    (common : Option ComputationCondition := none) : Option FlatRuleOutcome := do
  let table ← crossGroupExpressionTable secondTolerance
  let rule ← (assembleGeneratedNumericOperationTableRule crossGroupModel
    { table with commonPrecondition := common }).toOption
  evalValidationRule? crossGroupModel rule (crossGroupRaw 3 3)
    GroupPresenceContext.unavailable true

def crossGroupExpressionSingletonOutcome
    (target : Rat) : Option FlatRuleOutcome := do
  let operation ← crossGroupNumberOperation.toOption
  let table : GeneratedComputationTable
      (CheckedNumericComputationOperation crossGroupModel) := {
    targetField := crossGroupTarget.id
    name := "computedExpressionTable"
    alternatives := .singleton { operation }
    messagePlan }
  let rule ← (assembleGeneratedNumericOperationTableRule crossGroupModel table).toOption
  evalValidationRule? crossGroupModel rule (crossGroupRaw 3 target)
    GroupPresenceContext.unavailable true

def crossGroupAggregateOutcome (target : Rat) : Option FlatRuleOutcome := do
  let operation ← crossGroupAggregateOperation.toOption
  let rule ← (assembleGeneratedNumericOperationRule crossGroupModel operation
    "computedAggregate" none messagePlan).toOption
  evalValidationRule? crossGroupModel rule (crossGroupRaw 3 target)
    GroupPresenceContext.unavailable true

def crossGroupAggregateTableOutcome (target : Rat) : Option FlatRuleOutcome := do
  let first ← crossGroupNumberOperation.toOption
  let second ← crossGroupAggregateOperation.toOption
  let table : GeneratedComputationTable
      (CheckedNumericComputationOperation crossGroupModel) := {
    targetField := crossGroupTarget.id
    name := "computedAggregate"
    alternatives := .guarded {
      first := {
        precondition := .fieldFilled crossGroupSource.id
        operation := first }
      second := {
        precondition := .fieldFilled crossGroupSource.id
        operation := second } }
    messagePlan }
  let rule ←
    (assembleGeneratedNumericOperationTableRule crossGroupModel table).toOption
  evalValidationRule? crossGroupModel rule (crossGroupRaw 3 target)
    GroupPresenceContext.unavailable true

def crossGroupStringRangeOutcome (target : Rat)
    (code : RawCell := .parsed (.str "12X")) : Option FlatRuleOutcome := do
  let operation ← crossGroupStringRangeOperation.toOption
  let rule ← (assembleGeneratedNumericOperationRule crossGroupModel operation
    "computedRange" none messagePlan).toOption
  let raw : RawFlatContext := {
    read field :=
      if field = crossGroupCode.id then code
      else if field = crossGroupTarget.id then .parsed (.num target)
      else .empty }
  evalValidationRule? crossGroupModel rule raw
    GroupPresenceContext.unavailable true

def crossGroupStringRangeExpectedMessage
    (messageType : Polarity) : FlatRuleMessage :=
  { errorAddress := { field := crossGroupTarget.id, path := [] }
    errorCode := "computedRange"
    severity := .error
    messageType
    text }

def crossGroupFieldValueAsNumberOutcome (target : Rat)
    (source : RawCell := .parsed (.enum "2")) : Option FlatRuleOutcome := do
  let operation ← crossGroupFieldValueAsNumberOperation.toOption
  let rule ← (assembleGeneratedNumericOperationRule crossGroupModel operation
    "computedNumericChoice" none messagePlan).toOption
  let raw : RawFlatContext := {
    read field :=
      if field = crossGroupNumericChoice.id then source
      else if field = crossGroupTarget.id then .parsed (.num target)
      else .empty }
  evalValidationRule? crossGroupModel rule raw
    GroupPresenceContext.unavailable true

def crossGroupFieldValueAsNumberExpectedMessage
    (messageType : Polarity) : FlatRuleMessage :=
  { errorAddress := { field := crossGroupTarget.id, path := [] }
    errorCode := "computedNumericChoice"
    severity := .error
    messageType
    text }

def aggregateExpectedMessage : FlatRuleMessage :=
  { errorAddress := { field := crossGroupTarget.id, path := [] }
    errorCode := "computedAggregate"
    severity := .error
    messageType := .value
    text }

def expressionTableExpectedMessage : FlatRuleMessage :=
  { errorAddress := { field := crossGroupTarget.id, path := [] }
    errorCode := "computedExpressionTable"
    severity := .error
    messageType := .value
    text }

def crossGroupExpressionTargetMismatch :
    Option GeneratedComputationValidationError := do
  let first ← crossGroupNumberOperation.toOption
  let second ← crossGroupOtherTargetOperation.toOption
  let table : GeneratedComputationTable
      (CheckedNumericComputationOperation crossGroupModel) := {
    targetField := crossGroupTarget.id
    name := "mismatchedTargets"
    alternatives := .guarded {
      first := { precondition := .fieldFilled crossGroupSource.id, operation := first }
      second := { precondition := .fieldFilled crossGroupSource.id, operation := second } }
    messagePlan }
  match assembleGeneratedNumericOperationTableRule crossGroupModel table with
  | .ok _ => none
  | .error error => some error

def generatedOperationError {model : FlatModel}
    (candidate : Except NumericComputationElabError
      (CheckedNumericComputationOperation model)) :
    Option GeneratedComputationValidationError := do
  let operation ← candidate.toOption
  match operation.generatedMismatchComparison none with
  | .ok _ => none
  | .error error => some error

def repeatableAggregateGeneratedError :
    Option GeneratedComputationValidationError :=
  generatedOperationError repeatableAggregateOperation

def repeatableValueCountGeneratedError :
    Option GeneratedComputationValidationError :=
  generatedOperationError repeatableValueCountOperation

def repeatableTokenValueCountGeneratedError :
    Option GeneratedComputationValidationError :=
  generatedOperationError repeatableTokenValueCountOperation

def productAggregateGeneratedError :
    Option GeneratedComputationValidationError :=
  generatedOperationError productAggregateOperation

def firstFilledGeneratedError :
    Option GeneratedComputationValidationError :=
  generatedOperationError crossGroupFirstFilledOperation

def firstFilledGeneratedScope : Option NumericOperandScope := do
  let operation ← crossGroupFirstFilledOperation.toOption
  let comparison ← (operation.generatedMismatchComparison none).toOption
  pure comparison.operandScope

def repeatableFirstFilledGeneratedError :
    Option GeneratedComputationValidationError :=
  generatedOperationError repeatableFirstFilledOperation

def bothHoldingDifferent : LiteralNumberComputation :=
  computation (.fieldFilled gate.id) 1 (.fieldFilled gate.id) 2


end A12Kernel.Conformance.GeneratedComputationValidation.Support.CrossGroup
