import A12Kernel.Elaboration.GeneratedComputationValidation
import A12Kernel.Elaboration.NumericComputation

/-! # Generated-computation validation locks -/

namespace A12Kernel.Conformance.GeneratedComputationValidation

open A12Kernel

private def gate : FlatFieldDecl :=
  { id := 0, groupPath := ["Form"], name := "Gate",
    policy := { kind := .number { scale := 0, signed := true } } }

private def target : FlatFieldDecl :=
  { id := 1, groupPath := ["Form"], name := "Target",
    policy := { kind := .number { scale := 0, signed := true } } }

private def broken : FlatFieldDecl :=
  { id := 2, groupPath := ["Form"], name := "Broken",
    policy := { kind := .boolean } }

private def textGuard : FlatFieldDecl :=
  { id := 3, groupPath := ["Form"], name := "TextGuard",
    policy := { kind := .string } }

private def repeatedGate : FlatFieldDecl :=
  { id := 4, groupPath := ["Form", "Rows"], name := "Gate",
    policy := { kind := .number { scale := 0, signed := true } },
    repeatableScope := [10] }

private def repeatedTarget : FlatFieldDecl :=
  { id := 5, groupPath := ["Form", "Rows"], name := "Target",
    policy := { kind := .number { scale := 0, signed := true } },
    repeatableScope := [10] }

private def model : FlatModel :=
  { fields := [gate, target, broken, textGuard] }

private def repeatableModel : FlatModel :=
  { fields := [
      gate, target, broken, textGuard, repeatedGate, repeatedTarget]
    repeatableGroups := [{ level := 10, path := ["Form", "Rows"] }] }

private def repeatedGateStar : SurfaceStarFieldPath :=
  { base := .absolute
    groups := [
      { name := "Form" },
      { name := "Rows", starred := true }]
    field := "Gate" }

private def repeatedTargetStar : SurfaceStarFieldPath :=
  { repeatedGateStar with field := "Target" }

private def repeatableFirstFilledHaving : SurfaceCorrelatedHaving :=
  .compareNumbers .equal
    { origin := .inner
      field := {
        base := .absolute
        groups := ["Form", "Rows"]
        field := "Gate" } }
    { origin := .outer
      field := {
        base := .absolute
        groups := ["Form"]
        field := "Gate" } }

private def repeatableAggregateOperation :
    Except NumericComputationElabError
      (CheckedNumericComputationOperation repeatableModel) :=
  elaborateNumberEntityComputationOperation repeatableModel ["Form"] target.id
    (.atom (.aggregate .sum {
      first := .star repeatedGateStar
      rest := [] }))

private def repeatableFirstFilledOperation :
    Except NumericComputationElabError
      (CheckedNumericComputationOperation repeatableModel) :=
  elaborateCompleteNumericComputationOperation repeatableModel ["Form"] target.id
    (.atom (.firstFilled {
      first := .starHaving repeatedTargetStar repeatableFirstFilledHaving
      rest := [] }))

private def productAggregateOperation :
    Except NumericComputationElabError
      (CheckedNumericComputationOperation repeatableModel) :=
  elaborateCompleteNumericComputationOperation repeatableModel ["Form"] target.id
    (.atom (.sumOfProducts {
      left := repeatedGateStar
      right := repeatedTargetStar }))

private def crossGroupSource : FlatFieldDecl :=
  { id := 20, groupPath := ["Input"], name := "Source",
    policy := { kind := .number { scale := 0, signed := true } } }

private def crossGroupDate : FlatFieldDecl :=
  { id := 21, groupPath := ["Input"], name := "StartDate",
    policy := { kind := .temporal .date TemporalComponents.fullDate } }

private def crossGroupExtra : FlatFieldDecl :=
  { id := 13, groupPath := ["Input"], name := "Extra",
    policy := { kind := .number { scale := 0, signed := false } } }

private def crossGroupCode : FlatFieldDecl :=
  { id := 24, groupPath := ["Input"], name := "Code",
    policy := { kind := .string } }

private def crossGroupNumericChoice : FlatFieldDecl :=
  { id := 25, groupPath := ["Input"], name := "NumericChoice",
    policy := { kind := .enumeration },
    enumeration := some {
      storedTokens := ["1", "2", "3"]
      categories := [{ name := "Factor", tokens := ["10", "20", "30"] }] } }

private def crossGroupTarget : FlatFieldDecl :=
  { id := 22, groupPath := ["Output"], name := "Target",
    policy := { kind := .number { scale := 0, signed := true } } }

private def crossGroupOtherTarget : FlatFieldDecl :=
  { id := 23, groupPath := ["Output"], name := "OtherTarget",
    policy := { kind := .number { scale := 0, signed := true } } }

private def crossGroupModel : FlatModel :=
  { fields := [crossGroupSource, crossGroupDate, crossGroupExtra, crossGroupTarget,
      crossGroupOtherTarget, crossGroupCode, crossGroupNumericChoice]
    baseYear := some 2024
    timeZoneId := "Europe/Berlin" }

private def absolutePath (groups : List String) (field : String) :
    SurfaceFieldPath :=
  { base := .absolute, groups, field }

private def crossGroupNumberOperation :
    Except NumericComputationElabError
      (CheckedNumericComputationOperation crossGroupModel) :=
  elaborateNumericComputationOperation crossGroupModel ["Rules"]
    crossGroupTarget.id (.atom (.field (absolutePath ["Input"] "Source")))

private def crossGroupDatePartOperation :
    Except NumericComputationElabError
      (CheckedNumericComputationOperation crossGroupModel) :=
  elaborateNumericComputationOperation crossGroupModel ["Rules"]
    crossGroupTarget.id
    (.abs
      (.atom (.temporalFieldPart
        (absolutePath ["Input"] "StartDate") (.date .year))))

private def crossGroupDayDifferenceOperation :
    Except NumericComputationElabError
      (CheckedNumericComputationOperation crossGroupModel) :=
  elaborateNumericComputationOperation crossGroupModel ["Rules"]
    crossGroupTarget.id
    (.atom (.dayDifference (.baseYear .direct)
      (.field (absolutePath ["Input"] "StartDate"))))

private def crossGroupOffsetOperation :
    Except NumericComputationElabError
      (CheckedNumericComputationOperation crossGroupModel) :=
  elaborateNumericComputationOperation crossGroupModel ["Rules"]
    crossGroupTarget.id
    (.binary .add
      (.round .halfUp omittedRoundingPlaces
        (.binary .add
          (.atom (.field (absolutePath ["Input"] "Source")))
          (.literal { value := 1, authoredScale := 0 })))
      (.literal { value := 0, authoredScale := 0 }))

private def crossGroupOtherTargetOperation :
    Except NumericComputationElabError
      (CheckedNumericComputationOperation crossGroupModel) :=
  elaborateNumericComputationOperation crossGroupModel ["Rules"]
    crossGroupOtherTarget.id
    (.atom (.field (absolutePath ["Input"] "Source")))

private def crossGroupAggregateOperation :
    Except NumericComputationElabError
      (CheckedNumericComputationOperation crossGroupModel) :=
  elaborateNumericComputationOperation crossGroupModel ["Rules"]
    crossGroupTarget.id
    (.round .floor omittedRoundingPlaces
      (.abs (.binary .add
        (AuthoredNumericExpr.extremumList .minimum
          (AuthoredNumericExpr.extremumList .maximum
            (.binary .add
              (.atom (.aggregate .sum {
                first := absolutePath ["Input"] "Source"
                rest := [absolutePath ["Input"] "Extra"] }))
              (.literal { value := 0, authoredScale := 0 }))
            [.literal { value := -5, authoredScale := 0 }])
          [.literal { value := -4, authoredScale := 0 }])
        (.literal { value := 0, authoredScale := 0 }))))

private def crossGroupFirstFilledOperation :
    Except NumericComputationElabError
      (CheckedNumericComputationOperation crossGroupModel) :=
  elaborateCompleteNumericComputationOperation crossGroupModel ["Rules"]
    crossGroupTarget.id
    (.atom (.firstFilled {
      first := .field (absolutePath ["Input"] "Source")
      rest := [.field (absolutePath ["Input"] "Extra")] }))

private def crossGroupStringRangeOperation :
    Except NumericComputationElabError
      (CheckedNumericComputationOperation crossGroupModel) :=
  elaborateNumericComputationOperation crossGroupModel ["Rules"]
    crossGroupTarget.id
    (.abs (.atom (.stringRange (absolutePath ["Input"] "Code") 1 2)))

private def crossGroupFieldValueAsNumberOperation :
    Except NumericComputationElabError
      (CheckedNumericComputationOperation crossGroupModel) :=
  elaborateNumericComputationOperation crossGroupModel ["Rules"]
    crossGroupTarget.id
    (.round .halfUp omittedRoundingPlaces
      (.atom (.fieldValueAsNumber
        (.category (absolutePath ["Input"] "NumericChoice") "Factor"))))

private def messagePlan : MessageRenderPlan :=
  { parts := [.text "Target disagrees with the computation table"] }

private def text : ResolvedMessageText :=
  messagePlan.render

private def literal (value : Rat) : DecodedNumericLiteral :=
  { value, authoredScale := 0 }

private def alternative (precondition : ComputationCondition)
    (operation : Rat) : LiteralNumberComputationAlternative :=
  { precondition, operation := literal operation }

private def guardedComputation (first second : LiteralNumberComputationAlternative)
    (remaining : List LiteralNumberComputationAlternative := []) :
    LiteralNumberComputation :=
  { targetField := target.id
    name := "computedTarget"
    alternatives := .guarded {
      first
      second
      remaining }
    messagePlan }

private def computation (firstGuard : ComputationCondition) (firstValue : Rat)
    (secondGuard : ComputationCondition) (secondValue : Rat) :
    LiteralNumberComputation :=
  guardedComputation (alternative firstGuard firstValue)
    (alternative secondGuard secondValue)

private def singletonComputation (precondition : Option ComputationCondition)
    (value : Rat) : LiteralNumberComputation :=
  { targetField := target.id
    name := "computedTarget"
    alternatives := .singleton {
      precondition
      operation := literal value }
    messagePlan }

private def bothFilled (targetCell : RawCell) : RawFlatContext where
  read field :=
    if field = gate.id then .parsed (.num 7)
    else if field = target.id then targetCell
    else .empty

private def gateEmptyTargetOne : RawFlatContext where
  read field :=
    if field = target.id then .parsed (.num 1)
    else .empty

private def textGuardTargetOne (textCell : RawCell) : RawFlatContext where
  read field :=
    if field = textGuard.id then textCell
    else if field = target.id then .parsed (.num 1)
    else .empty

private def brokenAndHealthy : RawFlatContext where
  read field :=
    if field = gate.id then .parsed (.num 7)
    else if field = target.id then .parsed (.num 1)
    else if field = broken.id then .rejected .malformed
    else .empty

private def evaluationWorld : World :=
  { now := { epochMillis := 0 } }

private def repeatableDocument (rows : List RowIndex) : Document :=
  { instantiatedRows := rows.map fun row => { group := 10, path := [row] }
    rawCells := fun _ => none }

private def checkedNumber (raw : RawCell) : CheckedCell :=
  formalCheck { kind := .number { scale := 0, signed := true } } raw

private def repeatableRead (outerGate : CheckedCell)
    (filterRows targetRows : RowIndex → CheckedCell)
    (environment : Env) (field : FieldId) : CheckedCell :=
  if field == gate.id then outerGate
  else
    match environment with
    | [(10, row)] =>
        if field == repeatedGate.id then filterRows row
        else if field == repeatedTarget.id then targetRows row
        else malformedCheckedCell
    | _ => malformedCheckedCell

private def repeatableRaw (outerGate targetCell : RawCell) : RawFlatContext where
  read field :=
    if field == gate.id then outerGate
    else if field == target.id then targetCell
    else .empty

private def repeatableGeneratedRule?
    (operationResult : Except NumericComputationElabError
      (CheckedNumericComputationOperation repeatableModel))
    (errorCode : String) :
    Option (CheckedResolvedValidationRule repeatableModel) := do
  let operation ← operationResult.toOption
  (assembleGeneratedNumericOperationRule repeatableModel operation
    errorCode none messagePlan).toOption

private def repeatableGeneratedScalarCapability
    (operationResult : Except NumericComputationElabError
      (CheckedNumericComputationOperation repeatableModel))
    (errorCode : String) :
    Option (Bool × Except ValidationEvaluationError FlatRuleOutcome) := do
  let rule ← repeatableGeneratedRule? operationResult errorCode
  let prepared ←
    (prepareFlatStringContext evaluationWorld builtinStringPatternCompiler
      repeatableModel).toOption
  pure (
    rule.requiresAddressedValidation,
    rule.evalFull prepared "en_US" (repeatableRaw .empty (.parsed (.num 0)))
      GroupPresenceContext.unavailable true)

private def hasAddressedScalarRejection
    (capability :
      Option (Bool × Except ValidationEvaluationError FlatRuleOutcome)) : Bool :=
  match capability with
  | some (true, .error .addressedContextRequired) => true
  | _ => false

private def hasScalarOutcome
    (capability :
      Option (Bool × Except ValidationEvaluationError FlatRuleOutcome))
    (expected : FlatRuleOutcome) : Bool :=
  match capability with
  | some (false, .ok actual) => decide (actual = expected)
  | _ => false

private def repeatableFirstFilledReferences :
    Option (Bool × Bool × Bool × NumericOperandScope) := do
  let operation ← repeatableFirstFilledOperation.toOption
  let comparison ← (operation.generatedMismatchComparison none).toOption
  pure (
    comparison.core.referencesField target.id,
    comparison.core.referencesField repeatedTarget.id,
    comparison.core.referencesField repeatedGate.id &&
      comparison.core.referencesField gate.id,
    comparison.operandScope)

private def repeatableAggregateReferences :
    Option (Bool × Bool × NumericOperandScope) := do
  let operation ← repeatableAggregateOperation.toOption
  let comparison ← (operation.generatedMismatchComparison none).toOption
  pure (
    comparison.core.referencesField target.id,
    comparison.core.referencesField repeatedGate.id,
    comparison.operandScope)

private def productAggregateReferences :
    Option (Bool × Bool × Bool × NumericOperandScope) := do
  let operation ← productAggregateOperation.toOption
  let comparison ← (operation.generatedMismatchComparison none).toOption
  pure (
    comparison.core.referencesField target.id,
    comparison.core.referencesField repeatedGate.id,
    comparison.core.referencesField repeatedTarget.id,
    comparison.operandScope)

private def repeatableGeneratedAddressedOutcome
    (operationResult : Except NumericComputationElabError
      (CheckedNumericComputationOperation repeatableModel))
    (errorCode : String)
    (document : Document) (outerGate targetCell : RawCell)
    (filterRows targetRows : RowIndex → CheckedCell) :
    Option (Except StarAddressingError FlatRuleOutcome) := do
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
    document
    outer := []
    read := repeatableRead (fields.read gate.id) filterRows targetRows
  } true)

private def repeatableFirstFilledAddressedOutcome
    (document : Document) (outerGate targetCell : RawCell)
    (filterRows targetRows : RowIndex → CheckedCell) :
    Option (Except StarAddressingError FlatRuleOutcome) :=
  repeatableGeneratedAddressedOutcome repeatableFirstFilledOperation
    "computedRepeatableFirstFilled" document outerGate targetCell
    filterRows targetRows

private def repeatableAggregateAddressedOutcome
    (document : Document) (targetCell : RawCell)
    (sourceRows : RowIndex → CheckedCell) :
    Option (Except StarAddressingError FlatRuleOutcome) :=
  repeatableGeneratedAddressedOutcome repeatableAggregateOperation
    "computedRepeatableAggregate" document .empty targetCell
    sourceRows (fun _ => checkedNumber .empty)

private def productAggregateAddressedOutcome
    (document : Document) (targetCell : RawCell)
    (leftRows rightRows : RowIndex → CheckedCell) :
    Option (Except StarAddressingError FlatRuleOutcome) :=
  repeatableGeneratedAddressedOutcome productAggregateOperation
    "computedProductAggregate" document .empty targetCell leftRows rightRows

private def repeatableExpectedMessage
    (errorCode : String) (messageType : Polarity) : FlatRuleMessage :=
  { errorAddress := { field := target.id, path := [] }
    errorCode
    severity := .error
    messageType
    text }

private def repeatableFirstFilledExpectedMessage : FlatRuleMessage :=
  repeatableExpectedMessage "computedRepeatableFirstFilled" .omission

private def repeatableAggregateExpectedMessage : FlatRuleMessage :=
  repeatableExpectedMessage "computedRepeatableAggregate" .omission

private def productAggregateExpectedMessage : FlatRuleMessage :=
  repeatableExpectedMessage "computedProductAggregate" .omission

private def hasAddressedOutcome
    (result : Option (Except StarAddressingError FlatRuleOutcome))
    (expected : FlatRuleOutcome) : Bool :=
  match result with
  | some (.ok actual) => decide (actual = expected)
  | _ => false

private def hasAddressingError
    (result : Option (Except StarAddressingError FlatRuleOutcome))
    (expected : StarAddressingError) : Bool :=
  match result with
  | some (.error actual) => decide (actual = expected)
  | _ => false

private def evalFlatRule? (checkedModel : FlatModel)
    (rule : CheckedResolvedFlatRule checkedModel) (raw : RawFlatContext)
    (hasContent : Bool) : Option FlatRuleOutcome := do
  let prepared ←
    (prepareFlatStringContext evaluationWorld builtinStringPatternCompiler
      checkedModel).toOption
  pure (rule.evalFull prepared "en_US" raw hasContent)

private def evalValidationRule? (checkedModel : FlatModel)
    (rule : CheckedResolvedValidationRule checkedModel)
    (raw : RawFlatContext) (groups : GroupPresenceContext)
    (hasContent : Bool) : Option FlatRuleOutcome := do
  let prepared ←
    (prepareFlatStringContext evaluationWorld builtinStringPatternCompiler
      checkedModel).toOption
  (rule.evalFull prepared "en_US" raw groups hasContent).toOption

private def selectionOf (candidate : LiteralNumberComputation)
    (raw : RawFlatContext) :
    ComputationAlternativeSelection DecodedNumericLiteral :=
  GeneratedComputationTable.selectFirst candidate
    { read := (model.checkContext raw).read }

private def outcomeOf (candidate : LiteralNumberComputation)
    (raw : RawFlatContext) : Option FlatRuleOutcome :=
  match assembleGeneratedLiteralNumberRule model candidate with
  | .error _ => none
  | .ok rule => evalFlatRule? model rule raw true

private def assemblyErrorIn (checkedModel : FlatModel)
    (candidate : LiteralNumberComputation) :
    Option GeneratedComputationValidationError :=
  match assembleGeneratedLiteralNumberRule checkedModel candidate with
  | .ok _ => none
  | .error error => some error

private def assemblyErrorOf :=
  assemblyErrorIn model

private def generatedRowGroupOf (candidate : LiteralNumberComputation) :
    Option GroupPath :=
  match assembleGeneratedLiteralNumberRule model candidate with
  | .ok rule => some rule.condition.rowGroup
  | .error _ => none

private def expectedMessage (messageType : Polarity) : FlatRuleMessage :=
  { errorAddress := { field := target.id, path := [] }
    errorCode := "computedTarget"
    severity := .error
    messageType
    text }

private def crossGroupRaw (source target : Rat) : RawFlatContext where
  read field :=
    if field = crossGroupSource.id then .parsed (.num source)
    else if field = crossGroupExtra.id then .parsed (.num 2)
    else if field = crossGroupTarget.id then .parsed (.num target)
    else .empty

private def crossGroupScalarCapability :
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

private def crossGroupOutcome (source target : Rat) : Option FlatRuleOutcome := do
  let operation ← crossGroupNumberOperation.toOption
  let rule ← (assembleGeneratedNumericOperationRule crossGroupModel operation
    "computedCrossGroup" none messagePlan).toOption
  evalValidationRule? crossGroupModel rule (crossGroupRaw source target)
    GroupPresenceContext.unavailable true

private def crossGroupDatePartOutcome (target : Rat) : Option FlatRuleOutcome := do
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

private def crossGroupDayDifferenceOutcome
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

private def crossGroupGeneratedBoundary :
    Option (GroupPath × NumericOperandScope) := do
  let operation ← crossGroupNumberOperation.toOption
  let comparison ← (operation.generatedMismatchComparison none).toOption
  pure (comparison.rowGroup, comparison.operandScope)

private def crossGroupFirstFilledVerdict
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

private def crossGroupOrdinaryError : Option NumericValidationElabError :=
  match elaborateNumericComparison crossGroupModel ["Output"] {
      op := .ordinary .notEqual
      left := .atom (.field (absolutePath ["Output"] "Target"))
      right := .atom (.field (absolutePath ["Input"] "Source")) } with
  | .ok _ => none
  | .error error => some error

private def crossGroupExpectedMessage : FlatRuleMessage :=
  { errorAddress := { field := crossGroupTarget.id, path := [] }
    errorCode := "computedCrossGroup"
    severity := .error
    messageType := .value
    text }

private def crossGroupDatePartExpectedMessage : FlatRuleMessage :=
  { errorAddress := { field := crossGroupTarget.id, path := [] }
    errorCode := "computedDatePart"
    severity := .error
    messageType := .value
    text }

private def crossGroupDayDifferenceExpectedMessage : FlatRuleMessage :=
  { errorAddress := { field := crossGroupTarget.id, path := [] }
    errorCode := "computedDayDifference"
    severity := .error
    messageType := .value
    text }

private def crossGroupExpressionTable
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

private def selectedCrossGroupExpression :
    Option (AuthoredNumericExpr
      (CheckedNumericComputationAtom crossGroupModel)) := do
  let table ← crossGroupExpressionTable
  match table.selectFirst {
      read := (crossGroupModel.checkContext (crossGroupRaw 3 3)).read } with
  | .selected operation => some operation.core.expression
  | .noMatch | .poison _ => none

private def crossGroupExpressionTableOutcome
    (secondTolerance : Option NumericToleranceRange := none)
    (common : Option ComputationCondition := none) : Option FlatRuleOutcome := do
  let table ← crossGroupExpressionTable secondTolerance
  let rule ← (assembleGeneratedNumericOperationTableRule crossGroupModel
    { table with commonPrecondition := common }).toOption
  evalValidationRule? crossGroupModel rule (crossGroupRaw 3 3)
    GroupPresenceContext.unavailable true

private def crossGroupExpressionSingletonOutcome
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

private def crossGroupAggregateOutcome (target : Rat) : Option FlatRuleOutcome := do
  let operation ← crossGroupAggregateOperation.toOption
  let rule ← (assembleGeneratedNumericOperationRule crossGroupModel operation
    "computedAggregate" none messagePlan).toOption
  evalValidationRule? crossGroupModel rule (crossGroupRaw 3 target)
    GroupPresenceContext.unavailable true

private def crossGroupAggregateTableOutcome (target : Rat) : Option FlatRuleOutcome := do
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

private def crossGroupStringRangeOutcome (target : Rat)
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

private def crossGroupStringRangeExpectedMessage
    (messageType : Polarity) : FlatRuleMessage :=
  { errorAddress := { field := crossGroupTarget.id, path := [] }
    errorCode := "computedRange"
    severity := .error
    messageType
    text }

private def crossGroupFieldValueAsNumberOutcome (target : Rat)
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

private def crossGroupFieldValueAsNumberExpectedMessage
    (messageType : Polarity) : FlatRuleMessage :=
  { errorAddress := { field := crossGroupTarget.id, path := [] }
    errorCode := "computedNumericChoice"
    severity := .error
    messageType
    text }

private def aggregateExpectedMessage : FlatRuleMessage :=
  { errorAddress := { field := crossGroupTarget.id, path := [] }
    errorCode := "computedAggregate"
    severity := .error
    messageType := .value
    text }

private def expressionTableExpectedMessage : FlatRuleMessage :=
  { errorAddress := { field := crossGroupTarget.id, path := [] }
    errorCode := "computedExpressionTable"
    severity := .error
    messageType := .value
    text }

private def crossGroupExpressionTargetMismatch :
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

private def generatedOperationError {model : FlatModel}
    (candidate : Except NumericComputationElabError
      (CheckedNumericComputationOperation model)) :
    Option GeneratedComputationValidationError := do
  let operation ← candidate.toOption
  match operation.generatedMismatchComparison none with
  | .ok _ => none
  | .error error => some error

private def repeatableAggregateGeneratedError :
    Option GeneratedComputationValidationError :=
  generatedOperationError repeatableAggregateOperation

private def productAggregateGeneratedError :
    Option GeneratedComputationValidationError :=
  generatedOperationError productAggregateOperation

private def firstFilledGeneratedError :
    Option GeneratedComputationValidationError :=
  generatedOperationError crossGroupFirstFilledOperation

private def firstFilledGeneratedScope : Option NumericOperandScope := do
  let operation ← crossGroupFirstFilledOperation.toOption
  let comparison ← (operation.generatedMismatchComparison none).toOption
  pure comparison.operandScope

private def repeatableFirstFilledGeneratedError :
    Option GeneratedComputationValidationError :=
  generatedOperationError repeatableFirstFilledOperation

private def bothHoldingDifferent : LiteralNumberComputation :=
  computation (.fieldFilled gate.id) 1 (.fieldFilled gate.id) 2

/- Semantic desugaring derives the checked condition's row group from the resolved computation target declaration. -/
example : generatedRowGroupOf bothHoldingDifferent = some ["Form"] := by
  native_decide

private def tolerateFirst (range : NumericToleranceRange)
    (candidate : LiteralNumberComputation) : LiteralNumberComputation :=
  match candidate.alternatives with
  | .singleton alternative =>
      { candidate with alternatives := .singleton {
          alternative with tolerance := some range } }
  | .guarded alternatives =>
      { candidate with alternatives := .guarded {
          alternatives with
          first := { alternatives.first with tolerance := some range } } }

/- Computation selects the first holding operation, while generated validation retains the later holding mismatch. -/
example :
    selectionOf bothHoldingDifferent
        (bothFilled (.parsed (.num 1))) = .selected (literal 1) ∧
      outcomeOf bothHoldingDifferent
        (bothFilled (.parsed (.num 1))) =
          some (.fired (expectedMessage .value)) := by
  native_decide

/- The sole alternative may omit its precondition: computation selects it directly, while generated validation compares it without fabricating a guard. -/
example :
    let candidate := singletonComputation none 3
    selectionOf candidate (bothFilled (.parsed (.num 1))) =
        .selected (literal 3) ∧
      outcomeOf candidate (bothFilled (.parsed (.num 1))) =
        some (.fired (expectedMessage .value)) ∧
      outcomeOf candidate (bothFilled (.parsed (.num 3))) =
        some .notFired := by
  native_decide

/- A singleton's own guard and the table-wide common guard independently suppress both consumers when false. -/
example :
    let guarded := singletonComputation (some (.fieldNotFilled gate.id)) 3
    let commonGuarded :=
      { singletonComputation none 3 with
        commonPrecondition := some (.fieldNotFilled gate.id) }
    selectionOf guarded (bothFilled (.parsed (.num 1))) = .noMatch ∧
      outcomeOf guarded (bothFilled (.parsed (.num 1))) = some .notFired ∧
      selectionOf commonGuarded (bothFilled (.parsed (.num 1))) = .noMatch ∧
      outcomeOf commonGuarded (bothFilled (.parsed (.num 1))) =
        some .notFired := by
  native_decide

/- A third guarded alternative remains in declaration order for both first-match selection and all-alternatives validation. -/
example :
    let candidate :=
      guardedComputation
        (alternative (.fieldNotFilled gate.id) 90)
        (alternative (.fieldNotFilled gate.id) 91)
        [alternative (.fieldFilled gate.id) 3]
    selectionOf candidate (bothFilled (.parsed (.num 1))) =
        .selected (literal 3) ∧
      outcomeOf candidate (bothFilled (.parsed (.num 1))) =
        some (.fired (expectedMessage .value)) := by
  native_decide

/- Equal results under the same overlapping guard do not create a mismatch. -/
example :
    let candidate :=
      computation (.fieldFilled gate.id) 1 (.fieldFilled gate.id) 1
    selectionOf candidate (bothFilled (.parsed (.num 1))) =
        .selected (literal 1) ∧
      outcomeOf candidate (bothFilled (.parsed (.num 1))) =
        some .notFired := by
  native_decide

/- Per-alternative tolerance changes only the generated mismatch: computation still selects the literal operation, while interior and boundary differences stay quiet and a strict exterior fires. -/
example :
    let candidate := tolerateFirst .range1 <|
      computation (.fieldFilled gate.id) 1 (.fieldNotFilled gate.id) 99
    selectionOf candidate (bothFilled (.parsed (.num 2))) =
        .selected (literal 1) ∧
      outcomeOf candidate (bothFilled (.parsed (.num (3 / 2)))) =
        some .notFired ∧
      outcomeOf candidate (bothFilled (.parsed (.num 2))) =
        some .notFired ∧
      outcomeOf candidate (bothFilled (.parsed (.num 3))) =
        some (.fired (expectedMessage .value)) := by
  native_decide

/- Tolerance is tier-local: a tolerant first mismatch does not soften a later strict alternative. -/
example :
    let candidate := tolerateFirst .range10 <|
      computation (.fieldFilled gate.id) 1 (.fieldFilled gate.id) 20
    outcomeOf candidate (bothFilled (.parsed (.num 10))) =
      some (.fired (expectedMessage .value)) := by
  native_decide

/- A nonholding second guard cannot make its different operation reject the selected result. -/
example :
    let candidate :=
      computation (.fieldFilled gate.id) 1 (.fieldNotFilled gate.id) 2
    selectionOf candidate (bothFilled (.parsed (.num 1))) =
        .selected (literal 1) ∧
      outcomeOf candidate (bothFilled (.parsed (.num 1))) =
        some .notFired := by
  native_decide

/- A cleanly false common precondition suppresses both computation selection and the complete generated mismatch disjunction. -/
example :
    let candidate :=
      { bothHoldingDifferent with
        commonPrecondition := some (.fieldNotFilled gate.id) }
    selectionOf candidate (bothFilled (.parsed (.num 2))) = .noMatch ∧
      outcomeOf candidate (bothFilled (.parsed (.num 2))) =
        some .notFired := by
  native_decide

/- A holding common precondition preserves first-match computation while generated validation still retains the later holding mismatch. -/
example :
    let candidate :=
      { bothHoldingDifferent with
        commonPrecondition := some (.fieldFilled gate.id) }
    selectionOf candidate (bothFilled (.parsed (.num 1))) =
        .selected (literal 1) ∧
      outcomeOf candidate (bothFilled (.parsed (.num 1))) =
        some (.fired (expectedMessage .value)) := by
  native_decide

/- A malformed common guard preserves the phase split before any alternative-specific guard contributes. -/
example :
    let candidate :=
      { bothHoldingDifferent with
        commonPrecondition := some (.fieldFilled broken.id) }
    selectionOf candidate brokenAndHealthy = .poison .malformed ∧
      outcomeOf candidate brokenAndHealthy = some .unknown := by
  native_decide

/- An authored conjunction remains a conjunction in generated validation; one false conjunct keeps the differing first row silent. -/
example :
    let firstGuard :=
      ComputationCondition.and
        (.fieldFilled gate.id) (.fieldNotFilled gate.id)
    let candidate :=
      computation firstGuard 2 (.fieldFilled gate.id) 1
    selectionOf candidate (bothFilled (.parsed (.num 1))) =
        .selected (literal 1) ∧
      outcomeOf candidate (bothFilled (.parsed (.num 1))) =
        some .notFired := by
  native_decide

/- The explicit target-filled gate suppresses every mismatch when the target is empty. -/
example :
    selectionOf bothHoldingDifferent (bothFilled .empty) =
        .selected (literal 1) ∧
      outcomeOf bothHoldingDifferent (bothFilled .empty) =
        some .notFired := by
  native_decide

/- The same guard syntax has phase-specific consumers: computation poison aborts, while validation `Or` lets a healthy firing branch dominate unknown. -/
example :
    let guarded :=
      ComputationCondition.or (.fieldFilled broken.id) (.fieldFilled gate.id)
    let candidate :=
      computation guarded 2 (.fieldNotFilled gate.id) 1
    selectionOf candidate brokenAndHealthy = .poison .malformed ∧
      outcomeOf candidate brokenAndHealthy =
        some (.fired (expectedMessage .value)) := by
  native_decide

/- Message polarity remains data-derived: a not-filled guard can make this ERROR an OMISSION. -/
example :
    let candidate :=
      computation (.fieldNotFilled gate.id) 2 (.fieldFilled gate.id) 1
    selectionOf candidate gateEmptyTargetOne = .selected (literal 2) ∧
      outcomeOf candidate gateEmptyTargetOne =
        some (.fired (expectedMessage .omission)) := by
  native_decide

/- Swapping both literal results supplies an independent instance of the overlap mechanism. -/
example :
    let candidate :=
      computation (.fieldFilled gate.id) 2 (.fieldFilled gate.id) 1
    selectionOf candidate (bothFilled (.parsed (.num 2))) =
        .selected (literal 2) ∧
      outcomeOf candidate (bothFilled (.parsed (.num 2))) =
        some (.fired (expectedMessage .value)) := by
  native_decide

/- Authored numeric scale remains checked before the literal value is erased into the flat comparison. -/
example :
    let singletonMismatch :=
      { singletonComputation none 1 with alternatives := .singleton {
          operation := { value := 1, authoredScale := 1 } } }
    let firstMismatch :=
      guardedComputation {
          precondition := .fieldFilled gate.id
          operation := { value := 1, authoredScale := 1 }
        } (alternative (.fieldFilled gate.id) 2)
    let secondMismatch :=
      guardedComputation (alternative (.fieldFilled gate.id) 1) {
          precondition := .fieldFilled gate.id
          operation := { value := 2, authoredScale := 1 }
        }
    let thirdMismatch :=
      guardedComputation (alternative (.fieldFilled gate.id) 1)
        (alternative (.fieldFilled gate.id) 2) [{
          precondition := .fieldFilled gate.id
          operation := { value := 3, authoredScale := 1 }
        }]
    assemblyErrorOf singletonMismatch =
        some (.operationScaleMismatch 1 0 1) ∧
      assemblyErrorOf
        { singletonMismatch with
          commonPrecondition := some (.fieldFilled target.id) } =
        some (.operationScaleMismatch 1 0 1) ∧
      assemblyErrorOf firstMismatch =
        some (.operationScaleMismatch 1 0 1) ∧
      assemblyErrorOf secondMismatch =
        some (.operationScaleMismatch 2 0 1) ∧
      assemblyErrorOf thirdMismatch =
        some (.operationScaleMismatch 3 0 1) := by
  native_decide

/- A tolerance alternative bypasses the ordinary exact-comparison scale gate. -/
example :
    let singletonMismatch :=
      { singletonComputation none 1 with alternatives := .singleton {
          operation := { value := 1, authoredScale := 1 }
          tolerance := some .range1 } }
    let firstMismatch :=
      guardedComputation {
          precondition := .fieldFilled gate.id
          operation := { value := 1, authoredScale := 1 }
          tolerance := some .range1
        } (alternative (.fieldFilled gate.id) 2)
    let thirdMismatch :=
      guardedComputation (alternative (.fieldFilled gate.id) 1)
        (alternative (.fieldFilled gate.id) 2) [{
          precondition := .fieldFilled gate.id
          operation := { value := 3, authoredScale := 1 }
          tolerance := some .range1
        }]
    (assembleGeneratedLiteralNumberRule model singletonMismatch).isOk = true ∧
      (assembleGeneratedLiteralNumberRule model firstMismatch).isOk = true ∧
      (assembleGeneratedLiteralNumberRule model thirdMismatch).isOk = true := by
  native_decide

/- String presence guards are consumed in both phases without widening the Number target or table shape. -/
example :
    let candidate :=
      computation (.fieldFilled textGuard.id) 2
        (.fieldNotFilled textGuard.id) 1
    selectionOf candidate
        (textGuardTargetOne (.parsed (.str "present"))) =
        .selected (literal 2) ∧
      outcomeOf candidate
        (textGuardTargetOne (.parsed (.str "present"))) =
        some (.fired (expectedMessage .value)) ∧
      selectionOf candidate (textGuardTargetOne .presentEmpty) =
        .selected (literal 1) ∧
      outcomeOf candidate (textGuardTargetOne .presentEmpty) =
        some .notFired := by
  native_decide

/- A malformed String guard preserves the established phase split: computation poisons while generated validation is unknown. -/
example :
    let candidate :=
      computation (.fieldFilled textGuard.id) 2
        (.fieldNotFilled textGuard.id) 2
    selectionOf candidate (textGuardTargetOne (.rejected .malformed)) =
        .poison .malformed ∧
      outcomeOf candidate (textGuardTargetOne (.rejected .malformed)) =
        some .unknown := by
  native_decide

/- The generated fragment still rejects a non-Number target. -/
example :
    assemblyErrorOf
      { bothHoldingDifferent with targetField := broken.id } =
      some (.targetNotNumber broken.id) := by
  native_decide

/- The computed target cannot appear in the common or any alternative precondition; diagnostics retain the authored guard position. -/
example :
    assemblyErrorOf
        { bothHoldingDifferent with
          commonPrecondition := some
            (.and (.fieldFilled gate.id)
              (.or (.fieldNotFilled broken.id) (.fieldFilled target.id))) } =
        some (.targetSelfReference .common) ∧
      assemblyErrorOf
        (guardedComputation (alternative (.fieldFilled target.id) 1)
          (alternative (.fieldFilled gate.id) 2)) =
        some (.targetSelfReference (.alternative 1)) ∧
      assemblyErrorOf
        (guardedComputation (alternative (.fieldFilled gate.id) 1)
          (alternative (.fieldFilled gate.id) 2)
          [alternative (.fieldFilled target.id) 3]) =
        some (.targetSelfReference (.alternative 3)) ∧
      assemblyErrorOf
        (singletonComputation (some (.fieldFilled target.id)) 1) =
        some (.targetSelfReference (.alternative 1)) := by
  native_decide

/- The direct-ID route rejects repeatable guard and target declarations before constructing a flat rule. -/
example :
    assemblyErrorIn repeatableModel
        (computation (.fieldFilled repeatedGate.id) 1
          (.fieldFilled gate.id) 2) =
        some (.resolve (.repeatableReference repeatedGate.path)) ∧
      assemblyErrorIn repeatableModel
        { bothHoldingDifferent with targetField := repeatedTarget.id } =
        some (.resolve (.repeatableReference repeatedTarget.path)) ∧
      assemblyErrorIn repeatableModel
        { bothHoldingDifferent with
          commonPrecondition := some (.fieldFilled repeatedGate.id) } =
        some (.resolve (.repeatableReference repeatedGate.path)) ∧
      assemblyErrorIn repeatableModel
        (guardedComputation (alternative (.fieldFilled gate.id) 1)
          (alternative (.fieldFilled gate.id) 2)
          [alternative (.fieldFilled repeatedGate.id) 3]) =
        some (.resolve (.repeatableReference repeatedGate.path)) := by
  native_decide

/- Generated expression validation preserves computation's model-wide nonrepeatable operand scope; ordinary target-group validation still rejects the same cross-group reference. -/
example :
    hasScalarOutcome crossGroupScalarCapability .notFired = true ∧
      crossGroupOutcome 3 3 = some .notFired ∧
      crossGroupOutcome 3 4 = some (.fired crossGroupExpectedMessage) ∧
      crossGroupGeneratedBoundary =
        some (["Output"], .modelWideNonrepeatable) ∧
      crossGroupOrdinaryError =
        some (.fieldOutsideRowGroup ["Input", "Source"] ["Output"]) := by
  native_decide

/- The model-wide generated route traverses the same admitted temporal-component wrapper tree rather than treating direct Number as a special case. -/
example :
    (match crossGroupDatePartOperation with
    | .error _ => false
    | .ok operation =>
        (assembleGeneratedNumericOperationRule crossGroupModel operation
          "computedDatePart" none messagePlan).isOk) = true ∧
      crossGroupDatePartOutcome 2024 = some .notFired ∧
      crossGroupDatePartOutcome 2023 =
        some (.fired crossGroupDatePartExpectedMessage) := by
  native_decide

/- Generated validation preserves the checked profile-selected calendar-day atom and compares its scale-0 result without rebuilding temporal syntax. -/
example :
    crossGroupDayDifferenceOperation.isOk = true ∧
      crossGroupDayDifferenceOutcome 1 = some .notFired ∧
      crossGroupDayDifferenceOutcome 0 =
        some (.fired crossGroupDayDifferenceExpectedMessage) := by
  native_decide

/- Checked expression payloads reuse the source table: computation selects the first holding row, generated validation retains the later root-rounding/arithmetic mismatch, and tolerance remains validation-only. -/
example :
    selectedCrossGroupExpression =
      crossGroupNumberOperation.toOption.map
        (fun operation => operation.core.expression) := by
  rfl

example :
    crossGroupExpressionTableOutcome =
        some (.fired expressionTableExpectedMessage) ∧
      crossGroupExpressionTableOutcome (some .range1) = some .notFired ∧
      crossGroupExpressionSingletonOutcome 3 = some .notFired ∧
      crossGroupExpressionSingletonOutcome 4 =
        some (.fired expressionTableExpectedMessage) ∧
      crossGroupExpressionTableOutcome none
        (some (.fieldFilled crossGroupDate.id)) = some .notFired ∧
      crossGroupExpressionTargetMismatch = some (.operationTargetMismatch 2
        crossGroupTarget.id crossGroupOtherTarget.id) := by
  native_decide

/- A checked round/absolute/extremum/aggregate tree reaches both singleton and guarded all-alternative validation through the same expression narrowing; the later aggregate mismatch remains observable without a source-specific comparison wrapper. -/
example :
    crossGroupAggregateOutcome 4 = some .notFired ∧
      crossGroupAggregateOutcome 5 = some (.fired aggregateExpectedMessage) ∧
      crossGroupAggregateTableOutcome 3 =
        some (.fired aggregateExpectedMessage) := by
  native_decide

/- Every checked repeatable numeric source retains its address through generated-validation assembly rather than being flattened into scalar fields. -/
example :
    repeatableFirstFilledGeneratedError = none ∧
      repeatableAggregateGeneratedError = none ∧
      productAggregateGeneratedError = none ∧
      hasAddressedScalarRejection
          (repeatableGeneratedScalarCapability repeatableFirstFilledOperation
            "computedRepeatableFirstFilled") = true ∧
      hasAddressedScalarRejection
          (repeatableGeneratedScalarCapability repeatableAggregateOperation
            "computedRepeatableAggregate") = true ∧
      hasAddressedScalarRejection
          (repeatableGeneratedScalarCapability productAggregateOperation
            "computedProductAggregate") = true := by
  native_decide

/- The model-indexed leaf exposes the target, selected repeatable field, and both `Having` dependencies to Analyze/Transform consumers, then executes through the sole checked tree. Structural address failure remains outside semantic UNKNOWN. -/
example :
    let filterRows : RowIndex → CheckedCell
      | 1 => checkedNumber (.parsed (.num 0))
      | 2 => checkedNumber (.parsed (.num 1))
      | _ => checkedNumber .empty
    let targetRows : RowIndex → CheckedCell
      | 1 => checkedNumber (.parsed (.num 9))
      | 2 => checkedNumber (.parsed (.num 5))
      | _ => checkedNumber .empty
    let malformed : Document := {
      instantiatedRows := [{ group := 10, path := [1, 2] }]
      rawCells := fun _ => none }
    repeatableFirstFilledReferences =
        some (true, true, true, .modelWideCheckedComputation) ∧
      hasAddressedOutcome (repeatableFirstFilledAddressedOutcome
        (repeatableDocument [1, 2]) (.parsed (.num 1))
        (.parsed (.num 5)) filterRows targetRows) .notFired ∧
      hasAddressedOutcome (repeatableFirstFilledAddressedOutcome
        (repeatableDocument [1, 2]) (.parsed (.num 1))
        (.parsed (.num 6)) filterRows targetRows)
          (.fired repeatableFirstFilledExpectedMessage) ∧
      hasAddressingError (repeatableFirstFilledAddressedOutcome malformed
        (.parsed (.num 1)) (.parsed (.num 5)) filterRows targetRows)
          (.invalidRowDepth 10 [1, 2] 1) := by
  native_decide

/- Analyze sees each checked dependency while Execute preserves full aggregate folding versus row-aligned products. The 9/75 results reject first-filled flattening and Cartesian multiplication; malformed topology remains structural insufficient information. -/
example :
    let leftRows : RowIndex → CheckedCell
      | 1 => checkedNumber (.parsed (.num 2))
      | 2 => checkedNumber (.parsed (.num 3))
      | 3 => checkedNumber (.parsed (.num 4))
      | _ => checkedNumber .empty
    let rightRows : RowIndex → CheckedCell
      | 1 => checkedNumber (.parsed (.num 5))
      | 2 => checkedNumber (.parsed (.num 7))
      | 3 => checkedNumber (.parsed (.num 11))
      | _ => checkedNumber .empty
    let complete := repeatableDocument [1, 2, 3]
    let malformed : Document := {
      instantiatedRows := [{ group := 10, path := [1, 2] }]
      rawCells := fun _ => none }
    repeatableAggregateReferences =
        some (true, true, .modelWideCheckedComputation) ∧
      productAggregateReferences =
        some (true, true, true, .modelWideCheckedComputation) ∧
      hasAddressedOutcome
        (repeatableAggregateAddressedOutcome complete
          (.parsed (.num 9)) leftRows) .notFired ∧
      hasAddressedOutcome
        (repeatableAggregateAddressedOutcome complete
          (.parsed (.num 10)) leftRows)
          (.fired repeatableAggregateExpectedMessage) ∧
      hasAddressedOutcome
        (productAggregateAddressedOutcome complete
          (.parsed (.num 75)) leftRows rightRows) .notFired ∧
      hasAddressedOutcome
        (productAggregateAddressedOutcome complete
          (.parsed (.num 76)) leftRows rightRows)
          (.fired productAggregateExpectedMessage) ∧
      hasAddressingError
        (repeatableAggregateAddressedOutcome malformed
          (.parsed (.num 9)) leftRows)
          (.invalidRowDepth 10 [1, 2] 1) ∧
      hasAddressingError
        (productAggregateAddressedOutcome malformed
          (.parsed (.num 75)) leftRows rightRows)
          (.invalidRowDepth 10 [1, 2] 1) := by
  native_decide

/- Direct generated `FirstFilledValue` checks relevance in source order: a present head hides a nonrelevant suffix, while an empty head reaches that suffix. -/
example :
    let sourceAndTarget := fun field =>
      field == crossGroupSource.id || field == crossGroupTarget.id
    firstFilledGeneratedError = none ∧
      firstFilledGeneratedScope = some .modelWideNonrepeatable ∧
      crossGroupFirstFilledVerdict
        (.parsed (.num 3)) (.rejected .malformed) (.parsed (.num 3))
        sourceAndTarget = some .notFired ∧
      crossGroupFirstFilledVerdict
        .empty (.parsed (.num 2)) (.parsed (.num 2))
        sourceAndTarget = some .unknown ∧
      crossGroupFirstFilledVerdict
        .empty (.parsed (.num 2)) (.parsed (.num 2))
        (fun _ => true) = some .notFired := by
  native_decide

/- Generated validation narrows the checked absolute-value/String-range tree without rebuilding either layer and compares the same nonnegative result model-wide. -/
example :
    crossGroupStringRangeOutcome 12 = some .notFired ∧
      crossGroupStringRangeOutcome 13 =
        some (.fired (crossGroupStringRangeExpectedMessage .value)) ∧
      crossGroupStringRangeOutcome 13 .empty =
        some (.fired (crossGroupStringRangeExpectedMessage .omission)) ∧
      crossGroupStringRangeOutcome 13 (.parsed (.str "AB")) =
        some (.fired (crossGroupStringRangeExpectedMessage .value)) ∧
      crossGroupStringRangeOperation.isOk = true := by
  native_decide

/- Generated validation narrows the checked rounding/conversion tree without rebuilding either layer, preserving its category projection and missing-source polarity across the computation boundary. -/
example :
    crossGroupFieldValueAsNumberOutcome 20 = some .notFired ∧
      crossGroupFieldValueAsNumberOutcome 21 =
        some (.fired (crossGroupFieldValueAsNumberExpectedMessage .value)) ∧
      crossGroupFieldValueAsNumberOutcome 21 .empty =
        some (.fired (crossGroupFieldValueAsNumberExpectedMessage .omission)) ∧
      crossGroupFieldValueAsNumberOperation.isOk = true := by
  native_decide

end A12Kernel.Conformance.GeneratedComputationValidation
