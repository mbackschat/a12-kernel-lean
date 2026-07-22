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
      crossGroupOtherTarget, crossGroupCode, crossGroupNumericChoice] }

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
    (.atom (.temporalFieldPart (absolutePath ["Input"] "StartDate") (.date .year)))

private def crossGroupOffsetOperation :
    Except NumericComputationElabError
      (CheckedNumericComputationOperation crossGroupModel) :=
  elaborateNumericComputationOperation crossGroupModel ["Rules"]
    crossGroupTarget.id
    (.binary .add
      (.atom (.field (absolutePath ["Input"] "Source")))
      (.literal { value := 1, authoredScale := 0 }))

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
    (.atom (.aggregate .sum {
      first := absolutePath ["Input"] "Source"
      rest := [absolutePath ["Input"] "Extra"] }))

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

private def selectionOf (candidate : LiteralNumberComputation)
    (raw : RawFlatContext) :
    ComputationAlternativeSelection DecodedNumericLiteral :=
  GeneratedComputationTable.selectFirst candidate
    { read := (model.checkContext raw).read }

private def outcomeOf (candidate : LiteralNumberComputation)
    (raw : RawFlatContext) : Option FlatRuleOutcome :=
  match assembleGeneratedLiteralNumberRule model candidate with
  | .error _ => none
  | .ok rule => some (rule.evalFull evaluationWorld raw true)

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

private def crossGroupOutcome (source target : Rat) : Option FlatRuleOutcome := do
  let operation ← crossGroupNumberOperation.toOption
  let rule ← (assembleGeneratedNumericOperationRule crossGroupModel operation
    "computedCrossGroup" none messagePlan).toOption
  pure (rule.evalFull evaluationWorld (crossGroupRaw source target) true)

private def crossGroupGeneratedBoundary :
    Option (GroupPath × NumericOperandScope) := do
  let operation ← crossGroupNumberOperation.toOption
  let comparison ← (operation.generatedMismatchComparison none).toOption
  pure (comparison.rowGroup, comparison.operandScope)

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
    Option (AuthoredNumericExpr NumericComputationAtom) := do
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
  pure (rule.evalFull evaluationWorld (crossGroupRaw 3 3) true)

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
  pure (rule.evalFull evaluationWorld (crossGroupRaw 3 target) true)

private def crossGroupAggregateOutcome (target : Rat) : Option FlatRuleOutcome := do
  let operation ← crossGroupAggregateOperation.toOption
  let rule ← (assembleGeneratedNumericOperationRule crossGroupModel operation
    "computedAggregate" none messagePlan).toOption
  pure (rule.evalFull evaluationWorld (crossGroupRaw 3 target) true)

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
  pure (rule.evalFull evaluationWorld (crossGroupRaw 3 target) true)

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
  pure (rule.evalFull evaluationWorld raw true)

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
  pure (rule.evalFull evaluationWorld raw true)

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
    crossGroupOutcome 3 3 = some .notFired ∧
      crossGroupOutcome 3 4 = some (.fired crossGroupExpectedMessage) ∧
      crossGroupGeneratedBoundary =
        some (["Output"], .modelWideNonrepeatable) ∧
      crossGroupOrdinaryError =
        some (.fieldOutsideRowGroup ["Input", "Source"] ["Output"]) := by
  native_decide

/- The model-wide generated route is source-generic rather than a direct-Number exception. -/
example :
    (match crossGroupDatePartOperation with
    | .error _ => false
    | .ok operation =>
        (assembleGeneratedNumericOperationRule crossGroupModel operation
          "computedDatePart" none messagePlan).isOk) = true := by
  native_decide

/- Checked expression payloads reuse the source table: computation selects the first holding row, generated validation retains the later mismatch, and tolerance remains validation-only. -/
example :
    selectedCrossGroupExpression =
        crossGroupNumberOperation.toOption.map (fun operation => operation.core.expression) ∧
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

/- A checked aggregate operation reaches both singleton and guarded all-alternative validation through the same expression narrowing; the later aggregate mismatch remains observable without an aggregate-specific comparison wrapper. -/
example :
    crossGroupAggregateOutcome 5 = some .notFired ∧
      crossGroupAggregateOutcome 4 = some (.fired aggregateExpectedMessage) ∧
      crossGroupAggregateTableOutcome 3 =
        some (.fired aggregateExpectedMessage) := by
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
