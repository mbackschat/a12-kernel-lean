import A12Kernel.Elaboration.GeneratedComputationValidation
import A12Kernel.Elaboration.NumericComputation

/-! # Generated-computation validation shared model support -/

namespace A12Kernel.Conformance.GeneratedComputationValidation.Support.Core

open A12Kernel

def gate : FlatFieldDecl :=
  { id := 0, groupPath := ["Form"], name := "Gate",
    policy := { kind := .number { scale := 0, signed := true } } }

def target : FlatFieldDecl :=
  { id := 1, groupPath := ["Form"], name := "Target",
    policy := { kind := .number { scale := 0, signed := true } } }

def broken : FlatFieldDecl :=
  { id := 2, groupPath := ["Form"], name := "Broken",
    policy := { kind := .boolean } }

def textGuard : FlatFieldDecl :=
  { id := 3, groupPath := ["Form"], name := "TextGuard",
    policy := { kind := .string } }

def repeatedGate : FlatFieldDecl :=
  { id := 4, groupPath := ["Form", "Rows"], name := "Gate",
    policy := { kind := .number { scale := 0, signed := true } },
    repeatableScope := [10] }

def repeatedTarget : FlatFieldDecl :=
  { id := 5, groupPath := ["Form", "Rows"], name := "Target",
    policy := { kind := .number { scale := 0, signed := true } },
    repeatableScope := [10] }

def repeatedCode : FlatFieldDecl :=
  { id := 6, groupPath := ["Form", "Rows"], name := "Code",
    policy := { kind := .string },
    repeatableScope := [10] }

def model : FlatModel :=
  { fields := [gate, target, broken, textGuard] }

def repeatableModel : FlatModel :=
  { fields := [
      gate, target, broken, textGuard, repeatedGate, repeatedTarget,
      repeatedCode]
    repeatableGroups := [{ level := 10, path := ["Form", "Rows"] }] }

def repeatedGateStar : SurfaceStarFieldPath :=
  { base := .absolute
    groups := [
      { name := "Form" },
      { name := "Rows", starred := true }]
    field := "Gate" }

def repeatedTargetStar : SurfaceStarFieldPath :=
  { repeatedGateStar with field := "Target" }

def repeatedCodeStar : SurfaceStarFieldPath :=
  { repeatedGateStar with field := "Code" }

def repeatableFirstFilledHaving : SurfaceCorrelatedHaving :=
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

def repeatableAggregateOperation :
    Except NumericComputationElabError
      (CheckedNumericComputationOperation repeatableModel) :=
  elaborateNumberEntityComputationOperation repeatableModel ["Form"] target.id
    (.atom (.aggregate .sum {
      first := .star repeatedGateStar
      rest := [] }))

def repeatableFirstFilledOperation :
    Except NumericComputationElabError
      (CheckedNumericComputationOperation repeatableModel) :=
  elaborateCompleteNumericComputationOperation repeatableModel ["Form"] target.id
    (.atom (.firstFilled {
      first := .starHaving repeatedTargetStar repeatableFirstFilledHaving
      rest := [] }))

def repeatableValueCountOperation :
    Except NumericComputationElabError
      (CheckedNumericComputationOperation repeatableModel) :=
  elaborateCompleteNumericComputationOperation repeatableModel ["Form"] target.id
    (.atom (.valueCount 5 {
      first := .starHaving repeatedTargetStar repeatableFirstFilledHaving
      rest := [] }))

def repeatableTokenValueCountOperation :
    Except NumericComputationElabError
      (CheckedNumericComputationOperation repeatableModel) :=
  elaborateCompleteNumericComputationOperation repeatableModel ["Form"] target.id
    (.atom (.tokenValueCount "A" {
      first := .starHaving repeatedCodeStar .stored
        repeatableFirstFilledHaving
      rest := [] }))

def productAggregateOperation :
    Except NumericComputationElabError
      (CheckedNumericComputationOperation repeatableModel) :=
  elaborateCompleteNumericComputationOperation repeatableModel ["Form"] target.id
    (.atom (.sumOfProducts {
      left := repeatedGateStar
      right := repeatedTargetStar }))

def crossGroupSource : FlatFieldDecl :=
  { id := 20, groupPath := ["Input"], name := "Source",
    policy := { kind := .number { scale := 0, signed := true } } }

def crossGroupDate : FlatFieldDecl :=
  { id := 21, groupPath := ["Input"], name := "StartDate",
    policy := { kind := .temporal .date TemporalComponents.fullDate } }

def crossGroupExtra : FlatFieldDecl :=
  { id := 13, groupPath := ["Input"], name := "Extra",
    policy := { kind := .number { scale := 0, signed := false } } }

def crossGroupCode : FlatFieldDecl :=
  { id := 24, groupPath := ["Input"], name := "Code",
    policy := { kind := .string } }

def crossGroupNumericChoice : FlatFieldDecl :=
  { id := 25, groupPath := ["Input"], name := "NumericChoice",
    policy := { kind := .enumeration },
    enumeration := some {
      storedTokens := ["1", "2", "3"]
      categories := [{ name := "Factor", tokens := ["10", "20", "30"] }] } }

def crossGroupTarget : FlatFieldDecl :=
  { id := 22, groupPath := ["Output"], name := "Target",
    policy := { kind := .number { scale := 0, signed := true } } }

def crossGroupOtherTarget : FlatFieldDecl :=
  { id := 23, groupPath := ["Output"], name := "OtherTarget",
    policy := { kind := .number { scale := 0, signed := true } } }

def crossGroupModel : FlatModel :=
  { fields := [crossGroupSource, crossGroupDate, crossGroupExtra, crossGroupTarget,
      crossGroupOtherTarget, crossGroupCode, crossGroupNumericChoice]
    baseYear := some 2024
    timeZoneId := "Europe/Berlin" }

def absolutePath (groups : List String) (field : String) :
    SurfaceFieldPath :=
  { base := .absolute, groups, field }

def crossGroupNumberOperation :
    Except NumericComputationElabError
      (CheckedNumericComputationOperation crossGroupModel) :=
  elaborateNumericComputationOperation crossGroupModel ["Rules"]
    crossGroupTarget.id (.atom (.field (absolutePath ["Input"] "Source")))

def crossGroupDatePartOperation :
    Except NumericComputationElabError
      (CheckedNumericComputationOperation crossGroupModel) :=
  elaborateNumericComputationOperation crossGroupModel ["Rules"]
    crossGroupTarget.id
    (.abs
      (.atom (.temporalFieldPart
        (absolutePath ["Input"] "StartDate") (.date .year))))

def crossGroupDayDifferenceOperation :
    Except NumericComputationElabError
      (CheckedNumericComputationOperation crossGroupModel) :=
  elaborateNumericComputationOperation crossGroupModel ["Rules"]
    crossGroupTarget.id
    (.atom (.dayDifference (.baseYear .direct)
      (.field (absolutePath ["Input"] "StartDate"))))

def crossGroupOffsetOperation :
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

def crossGroupOtherTargetOperation :
    Except NumericComputationElabError
      (CheckedNumericComputationOperation crossGroupModel) :=
  elaborateNumericComputationOperation crossGroupModel ["Rules"]
    crossGroupOtherTarget.id
    (.atom (.field (absolutePath ["Input"] "Source")))

def crossGroupAggregateOperation :
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

def crossGroupFirstFilledOperation :
    Except NumericComputationElabError
      (CheckedNumericComputationOperation crossGroupModel) :=
  elaborateCompleteNumericComputationOperation crossGroupModel ["Rules"]
    crossGroupTarget.id
    (.atom (.firstFilled {
      first := .field (absolutePath ["Input"] "Source")
      rest := [.field (absolutePath ["Input"] "Extra")] }))

def crossGroupStringRangeOperation :
    Except NumericComputationElabError
      (CheckedNumericComputationOperation crossGroupModel) :=
  elaborateNumericComputationOperation crossGroupModel ["Rules"]
    crossGroupTarget.id
    (.abs (.atom (.stringRange (absolutePath ["Input"] "Code") 1 2)))

def crossGroupFieldValueAsNumberOperation :
    Except NumericComputationElabError
      (CheckedNumericComputationOperation crossGroupModel) :=
  elaborateNumericComputationOperation crossGroupModel ["Rules"]
    crossGroupTarget.id
    (.round .halfUp omittedRoundingPlaces
      (.atom (.fieldValueAsNumber
        (.category (absolutePath ["Input"] "NumericChoice") "Factor"))))

def crossGroupTokenCategoryCountOperation :
    Except NumericComputationElabError
      (CheckedNumericComputationOperation crossGroupModel) :=
  elaborateCompleteNumericComputationOperation crossGroupModel ["Rules"]
    crossGroupTarget.id
    (.atom (.tokenValueCount "10" {
      first := .field (.category
        (absolutePath ["Input"] "NumericChoice") "Factor")
      rest := [
        .field (.direct (absolutePath ["Input"] "Code"))] }))

def messagePlan : MessageRenderPlan :=
  { parts := [.text "Target disagrees with the computation table"] }

def text : ResolvedMessageText :=
  messagePlan.render

def literal (value : Rat) : DecodedNumericLiteral :=
  { value, authoredScale := 0 }

def alternative (precondition : ComputationCondition)
    (operation : Rat) : LiteralNumberComputationAlternative :=
  { precondition, operation := literal operation }

def guardedComputation (first second : LiteralNumberComputationAlternative)
    (remaining : List LiteralNumberComputationAlternative := []) :
    LiteralNumberComputation :=
  { targetField := target.id
    name := "computedTarget"
    alternatives := .guarded {
      first
      second
      remaining }
    messagePlan }

def computation (firstGuard : ComputationCondition) (firstValue : Rat)
    (secondGuard : ComputationCondition) (secondValue : Rat) :
    LiteralNumberComputation :=
  guardedComputation (alternative firstGuard firstValue)
    (alternative secondGuard secondValue)

def singletonComputation (precondition : Option ComputationCondition)
    (value : Rat) : LiteralNumberComputation :=
  { targetField := target.id
    name := "computedTarget"
    alternatives := .singleton {
      precondition
      operation := literal value }
    messagePlan }

def bothFilled (targetCell : RawCell) : RawFlatContext where
  read field :=
    if field = gate.id then .parsed (.num 7)
    else if field = target.id then targetCell
    else .empty

def gateEmptyTargetOne : RawFlatContext where
  read field :=
    if field = target.id then .parsed (.num 1)
    else .empty

def textGuardTargetOne (textCell : RawCell) : RawFlatContext where
  read field :=
    if field = textGuard.id then textCell
    else if field = target.id then .parsed (.num 1)
    else .empty

def brokenAndHealthy : RawFlatContext where
  read field :=
    if field = gate.id then .parsed (.num 7)
    else if field = target.id then .parsed (.num 1)
    else if field = broken.id then .rejected .malformed
    else .empty

def evaluationWorld : World :=
  { now := { epochMillis := 0 } }

def repeatableDocument (rows : List RowIndex) : Document :=
  { instantiatedRows := rows.map fun row => { group := 10, path := [row] }
    rawCells := fun _ => none }

def checkedNumber (raw : RawCell) : CheckedCell :=
  formalCheck { kind := .number { scale := 0, signed := true } } raw

def repeatableRead (outerGate : CheckedCell)
    (filterRows targetRows : RowIndex → CheckedCell)
    (environment : Env) (field : FieldId) : CheckedCell :=
  if field == gate.id then outerGate
  else
    match environment with
    | [(10, row)] =>
      if field == repeatedGate.id then filterRows row
        else if field == repeatedTarget.id || field == repeatedCode.id then
          targetRows row
        else malformedCheckedCell
    | _ => malformedCheckedCell

def repeatableRaw (outerGate targetCell : RawCell) : RawFlatContext where
  read field :=
    if field == gate.id then outerGate
    else if field == target.id then targetCell
    else .empty

def repeatableGeneratedRule?
    (operationResult : Except NumericComputationElabError
      (CheckedNumericComputationOperation repeatableModel))
    (errorCode : String) :
    Option (CheckedResolvedValidationRule repeatableModel) := do
  let operation ← operationResult.toOption
  (assembleGeneratedNumericOperationRule repeatableModel operation
    errorCode none messagePlan).toOption

def repeatableGeneratedScalarCapability
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

end A12Kernel.Conformance.GeneratedComputationValidation.Support.Core
