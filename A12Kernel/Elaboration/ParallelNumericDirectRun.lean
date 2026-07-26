import A12Kernel.Elaboration.NumericComputation.Evaluation
import A12Kernel.Elaboration.ParallelComputationClearing

/-! # Isolated direct parallel Number run

This bounded capsule checks one optionally guarded Number expression whose field atoms are model-owned Number declarations addressable from one exact-text parallel route's selected operand-group environment. It reuses the shared authored numeric tree, lowering, operation admission, authoring rules, scale summary, target policy, and evaluator; the route remains the sole owner of the index join and invalid-index disposition. Because the run has exactly one computed target and every admitted operand lies in the distinct joined group, those operands are source fields rather than unresolved computed dependencies. Execution enumerates existing target rows only, omits every target covered by an invalid-index post-loop mark, reads clean unmatched operands as numeric zero, and retains each evaluated result at its exact target address. Presence guards may read any model-owned field addressable from that same environment and remain kind-neutral; additional indexed groups, multi-computation scheduling, and broader repeatable overlays remain separate. -/

namespace A12Kernel

inductive ParallelNumericDirectPlanError where
  | route (error : ParallelComputationPlanError)
  | guardNotLimitedToOperand
  | expressionResolve (error : ResolveError)
  | expressionNotLimitedToOperand
  | unsupportedExpression
  | authoring (result : NumericAuthoringCheck)
  | operandFrameOutsideTarget (scope : List RepeatableLevel)
  | operationScaleMismatch
      (targetScale : Nat) (operation : NumericScaleSummary)
  deriving Repr, DecidableEq

/-- Admit one presence-guard field exactly when the model-owned declaration is addressable from the route's selected operand-group environment. Presence remains kind-neutral. -/
def CheckedParallelNumericClearingPlan.admitsGuardField
    (route : CheckedParallelNumericClearingPlan model)
    (field : FieldId) : Bool :=
  match model.lookupUniqueId field with
  | .ok declaration =>
      declaration.repeatableScope ==
          route.operandDeclaration.repeatableScope &&
        route.groups.rightGroup.path.isPrefixOf declaration.groupPath
  | .error _ => false

/-- Whether every leaf of an optional bounded guard reuses the route's selected operand-group environment. -/
def parallelNumericDirectGuardAdmitted
    (route : CheckedParallelNumericClearingPlan model) :
    Option ComputationCondition → Bool
  | none => true
  | some condition => referencesOnly condition
where
  referencesOnly : ComputationCondition → Bool
    | .leaf (.fieldFilled field) | .leaf (.fieldNotFilled field) =>
        route.admitsGuardField field
    | .and left right | .or left right =>
        referencesOnly left && referencesOnly right

private def parallelNumericGuardFields :
    Option ComputationCondition → List FieldId
  | none => []
  | some condition => fields condition
where
  fields : ComputationCondition → List FieldId
    | .leaf (.fieldFilled field) | .leaf (.fieldNotFilled field) => [field]
    | .and left right | .or left right => fields left ++ fields right

/-- Admit one expression field exactly when it is a model-owned Number declaration addressable from the route's selected operand-group environment. Nested nonrepeatable groups remain legal; another repeatable or indexed scope does not. -/
def CheckedParallelNumericClearingPlan.admitsExpressionDeclaration
    (route : CheckedParallelNumericClearingPlan model)
    (declaration : FlatFieldDecl) : Bool :=
  match model.lookupUniqueId declaration.id with
  | .ok admitted =>
      admitted == declaration &&
        declaration.toNumberField?.isSome &&
        declaration.repeatableScope ==
          route.operandDeclaration.repeatableScope &&
        route.groups.rightGroup.path.isPrefixOf declaration.groupPath
  | .error _ => false

/-- Collect declarations only to fetch structurally checked carriers from the selected environment. Semantic observation and left-to-right poison remain with the shared expression evaluator. -/
private def parallelNumericExpressionDeclarations :
    AuthoredNumericExpr FlatFieldDecl → List FlatFieldDecl
  | .atom declaration => [declaration]
  | .literal _ => []
  | .group body => parallelNumericExpressionDeclarations body
  | .binary _ left right | .power left right | .extremum _ left right =>
      parallelNumericExpressionDeclarations left ++
        parallelNumericExpressionDeclarations right
  | .abs body | .extremumCall _ body =>
      parallelNumericExpressionDeclarations body
  | .round _ _ body => parallelNumericExpressionDeclarations body

/-- One exact target-addressed rich outcome from the direct parallel computation. -/
structure ParallelNumericDirectOutcome where
  address : CellAddr
  outcome : NumericTargetOutcome
  deriving Repr, DecidableEq

/-- The complete one-computation inventory for one checked optionally guarded Number operation over the existing parallel route certificate. -/
structure CheckedIsolatedParallelNumericDirectRun (model : FlatModel) where
  private mk ::
  route : CheckedParallelNumericClearingPlan model
  precondition : Option ComputationCondition
  suppressExactScaleWarning : Bool
  expression : AuthoredNumericExpr FlatFieldDecl
  guardAdmitted :
    parallelNumericDirectGuardAdmitted route precondition = true
  expressionUsesOperand : expression.hasAtom = true
  expressionOperandsAdmitted :
    expression.allAtoms route.admitsExpressionDeclaration = true
  expressionAdmitted :
    expression.isAdmittedResolvedNumericOperation = true
  expressionAuthoring :
    expression.numericOperationAuthoringCheck = .accepted
  operandScopeAvailable : (match route.groups.outerScopePlan with
      | .framed .right _ _ => false
      | .common _ | .framed .left _ _ => true) = true
  operationScale : NumericScaleSummary
  operationScaleOwned :
    expression.summary? FlatFieldDecl.numericScaleSummary =
      some operationScale
  operationScaleAdmitted :
    exactNumericScaleComparisonAllowedWithSuppression
      suppressExactScaleWarning
      (.field route.target.info.scale)
      operationScale = true

namespace CheckedIsolatedParallelNumericDirectRun

def WellFormed
    (checked : CheckedIsolatedParallelNumericDirectRun model) : Prop :=
  checked.route.WellFormed ∧
    parallelNumericDirectGuardAdmitted
      checked.route checked.precondition = true ∧
    checked.expression.hasAtom = true ∧
    checked.expression.allAtoms
      checked.route.admitsExpressionDeclaration = true ∧
    checked.expression.isAdmittedResolvedNumericOperation = true ∧
    checked.expression.numericOperationAuthoringCheck = .accepted ∧
    (match checked.route.groups.outerScopePlan with
      | .framed .right _ _ => false
      | .common _ | .framed .left _ _ => true) = true ∧
    checked.expression.summary? FlatFieldDecl.numericScaleSummary =
      some checked.operationScale ∧
    exactNumericScaleComparisonAllowedWithSuppression
      checked.suppressExactScaleWarning
      (.field checked.route.target.info.scale)
      checked.operationScale = true

inductive ExecutionError where
  | marking (side : ParallelComputationIndexSide)
      (error : ParallelComputationMarkingError)
  | targetRows (error : ActualRowEnvironmentError)
  | environment (error : EnvBindingError)
  | indexColumn (side : ParallelComputationIndexSide)
      (error : CheckedIndexColumnError)
  | missingTargetIndex (address : CellAddr)
  | document (error : CheckedDocumentError)
  | numeric (error : NumericComputationFault)
  | unsupportedTarget (fault : NumericTargetCheckFault)
  deriving Repr, DecidableEq

/-- Resolve the joined operand environment once and fetch every admitted declaration at its own field identity. `none` is a clean unmatched index key; fetching checked carriers does not itself observe their formal findings. -/
private def operandCells
    (checked : CheckedIsolatedParallelNumericDirectRun model)
    (preliminary : CheckedIndexPreliminary model)
    (targetEnvironment : Env) (key : SemanticIndexKey) :
    Except ExecutionError (Option (List (FieldId × CheckedCell))) := do
  let operandColumn ←
    preliminary.resolveIndexColumn
      checked.route.groups.rightGroup targetEnvironment
      |>.mapError (ExecutionError.indexColumn .operand)
  match operandColumn.entries.find? fun entry => entry.key == key with
  | none => pure none
  | some entry =>
      let guardDeclarations :=
        (parallelNumericGuardFields checked.precondition).filterMap fun field =>
          match model.lookupUniqueId field with
          | .ok declaration => some declaration
          | .error _ => none
      let declarations :=
        (checked.route.operandDeclaration ::
          parallelNumericExpressionDeclarations checked.expression ++
          guardDeclarations).eraseDups
      let cells ← declarations.mapM fun declaration => do
        let path ←
          entry.environment.pathForScope declaration.repeatableScope
            |>.mapError ExecutionError.environment
        let cell ← preliminary.base.read {
          field := declaration.id
          path
        } |>.mapError ExecutionError.document
        pure (declaration.id, cell)
      pure (some cells)

private def executeTarget
    (checked : CheckedIsolatedParallelNumericDirectRun model)
    (preliminary : CheckedIndexPreliminary model)
    (targetEnvironment : Env) (address : CellAddr) :
    Except ExecutionError ParallelNumericDirectOutcome := do
  let targetColumn ←
    preliminary.resolveIndexColumn
      checked.route.groups.leftGroup targetEnvironment
      |>.mapError (ExecutionError.indexColumn .target)
  let targetEntry ← match targetColumn.entries.find? fun entry =>
      entry.environment == targetEnvironment with
    | some entry => pure entry
    | none => throw (.missingTargetIndex address)
  let cells ← checked.operandCells preliminary
    targetEnvironment targetEntry.key
  let context : ScalarComputationContext := {
    read := fun field =>
      match cells with
      | none => { rawPresent := false, parsed := none, findings := [] }
      | some resolved =>
          match resolved.find? fun cell => cell.1 == field with
          | some cell => cell.2
          | none => malformedCheckedCell
  }
  let guardResult := match checked.precondition with
    | none => ComputationConditionResult.holds
    | some guard => guard.eval context
  match guardResult with
  | .notTrue => pure { address, outcome := .noValue }
  | .poison cause =>
      pure { address, outcome := .inheritedPoison cause }
  | .holds =>
      let value ← checked.expression.evaluateComputation context
          |>.mapError .numeric
      let checkedTarget :=
        if checked.suppressExactScaleWarning then
          checked.route.targetPolicy.checkWithScaleWarningSuppressed value
        else
          checked.route.targetPolicy.check value
      match checkedTarget with
      | .supported outcome => pure { address, outcome }
      | .unsupported fault => throw (.unsupportedTarget fault)

/-- Execute every existing target row not covered by either side's checked invalid-index marks. Collection order is the checked document's private canonicalization. -/
def execute
    (checked : CheckedIsolatedParallelNumericDirectRun model)
    (preliminary : CheckedIndexPreliminary model) :
    Except ExecutionError (List ParallelNumericDirectOutcome) := do
  let coverage ←
    checked.route.targetCoverage preliminary
      |>.mapError fun
        | .marking side error => .marking side error
        | .targetRows error => .targetRows error
        | .targetEnvironment error => .environment error
  let candidates ← coverage.mapM fun target => do
    if target.indexInvalid then
      pure none
    else
      some <$> checked.executeTarget preliminary
        target.environment target.address
  pure (candidates.filterMap id)

end CheckedIsolatedParallelNumericDirectRun

/-- Resolve one bounded expression atom to a Number declaration addressable from the route-owned joined operand group. This is a certificate construction over the shared numeric tree, not a second evaluator or index join. -/
private def FlatModel.resolveParallelNumericDirectExpression
    (model : FlatModel) (declaringGroup : GroupPath)
    (route : CheckedParallelNumericClearingPlan model)
    (expression : AuthoredNumericExpr SurfaceNumericAtom) :
    Except ParallelNumericDirectPlanError
      (AuthoredNumericExpr FlatFieldDecl) :=
  expression.mapM fun
    | .field reference => do
        let declaration ←
          model.resolveFieldDeclarationUnchecked declaringGroup reference
            |>.mapError ParallelNumericDirectPlanError.expressionResolve
        if route.admitsExpressionDeclaration declaration then
          pure declaration
        else
          throw .expressionNotLimitedToOperand
    | _ => throw .expressionNotLimitedToOperand

/-- Check one optionally guarded Number operation without reimplementing the parallel route, numeric lowering, operation admission, authoring checks, or scale gate. Every expression atom must be a Number declaration addressable from the selected operand-group environment; every kind-neutral guard leaf must be a model-owned declaration addressable from that same environment. The scale-warning directive defaults to false; when true it selects both the shared suppressed static gate and the existing warning-suppressed target check, but never changes expression arithmetic. -/
def checkIsolatedParallelNumericExpressionRunWithGuard (model : FlatModel)
    (declaringGroup : GroupPath) (targetField : FieldId)
    (operandReference : SurfaceFieldPath)
    (expression : AuthoredNumericExpr SurfaceNumericAtom)
    (precondition : Option ComputationCondition)
    (suppressExactScaleWarning : Bool := false) :
    Except ParallelNumericDirectPlanError
      (CheckedIsolatedParallelNumericDirectRun model) := do
  let route ←
    checkParallelNumericComputationClearingPlan
      model declaringGroup targetField operandReference
      |>.mapError .route
  let resolved ←
    model.resolveParallelNumericDirectExpression
      declaringGroup route expression
  if usesOperand : resolved.hasAtom = true then
    if operandsAdmitted :
        resolved.allAtoms route.admitsExpressionDeclaration = true then
      if expressionAdmitted :
          resolved.isAdmittedResolvedNumericOperation = true then
        match authoring : resolved.numericOperationAuthoringCheck with
        | .accepted =>
          match scaleOwned :
              resolved.summary? FlatFieldDecl.numericScaleSummary with
          | none => throw .unsupportedExpression
          | some operationScale =>
            if guardAdmitted :
                parallelNumericDirectGuardAdmitted
                  route precondition = true then
              if scopeAvailable :
                  (match route.groups.outerScopePlan with
                    | .framed .right _ _ => false
                    | .common _ | .framed .left _ _ => true) = true then
                if scaleAdmitted :
                    exactNumericScaleComparisonAllowedWithSuppression
                      suppressExactScaleWarning
                      (.field route.target.info.scale)
                      operationScale = true then
                  pure (CheckedIsolatedParallelNumericDirectRun.mk
                    route precondition suppressExactScaleWarning resolved
                    guardAdmitted usesOperand operandsAdmitted expressionAdmitted
                    authoring scopeAvailable operationScale scaleOwned
                    scaleAdmitted)
                else
                  throw (.operationScaleMismatch
                    route.target.info.scale operationScale)
              else
                throw (.operandFrameOutsideTarget
                  (model.repeatableScopeForGroupPath
                    route.groups.rightGroup.path))
            else
              throw .guardNotLimitedToOperand
        | result => throw (.authoring result)
      else
        throw .unsupportedExpression
    else
      throw .expressionNotLimitedToOperand
  else
    throw .expressionNotLimitedToOperand

/-- Check one optionally guarded direct Number copy as the atom-only specialization of the shared expression route. -/
def checkIsolatedParallelNumericDirectRunWithGuard (model : FlatModel)
    (declaringGroup : GroupPath) (targetField : FieldId)
    (operandReference : SurfaceFieldPath)
    (precondition : Option ComputationCondition) :
    Except ParallelNumericDirectPlanError
      (CheckedIsolatedParallelNumericDirectRun model) :=
  checkIsolatedParallelNumericExpressionRunWithGuard model declaringGroup
    targetField operandReference (.atom (.field operandReference)) precondition

/-- Check the original unguarded direct-copy fragment. -/
def checkIsolatedParallelNumericDirectRun (model : FlatModel)
    (declaringGroup : GroupPath) (targetField : FieldId)
    (operandReference : SurfaceFieldPath) :
    Except ParallelNumericDirectPlanError
      (CheckedIsolatedParallelNumericDirectRun model) :=
  checkIsolatedParallelNumericDirectRunWithGuard model declaringGroup
    targetField operandReference none

end A12Kernel
