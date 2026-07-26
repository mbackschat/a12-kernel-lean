import A12Kernel.Elaboration.NumericComputation.Evaluation
import A12Kernel.Elaboration.ParallelComputationClearing

/-! # Isolated direct parallel Number run

This bounded capsule checks one optionally guarded Number expression whose field atoms are model-owned declarations addressable through exact-text parallel routes to one target group. It reuses the shared authored numeric tree, lowering, operation admission, authoring rules, scale summary, target policy, checked pairwise join, and evaluator. Because the run has exactly one computed target, every admitted operand is a source field rather than an unresolved computed dependency. Execution enumerates existing target rows only, omits every target covered by any participating group's invalid-index post-loop mark, reads clean unmatched operands as numeric zero, and retains each evaluated result at its exact target address. Presence guards remain kind-neutral; every distinct indexed group referenced by either the operation or its guard participates statically, while guard evaluation retains the existing lazy `And`/`Or` observation semantics. Multi-computation scheduling and broader repeatable overlays remain separate. -/

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

/-- Admit one presence-guard field exactly when the model-owned declaration is addressable from the route's observed-group environment. Presence remains kind-neutral. -/
def CheckedParallelNumericTargetRoute.admitsGuardField
    (route : CheckedParallelNumericTargetRoute model)
    (field : FieldId) : Bool :=
  match model.lookupUniqueId field with
  | .ok declaration =>
      declaration.repeatableScope ==
          route.sourceDeclaration.repeatableScope &&
        route.groups.rightGroup.path.isPrefixOf declaration.groupPath
  | .error _ => false

/-- Preserve the original Number-specialized admission surface as the kind-neutral route projection. -/
def CheckedParallelNumericClearingPlan.admitsGuardField
    (route : CheckedParallelNumericClearingPlan model)
    (field : FieldId) : Bool :=
  route.asTargetRoute.admitsGuardField field

/-- Whether every guard leaf belongs to one statically participating checked route. -/
def parallelNumericDirectGuardAdmitted
    (routes : List (CheckedParallelNumericTargetRoute model)) :
    Option ComputationCondition → Bool
  | none => true
  | some condition => referencesOnly condition
where
  referencesOnly : ComputationCondition → Bool
    | .leaf (.fieldFilled field) | .leaf (.fieldNotFilled field) =>
        routes.any fun route => route.admitsGuardField field
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

/-- Admit one expression field exactly when it is a model-owned Number declaration addressable from the route's observed-group environment. Nested nonrepeatable groups remain legal; another repeatable or indexed scope does not. -/
def CheckedParallelNumericTargetRoute.admitsExpressionDeclaration
    (route : CheckedParallelNumericTargetRoute model)
    (declaration : FlatFieldDecl) : Bool :=
  match model.lookupUniqueId declaration.id with
  | .ok admitted =>
      admitted == declaration &&
        declaration.toNumberField?.isSome &&
        declaration.repeatableScope ==
          route.sourceDeclaration.repeatableScope &&
        route.groups.rightGroup.path.isPrefixOf declaration.groupPath
  | .error _ => false

def CheckedParallelNumericClearingPlan.admitsExpressionDeclaration
    (route : CheckedParallelNumericClearingPlan model)
    (declaration : FlatFieldDecl) : Bool :=
  route.asTargetRoute.admitsExpressionDeclaration declaration

/-- Collect authored atoms only to construct checked read routes and fetch carriers. Evaluation retains the original expression tree. -/
private def parallelNumericExpressionAtoms :
    AuthoredNumericExpr Atom → List Atom
  | .atom atom => [atom]
  | .literal _ => []
  | .group body => parallelNumericExpressionAtoms body
  | .binary _ left right | .power left right | .extremum _ left right =>
      parallelNumericExpressionAtoms left ++
        parallelNumericExpressionAtoms right
  | .abs body | .extremumCall _ body =>
      parallelNumericExpressionAtoms body
  | .round _ _ body => parallelNumericExpressionAtoms body

private def parallelNumericRouteScopeAvailable
    (route : CheckedParallelNumericTargetRoute model) : Bool :=
  match route.groups.outerScopePlan with
  | .framed .right _ _ => false
  | .common _ | .framed .left _ _ => true

private def parallelNumericRoutesAdmitExpression
    (routes : List (CheckedParallelNumericTargetRoute model))
    (declaration : FlatFieldDecl) : Bool :=
  routes.any fun route => route.admitsExpressionDeclaration declaration

/-- One exact target-addressed rich outcome from the direct parallel computation. -/
structure ParallelNumericDirectOutcome where
  address : CellAddr
  outcome : NumericTargetOutcome
  deriving Repr, DecidableEq

/-- The complete one-computation inventory for one checked optionally guarded Number operation over the existing parallel route certificate. -/
structure CheckedIsolatedParallelNumericDirectRun (model : FlatModel) where
  private mk ::
  route : CheckedParallelNumericClearingPlan model
  additionalRoutes : List (CheckedParallelNumericTargetRoute model)
  precondition : Option ComputationCondition
  suppressExactScaleWarning : Bool
  expression : AuthoredNumericExpr FlatFieldDecl
  routeTargetsCoherent :
    (additionalRoutes.all fun additional =>
      additional.targetDeclaration == route.targetDeclaration) = true
  guardAdmitted :
    parallelNumericDirectGuardAdmitted
      (route.asTargetRoute :: additionalRoutes) precondition = true
  expressionUsesOperand :
    expression.anyAtom route.admitsExpressionDeclaration = true
  expressionOperandsAdmitted :
    expression.allAtoms
      (parallelNumericRoutesAdmitExpression
        (route.asTargetRoute :: additionalRoutes)) = true
  expressionAdmitted :
    expression.isAdmittedResolvedNumericOperation = true
  expressionAuthoring :
    expression.numericOperationAuthoringCheck = .accepted
  operandScopesAvailable :
    (route.asTargetRoute :: additionalRoutes).all
      parallelNumericRouteScopeAvailable = true
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

/-- Every distinct operand group is represented by one route to the same checked target. -/
def operandRoutes
    (checked : CheckedIsolatedParallelNumericDirectRun model) :
    List (CheckedParallelNumericTargetRoute model) :=
  checked.route.asTargetRoute :: checked.additionalRoutes

/-- Whether the guard or resolved numeric expression reads one exact field. -/
def referencesField
    (checked : CheckedIsolatedParallelNumericDirectRun model)
    (field : FieldId) : Bool :=
  (checked.precondition.map (·.referencesField field)).getD false ||
    checked.expression.anyAtom fun declaration => declaration.id == field

def WellFormed
    (checked : CheckedIsolatedParallelNumericDirectRun model) : Prop :=
  checked.route.WellFormed ∧
    (∀ additional ∈ checked.additionalRoutes,
      additional.WellFormed) ∧
    checked.additionalRoutes.all (fun additional =>
      additional.targetDeclaration ==
        checked.route.targetDeclaration) = true ∧
    parallelNumericDirectGuardAdmitted
      checked.operandRoutes checked.precondition = true ∧
    checked.expression.anyAtom
      checked.route.admitsExpressionDeclaration = true ∧
    checked.expression.allAtoms
      (parallelNumericRoutesAdmitExpression
        checked.operandRoutes) = true ∧
    checked.expression.isAdmittedResolvedNumericOperation = true ∧
    checked.expression.numericOperationAuthoringCheck = .accepted ∧
    checked.operandRoutes.all
      parallelNumericRouteScopeAvailable = true ∧
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

/-- Resolve one joined operand environment and fetch every declaration owned by that route. A clean unmatched key supplies explicit empty carriers; fetching carriers does not observe their formal findings. -/
private def operandCellsForRoute
    (route : CheckedParallelNumericTargetRoute model)
    (declarations : List FlatFieldDecl)
    (preliminary : CheckedIndexPreliminary model)
    (targetEnvironment : Env) (key : SemanticIndexKey) :
    Except ExecutionError (List (FieldId × CheckedCell)) := do
  let operandColumn ←
    preliminary.resolveIndexColumn
      route.groups.rightGroup targetEnvironment
      |>.mapError (ExecutionError.indexColumn .operand)
  match operandColumn.entries.find? fun entry => entry.key == key with
  | none =>
      pure (declarations.map fun declaration =>
        (declaration.id,
          { rawPresent := false, parsed := none, findings := [] }))
  | some entry =>
      declarations.mapM fun declaration => do
        let path ←
          entry.environment.pathForScope declaration.repeatableScope
            |>.mapError ExecutionError.environment
        let cell ← preliminary.base.read {
          field := declaration.id
          path
        } |>.mapError ExecutionError.document
        pure (declaration.id, cell)

/-- Fetch each admitted field through the sole route for its indexed group. Carrier construction remains observation-free so a table can collect all row inputs before first-selected evaluation. -/
def operandCells
    (checked : CheckedIsolatedParallelNumericDirectRun model)
    (preliminary : CheckedIndexPreliminary model)
    (targetEnvironment : Env) (key : SemanticIndexKey) :
    Except ExecutionError (List (FieldId × CheckedCell)) := do
  let guardDeclarations :=
    (parallelNumericGuardFields checked.precondition).filterMap fun field =>
      match model.lookupUniqueId field with
      | .ok declaration => some declaration
      | .error _ => none
  let declarations :=
    (checked.route.operandDeclaration ::
      parallelNumericExpressionAtoms checked.expression ++
      guardDeclarations).eraseDups
  let nested ← checked.operandRoutes.mapM fun route => do
    let owned := declarations.filter fun declaration =>
      route.admitsExpressionDeclaration declaration ||
        route.admitsGuardField declaration.id
    operandCellsForRoute route owned preliminary
      targetEnvironment key
  pure nested.flatten

/-- Resolve the target's checked semantic key at one actual target environment. The exact address is retained only for structural failure reporting. -/
def targetKeyFor
    (checked : CheckedIsolatedParallelNumericDirectRun model)
    (preliminary : CheckedIndexPreliminary model)
    (targetEnvironment : Env) (address : CellAddr) :
    Except ExecutionError SemanticIndexKey := do
  let targetColumn ←
    preliminary.resolveIndexColumn
      checked.route.groups.leftGroup targetEnvironment
      |>.mapError (ExecutionError.indexColumn .target)
  match targetColumn.entries.find? fun entry =>
      entry.environment == targetEnvironment with
  | some entry => pure entry.key
  | none => throw (.missingTargetIndex address)

/-- Evaluate an already-selected checked operation against one addressed carrier context. Guard selection remains with the caller, allowing both the singleton run and a wider first-selected table to share target semantics without inspecting outcomes to recover selection. -/
def evaluateSelected
    (checked : CheckedIsolatedParallelNumericDirectRun model)
    (context : ScalarComputationContext) :
    Except ExecutionError NumericTargetOutcome := do
  let value ← checked.expression.evaluateComputation context
      |>.mapError .numeric
  let checkedTarget :=
    if checked.suppressExactScaleWarning then
      checked.route.targetPolicy.checkWithScaleWarningSuppressed value
    else
      checked.route.targetPolicy.check value
  match checkedTarget with
  | .supported outcome => pure outcome
  | .unsupported fault => throw (.unsupportedTarget fault)

private def executeTarget
    (checked : CheckedIsolatedParallelNumericDirectRun model)
    (preliminary : CheckedIndexPreliminary model)
    (targetEnvironment : Env) (address : CellAddr) :
    Except ExecutionError ParallelNumericDirectOutcome := do
  let key ← checked.targetKeyFor preliminary targetEnvironment address
  let cells ← checked.operandCells preliminary
    targetEnvironment key
  let context : ScalarComputationContext := {
    read := fun field =>
      match cells.find? fun cell => cell.1 == field with
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
      pure { address, outcome := ← checked.evaluateSelected context }

/-- Derive executable target coverage from every statically participating route. Additional routes contribute only invalidity; the primary route owns the canonical actual target inventory. -/
def executableTargets
    (primary : CheckedParallelNumericTargetRoute model)
    (additional : List (CheckedParallelNumericTargetRoute model))
    (preliminary : CheckedIndexPreliminary model) :
    Except ExecutionError (List ParallelNumericTargetCoverage) := do
  let primaryCoverage ←
    primary.targetCoverage preliminary
      |>.mapError fun
        | .marking side error => .marking side error
        | .targetRows error => .targetRows error
        | .targetEnvironment error => .environment error
  let additionalCoverage ← additional.mapM fun route =>
    route.targetCoverage preliminary
      |>.mapError fun
        | .marking side error => .marking side error
        | .targetRows error => .targetRows error
        | .targetEnvironment error => .environment error
  let additionallyInvalid :=
    (additionalCoverage.flatten.filter (·.indexInvalid)).map (·.address)
  pure (primaryCoverage.filter fun target =>
    !target.indexInvalid &&
      !additionallyInvalid.contains target.address)

/-- Execute every existing target row not covered by any participating group's checked invalid-index marks. Collection order is the checked document's private canonicalization. -/
def execute
    (checked : CheckedIsolatedParallelNumericDirectRun model)
    (preliminary : CheckedIndexPreliminary model) :
    Except ExecutionError (List ParallelNumericDirectOutcome) := do
  let targets ← executableTargets checked.route.asTargetRoute
    checked.additionalRoutes preliminary
  targets.mapM fun target =>
    checked.executeTarget preliminary target.environment target.address

end CheckedIsolatedParallelNumericDirectRun

private def appendParallelNumericRouteIfNew
    (routes : List (CheckedParallelNumericTargetRoute model))
    (candidate : CheckedParallelNumericTargetRoute model) :
    List (CheckedParallelNumericTargetRoute model) :=
  if routes.any fun route =>
      route.groups.rightGroup.path == candidate.groups.rightGroup.path then
    routes
  else
    routes ++ [candidate]

/-- Resolve every field atom and retain one checked target-to-operand route per participating indexed group. This is a certificate construction over the shared numeric tree, not a second evaluator or join. -/
private def FlatModel.resolveParallelNumericDirectExpression
    (model : FlatModel) (declaringGroup : GroupPath)
    (route : CheckedParallelNumericClearingPlan model)
    (expression : AuthoredNumericExpr SurfaceNumericAtom) :
    Except ParallelNumericDirectPlanError
      (AuthoredNumericExpr FlatFieldDecl ×
        List (CheckedParallelNumericTargetRoute model)) := do
  let routed ← expression.mapM fun
    | .field reference =>
        match checkParallelNumericComputationClearingPlan
            model declaringGroup route.targetField reference with
        | .ok checked => pure checked
        | .error (.operandResolve error) =>
            throw (.expressionResolve error)
        | .error (.join (.incompatibleGroups _ _)) =>
            throw .expressionNotLimitedToOperand
        | .error error => throw (.route error)
    | _ => throw .expressionNotLimitedToOperand
  let routes :=
    (parallelNumericExpressionAtoms routed).foldl
      (fun routes candidate =>
        appendParallelNumericRouteIfNew routes candidate.asTargetRoute)
      [route.asTargetRoute]
  pure (routed.map (·.operandDeclaration), routes.drop 1)

/-- Add one checked route for every guard field whose indexed group is not already represented. Guard evaluation remains lazy; this construction records only the groups whose index columns participate in the generated loop. -/
private def FlatModel.resolveParallelNumericGuardRoutes
    (model : FlatModel) (declaringGroup : GroupPath)
    (primary : CheckedParallelNumericTargetRoute model)
    (additionalRoutes : List (CheckedParallelNumericTargetRoute model))
    (precondition : Option ComputationCondition) :
    Except ParallelNumericDirectPlanError
      (List (CheckedParallelNumericTargetRoute model)) := do
  let routes ← (parallelNumericGuardFields precondition).foldlM
    (fun (routes : List (CheckedParallelNumericTargetRoute model))
        field => do
      if routes.any fun route => route.admitsGuardField field then
        pure routes
      else
        let declaration ← match model.lookupUniqueId field with
          | .ok declaration => pure declaration
          | .error _ =>
              throw ParallelNumericDirectPlanError.guardNotLimitedToOperand
        let reference : SurfaceFieldPath := {
          base := .absolute
          groups := declaration.groupPath
          field := declaration.name
        }
        match checkParallelNumericTargetRoute
            model declaringGroup primary.targetField reference with
        | .ok route =>
            pure (appendParallelNumericRouteIfNew routes route)
        | .error (.join (.incompatibleGroups _ _))
        | .error (.missingIndexedAncestor _) =>
            throw ParallelNumericDirectPlanError.guardNotLimitedToOperand
        | .error error =>
            throw (ParallelNumericDirectPlanError.route error))
    (primary :: additionalRoutes)
  pure (routes.drop 1)

/-- Check one optionally guarded Number operation without reimplementing pairwise joins, numeric lowering, operation admission, authoring checks, or the scale gate. Each distinct indexed group referenced by the expression or guard receives one route to the same target. The scale-warning directive defaults to false; when true it selects both the shared suppressed static gate and the existing warning-suppressed target check, but never changes expression arithmetic. -/
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
  let (resolved, expressionRoutes) ←
    model.resolveParallelNumericDirectExpression
      declaringGroup route expression
  let additionalRoutes ←
    model.resolveParallelNumericGuardRoutes declaringGroup
      route.asTargetRoute expressionRoutes precondition
  let operandRoutes := route.asTargetRoute :: additionalRoutes
  if usesOperand :
      resolved.anyAtom route.admitsExpressionDeclaration = true then
    if targetsCoherent :
        additionalRoutes.all (fun additional =>
          additional.targetDeclaration ==
            route.targetDeclaration) = true then
      if operandsAdmitted :
          resolved.allAtoms
            (parallelNumericRoutesAdmitExpression operandRoutes) = true then
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
                    operandRoutes precondition = true then
                if scopeAvailable :
                    operandRoutes.all
                      parallelNumericRouteScopeAvailable = true then
                  if scaleAdmitted :
                      exactNumericScaleComparisonAllowedWithSuppression
                        suppressExactScaleWarning
                        (.field route.target.info.scale)
                        operationScale = true then
                    pure (CheckedIsolatedParallelNumericDirectRun.mk
                      route additionalRoutes precondition
                      suppressExactScaleWarning resolved targetsCoherent
                      guardAdmitted usesOperand operandsAdmitted
                      expressionAdmitted authoring scopeAvailable
                      operationScale scaleOwned scaleAdmitted)
                  else
                    throw (.operationScaleMismatch
                      route.target.info.scale operationScale)
                else
                  let outside := operandRoutes.find? fun candidate =>
                    !parallelNumericRouteScopeAvailable candidate
                  throw (.operandFrameOutsideTarget
                    (Option.getD
                      (outside.map fun candidate =>
                        model.repeatableScopeForGroupPath
                          candidate.groups.rightGroup.path) []))
              else
                throw .guardNotLimitedToOperand
          | result => throw (.authoring result)
        else
          throw .unsupportedExpression
      else
        throw .expressionNotLimitedToOperand
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
