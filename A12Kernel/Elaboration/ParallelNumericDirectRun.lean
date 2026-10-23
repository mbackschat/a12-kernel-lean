import A12Kernel.Elaboration.ParallelNumericOperand

/-! # Checked parallel Number operations

The checked key joins provide typed field carriers to the shared numeric tree and evaluator
(spec/09 §5). Bound fields read at the target environment; joined fields read at their matching
environment, with an explicit empty carrier for unmatched keys. Route discovery does not observe
values, so first-selected tables preserve guard and operand poison order. A scalar fallback may
share a route selected by another alternative. The mixed plan owns scheduling and fresh overlays.
-/

namespace A12Kernel

/-- Whether the target row binds every frame the join's partner side needs: a partner framed by a
repeatable level outside the target's frames has no row the target binds. -/
def CheckedParallelTargetJoin.scopeAvailable (join : CheckedParallelTargetJoin model) : Bool :=
  match join.groups.outerScopePlan with
  | .framed .right _ _ => false
  | .common _ | .framed .left _ _ => true

private def parallelNumericRouteScopeAvailable
    (route : CheckedParallelNumericTargetRoute model) : Bool :=
  route.join.scopeAvailable

/-- One exact target-addressed rich outcome from a parallel computation. -/
structure ParallelNumericDirectOutcome where
  address : CellAddr
  outcome : NumericTargetOutcome
  deriving Repr, DecidableEq

/-- The complete one-computation inventory for one checked optionally guarded Number operation over the existing parallel route certificate. -/
structure CheckedIsolatedParallelNumericDirectRun (model : FlatModel) where
  private mk ::
  route : CheckedParallelNumericTargetRoute model
  additionalRoutes : List (CheckedParallelNumericTargetRoute model)
  precondition : Option (ParallelNumericGuard model)
  suppressExactScaleWarning : Bool
  bandedRounding : Option ComputationRoundingMode := none
  expression : AuthoredNumericExpr (ParallelNumericOperationAtom model)
  guardExcludesTarget :
    (precondition.map
      (·.forbidsTarget route.targetField)).getD false = false
  expressionExcludesTarget :
    expression.anyAtom (·.forbidsTarget route.targetField) = false
  routeTargetsCoherent :
    (additionalRoutes.all fun additional =>
      additional.targetDeclaration == route.targetDeclaration) = true
  guardAdmitted :
    parallelNumericDirectGuardAdmitted
      ((route :: additionalRoutes).map (·.join)) precondition = true
  expressionOperandsAdmitted :
    expression.allAtoms
      (parallelNumericOperationAtomAdmitted
        (route :: additionalRoutes)) = true
  expressionAdmitted :
    expression.isAdmittedResolvedNumericOperation = true
  expressionAuthoring :
    expression.numericOperationAuthoringCheck = .accepted
  operandScopesAvailable :
    (route :: additionalRoutes).all
      parallelNumericRouteScopeAvailable = true
  operationScale : NumericScaleSummary
  operationScaleOwned :
    expression.summary? ParallelNumericOperationAtom.scaleSummary = some operationScale
  operationScaleAdmitted :
    exactNumericScaleComparisonAllowedWithSuppression
      suppressExactScaleWarning
      (.field route.target.info.scale)
      operationScale = true

namespace CheckedIsolatedParallelNumericDirectRun

/-- Output rounding belongs to the selected store attempt; the authored operation remains
unchanged for generated comparison (spec/09, KF474). -/
def withBandedRounding (checked : CheckedIsolatedParallelNumericDirectRun model)
    (mode : Option ComputationRoundingMode) : CheckedIsolatedParallelNumericDirectRun model :=
  { checked with bandedRounding := mode }

/-- Every distinct operand group is represented by one route to the same checked target. -/
def operandRoutes
    (checked : CheckedIsolatedParallelNumericDirectRun model) :
    List (CheckedParallelNumericTargetRoute model) :=
  checked.route :: checked.additionalRoutes

/-- Whether the guard or resolved numeric expression reads one exact field. -/
def referencesField
    (checked : CheckedIsolatedParallelNumericDirectRun model)
    (field : FieldId) : Bool :=
  (checked.precondition.map (·.referencesField field)).getD false ||
    checked.expression.anyAtom (·.referencesField field)

/-- Whether the guard's target ban or the resolved expression reaches one exact field. A positive
read of a group containing the field is no ban, as on the ordinary carrier (spec/09 §5). -/
def forbidsField
    (checked : CheckedIsolatedParallelNumericDirectRun model)
    (field : FieldId) : Bool :=
  (checked.precondition.map (·.forbidsTarget field)).getD false ||
    checked.expression.anyAtom (·.forbidsTarget field)

def WellFormed
    (checked : CheckedIsolatedParallelNumericDirectRun model) : Prop :=
  checked.route.WellFormed ∧
    (∀ additional ∈ checked.additionalRoutes,
      additional.WellFormed) ∧
    checked.additionalRoutes.all (fun additional =>
      additional.targetDeclaration ==
        checked.route.targetDeclaration) = true ∧
    (checked.precondition.map
      (·.forbidsTarget checked.route.targetField)).getD false = false ∧
    checked.expression.anyAtom (·.forbidsTarget checked.route.targetField) = false ∧
    parallelNumericDirectGuardAdmitted
      (checked.operandRoutes.map (·.join)) checked.precondition = true ∧
    checked.expression.allAtoms
      (parallelNumericOperationAtomAdmitted
        checked.operandRoutes) = true ∧
    checked.expression.isAdmittedResolvedNumericOperation = true ∧
    checked.expression.numericOperationAuthoringCheck = .accepted ∧
    checked.operandRoutes.all
      parallelNumericRouteScopeAvailable = true ∧
    checked.expression.summary? ParallelNumericOperationAtom.scaleSummary =
      some checked.operationScale ∧
    exactNumericScaleComparisonAllowedWithSuppression
      checked.suppressExactScaleWarning
      (.field checked.route.target.info.scale)
      checked.operationScale = true

inductive ExecutionError where
  | guard (error : CheckedComputationConditionError)
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
    (read : CellAddr → Except CheckedDocumentError CheckedCell)
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
        let cell ← read {
          field := declaration.id
          path
        } |>.mapError ExecutionError.document
        pure (declaration.id, cell)

/-- The row each route's partner group binds at one target key, for a guard part read at that row:
the matched row, or a key-only row when the key matches none. A group with neither has no entry. -/
def partnerEnvironments (joins : List (CheckedParallelTargetJoin model))
    (preliminary : CheckedIndexPreliminary model) (targetEnvironment : Env) (key : SemanticIndexKey) :
    Except ExecutionError (List (GroupPath × Env)) := do
  let found ← joins.mapM fun join => do
    let group := join.groups.rightGroup
    let column ← preliminary.resolveIndexColumn group targetEnvironment
      |>.mapError (ExecutionError.indexColumn .operand)
    pure <| (group.path, ·) <$> match column.entries.find? (·.key == key) with
      | some entry => some entry.environment
      | none => preliminary.base.keyOnlyEnvironment? targetEnvironment group
  pure found.reduceOption

/-- The guard context at one target row: the joined cells, the document there, and the document at
each partner row. -/
def guardContextAt (cells : List (FieldId × CheckedCell)) (partners : List (GroupPath × Env))
    (ordinaryAt : Env → NumericComputationEvaluationContext) (targetEnvironment : Env) :
    ParallelNumericGuardContext := {
  joinedRead := fun field =>
    match cells.find? fun cell => cell.1 == field with
    | some cell => cell.2
    | none => malformedCheckedCell
  ordinary := ordinaryAt targetEnvironment
  partnerAt := fun group => (partners.lookup group).map ordinaryAt }

/-- Fetch bound fields at the target environment and joined fields through their indexed-group route, using one supplied checked addressed read. Carrier construction remains observation-free so a table can collect all row inputs before first-selected evaluation. -/
def operandCellsWith
    (checked : CheckedIsolatedParallelNumericDirectRun model)
    (preliminary : CheckedIndexPreliminary model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (targetEnvironment : Env) (key : SemanticIndexKey) :
    Except ExecutionError (List (FieldId × CheckedCell)) := do
  let guardDeclarations :=
    (parallelNumericGuardFields checked.precondition).filterMap fun field =>
      match model.lookupUniqueId field with
      | .ok declaration => some declaration
      | .error _ => none
  let declarations :=
    (checked.route.sourceDeclaration ::
      (model.fields.filter fun declaration =>
        checked.expression.anyAtom fun atom =>
          atom.joined?.any (NumericComputationAtom.referencesField model declaration.id)) ++
      guardDeclarations).eraseDups
  let bound := checked.route.join.admitsBoundDeclaration
  let boundCells ← (declarations.filter bound).mapM fun declaration => do
    let path ← targetEnvironment.pathForScope declaration.repeatableScope |>.mapError .environment
    let cell ← read { field := declaration.id, path } |>.mapError .document
    pure (declaration.id, cell)
  let nested ← checked.operandRoutes.mapM fun route => do
    let owned := declarations.filter fun declaration => !bound declaration &&
      (route.admitsExpressionDeclaration declaration || route.join.admitsGuardField declaration.id)
    operandCellsForRoute route owned preliminary read targetEnvironment key
  pure (boundCells ++ nested.flatten)

/-- Preserve the isolated-run entry point by reading carriers from the immutable preliminary document. -/
def operandCells
    (checked : CheckedIsolatedParallelNumericDirectRun model)
    (preliminary : CheckedIndexPreliminary model)
    (targetEnvironment : Env) (key : SemanticIndexKey) :
    Except ExecutionError (List (FieldId × CheckedCell)) :=
  checked.operandCellsWith preliminary preliminary.base.read
    targetEnvironment key

/-- Resolve the target's checked semantic key at one actual target environment. The exact address is retained only for structural failure reporting. -/
def joinTargetKeyFor
    (join : CheckedParallelTargetJoin model)
    (preliminary : CheckedIndexPreliminary model)
    (targetEnvironment : Env) (address : CellAddr) :
    Except ExecutionError SemanticIndexKey := do
  let targetColumn ←
    preliminary.resolveIndexColumn
      join.groups.leftGroup targetEnvironment
      |>.mapError (ExecutionError.indexColumn .target)
  -- A target below its joined group joins the key of the joined row holding it.
  let joinedScope := model.repeatableScopeForGroupPath join.groups.leftGroup.path
  let targetJoined := (targetEnvironment.pathForScope joinedScope).toOption
  match targetColumn.entries.find? fun entry =>
      targetJoined.isSome && (entry.environment.pathForScope joinedScope).toOption == targetJoined with
  | some entry => pure entry.key
  | none => throw (.missingTargetIndex address)

def targetKeyFor
    (checked : CheckedIsolatedParallelNumericDirectRun model)
    (preliminary : CheckedIndexPreliminary model)
    (targetEnvironment : Env) (address : CellAddr) :
    Except ExecutionError SemanticIndexKey :=
  joinTargetKeyFor checked.route.join preliminary targetEnvironment address

/-- Evaluate an already-selected checked operation against one addressed carrier context. Guard selection remains with the caller, allowing both the singleton run and a wider first-selected table to share target semantics without inspecting outcomes to recover selection. -/
def evaluateSelected
    (checked : CheckedIsolatedParallelNumericDirectRun model)
    (context : ParallelNumericGuardContext) :
    Except ExecutionError NumericTargetOutcome := do
  let value ← checked.expression.evaluateComputationWith
      ParallelNumericOperationAtom.numericComputationFault? (·.read context)
      |>.mapError .numeric
  let checkedTarget := match checked.bandedRounding with
    | some mode => checked.route.targetPolicy.checkBanded mode value
    | none => if checked.suppressExactScaleWarning then
        checked.route.targetPolicy.checkWithScaleWarningSuppressed value
      else checked.route.targetPolicy.check value
  match checkedTarget with
  | .supported outcome => pure outcome
  | .unsupported fault => throw (.unsupportedTarget fault)

def executeTargetWith
    (checked : CheckedIsolatedParallelNumericDirectRun model)
    (preliminary : CheckedIndexPreliminary model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (ordinaryAt : Env → NumericComputationEvaluationContext)
    (targetEnvironment : Env) (address : CellAddr) :
    Except ExecutionError ParallelNumericDirectOutcome := do
  let key ← checked.targetKeyFor preliminary targetEnvironment address
  let cells ← checked.operandCellsWith preliminary read targetEnvironment key
  let partners ← partnerEnvironments (checked.operandRoutes.map (·.join)) preliminary targetEnvironment key
  let guardContext := guardContextAt cells partners ordinaryAt targetEnvironment
  let guardResult ← match checked.precondition with
    | none => pure ComputationConditionResult.holds
    | some guard => (guard.eval guardContext).mapError .guard
  match guardResult with
  | .notTrue => pure { address, outcome := .noValue }
  | .poison cause =>
      pure { address, outcome := .inheritedPoison cause }
  | .holds =>
      pure { address, outcome := ← checked.evaluateSelected guardContext }

/-- Derive all target coverage from every statically participating route. Additional routes contribute only invalidity; the primary route owns the canonical actual target inventory. -/
def targetCoverage
    (primary : CheckedParallelTargetJoin model)
    (additional : List (CheckedParallelTargetJoin model))
    (preliminary : CheckedIndexPreliminary model) :
    Except ExecutionError (List ParallelNumericTargetCoverage) := do
  let primaryCoverage ←
    primary.targetCoverage preliminary
      |>.mapError fun
        | .marking side error => .marking side error
        | .targetRows error => .targetRows error
        | .targetEnvironment error => .environment error
  let additionalCoverage ← additional.mapM fun join =>
    join.targetCoverage preliminary
      |>.mapError fun
        | .marking side error => .marking side error
        | .targetRows error => .targetRows error
        | .targetEnvironment error => .environment error
  let additionallyInvalid :=
    (additionalCoverage.flatten.filter (·.indexInvalid)).map (·.address)
  pure (primaryCoverage.map fun target =>
    { target with indexInvalid := target.indexInvalid || additionallyInvalid.contains target.address })

/-- The executable projection excludes the same invalid-index and over-limit targets that the
whole-call bridge retains as clears; both consume one route-owned coverage judgment. -/
def executableTargets
    (primary : CheckedParallelTargetJoin model)
    (additional : List (CheckedParallelTargetJoin model))
    (preliminary : CheckedIndexPreliminary model) :
    Except ExecutionError (List ParallelNumericTargetCoverage) := do
  pure ((← targetCoverage primary additional preliminary).filter fun target =>
    !target.indexInvalid && !target.overLimit)

/-- Execute every existing target row not covered by any participating group's checked invalid-index marks. Collection order is the checked document's private canonicalization. -/
def execute
    (checked : CheckedIsolatedParallelNumericDirectRun model)
    (preliminary : CheckedIndexPreliminary model) :
    Except ExecutionError (List ParallelNumericDirectOutcome) := do
  let targets ← executableTargets checked.route.join
    (checked.additionalRoutes.map (·.join)) preliminary
  targets.mapM fun target =>
    checked.executeTargetWith preliminary preliminary.base.read preliminary.base.parallelGuardContextAt
      target.environment target.address

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

/-- Resolve typed atoms and construct one checked route for each unbound field. Evaluation still
uses the authored tree, so route discovery never observes operand values. -/
private def FlatModel.resolveParallelNumericDirectExpression
    (model : FlatModel) (declaringGroup : GroupPath)
    (route : CheckedParallelNumericTargetRoute model)
    (expression : AuthoredNumericExpr (ParallelNumericOperationAtomOf SurfaceNumericAtom model)) :
    Except ParallelNumericDirectPlanError
      (AuthoredNumericExpr (ParallelNumericOperationAtom model) × List (CheckedParallelNumericTargetRoute model)) := do
  let resolved ← expression.mapM fun
    | .joined atom => .joined <$> model.resolveParallelNumericAtom declaringGroup route.targetDeclaration.groupPath atom
    | .ordinary atom => pure (.ordinary atom)
  let joinedFields := (expression.atoms.filterMap (·.joined?)).flatMap SurfaceNumericAtom.parallelFields
  let routes ← joinedFields.foldlM (fun routes reference => do
    let declaration ← model.resolveParallelNumericDeclaration declaringGroup route.targetDeclaration.groupPath reference
    if route.join.admitsBoundDeclaration declaration then pure routes
    else
      let checked ← (checkParallelNumericTargetRoute model declaringGroup route.targetField reference).mapError .route
      pure (appendParallelNumericRouteIfNew routes checked)) [route]
  pure (resolved, routes.drop 1)

/-- Add one checked route for every guard field whose indexed group is not already represented. Guard evaluation remains lazy; this construction records only the groups whose index columns participate in the generated loop. -/
private def FlatModel.resolveParallelNumericGuardRoutes
    (model : FlatModel) (declaringGroup : GroupPath)
    (primary : CheckedParallelNumericTargetRoute model)
    (additionalRoutes : List (CheckedParallelNumericTargetRoute model))
    (precondition : Option (ParallelNumericGuard model)) :
    Except ParallelNumericDirectPlanError
      (List (CheckedParallelNumericTargetRoute model)) := do
  let routes ← (parallelNumericGuardFields precondition).foldlM
    (fun (routes : List (CheckedParallelNumericTargetRoute model))
        field => do
      if routes.any fun route => route.join.admitsGuardField field then
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

/-- Certify target exclusion at the complete operation boundary. Keeping the direct guard and expression facts makes the checked operation's public self-reference invariant eliminable without reconstructing model paths in every consumer proof. -/
private structure ParallelNumericTargetExclusion
    (target : FieldId)
    (precondition : Option (ParallelNumericGuard model))
    (expression : AuthoredNumericExpr (ParallelNumericOperationAtom model)) : Type where
  guard :
    (precondition.map
      (·.forbidsTarget target)).getD false = false
  expression :
    expression.anyAtom (·.forbidsTarget target) = false

private def checkParallelNumericTargetExclusion
    (target : FieldId)
    (precondition : Option (ParallelNumericGuard model))
    (expression : AuthoredNumericExpr (ParallelNumericOperationAtom model)) :
    Except ParallelNumericDirectPlanError
      (ParallelNumericTargetExclusion target precondition expression) :=
  if expressionExcluded :
      expression.anyAtom (·.forbidsTarget target) = false then
    if guardExcluded :
        (precondition.map
          (·.forbidsTarget target)).getD false = false then
      .ok {
        guard := guardExcluded
        expression := expressionExcluded
      }
    else
      .error .guardNotLimitedToOperand
  else
    .error .expressionNotLimitedToOperand

/-- Check one optionally guarded Number operation without reimplementing pairwise joins, numeric lowering, operation admission, authoring checks, or the scale gate. Each distinct indexed group referenced by the expression or guard receives one route to the same target. The supplied primary route belongs to the complete table and may be unused by this alternative. The scale-warning directive defaults to false; when true it selects both the shared suppressed static gate and the existing warning-suppressed target check, but never changes expression arithmetic. -/
def checkParallelNumericTableOperationWithGuard (model : FlatModel)
    (declaringGroup : GroupPath) (targetField : FieldId)
    (operandReference : SurfaceFieldPath)
    (expression : AuthoredNumericExpr (ParallelNumericOperationAtomOf SurfaceNumericAtom model))
    (precondition : Option (ParallelNumericGuard model))
    (suppressExactScaleWarning : Bool := false) :
    Except ParallelNumericDirectPlanError
      (CheckedIsolatedParallelNumericDirectRun model) := do
  let route ←
    checkParallelNumericTargetRoute
      model declaringGroup targetField operandReference
      |>.mapError .route
  let (resolved, expressionRoutes) ←
    model.resolveParallelNumericDirectExpression
      declaringGroup route expression
  let targetExclusion ←
    checkParallelNumericTargetExclusion
      route.targetField precondition resolved
  let additionalRoutes ←
    model.resolveParallelNumericGuardRoutes declaringGroup
      route expressionRoutes precondition
  let operandRoutes := route :: additionalRoutes
  if targetsCoherent :
      additionalRoutes.all (fun additional =>
        additional.targetDeclaration ==
          route.targetDeclaration) = true then
    if operandsAdmitted :
        resolved.allAtoms
          (parallelNumericOperationAtomAdmitted operandRoutes) = true then
      if expressionAdmitted :
          resolved.isAdmittedResolvedNumericOperation = true then
        match authoring : resolved.numericOperationAuthoringCheck with
        | .accepted =>
          match scaleOwned :
              resolved.summary? ParallelNumericOperationAtom.scaleSummary with
          | none => throw .unsupportedExpression
          | some operationScale =>
            if guardAdmitted :
                parallelNumericDirectGuardAdmitted
                  (operandRoutes.map (·.join)) precondition = true then
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
                    suppressExactScaleWarning none resolved
                    targetExclusion.guard targetExclusion.expression
                    targetsCoherent guardAdmitted
                    operandsAdmitted
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


/-- The isolated entry point keeps its own joined-operand requirement. Only a complete table
may supply a primary route from another alternative (spec/09 §5). -/
def checkIsolatedParallelNumericExpressionRunWithGuard (model : FlatModel)
    (declaringGroup : GroupPath) (targetField : FieldId)
    (operandReference : SurfaceFieldPath) (expression : AuthoredNumericExpr SurfaceNumericAtom)
    (precondition : Option (ParallelNumericGuard model))
    (suppressExactScaleWarning : Bool := false) :
    Except ParallelNumericDirectPlanError (CheckedIsolatedParallelNumericDirectRun model) := do
  let anchor ← (checkParallelNumericComputationClearingPlan model declaringGroup targetField operandReference).mapError .route
  let checked ← checkParallelNumericTableOperationWithGuard model declaringGroup targetField
    operandReference (expression.map .joined) precondition suppressExactScaleWarning
  if checked.expression.anyAtom (fun atom => model.fields.any fun declaration =>
      atom.referencesField declaration.id && anchor.admitsExpressionDeclaration declaration) then
    pure checked
  else throw .expressionNotLimitedToOperand

/-- Check one optionally guarded direct Number copy as the atom-only specialization of the shared expression route. -/
def checkIsolatedParallelNumericDirectRunWithGuard (model : FlatModel)
    (declaringGroup : GroupPath) (targetField : FieldId)
    (operandReference : SurfaceFieldPath)
    (precondition : Option (ParallelNumericGuard model)) :
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
