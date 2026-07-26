import A12Kernel.Elaboration.CheckedIndexColumn
import A12Kernel.Elaboration.NumericComputation.SourceTarget
import A12Kernel.Semantics.ParallelComputationClearing

/-! # Checked parallel-computation clearing plans

This bounded route recognizes one direct non-starred Number operand in an indexed group parallel to a repeatable Number target's indexed group. Both declarations and both groups come from one validated model; the existing checked parallel-group owner proves index-name/kind and scope compatibility. It derives side-specific mark scopes, resolves checked index columns over actual target rows, and projects covered source-filled targets to an extensional clearing fragment. General computation expressions, guards, starred operands, table execution, successful repeatable outcomes, and application remain separate. -/

namespace A12Kernel

inductive ParallelComputationIndexSide where
  | target
  | operand
  deriving Repr, DecidableEq

inductive ParallelComputationPlanError where
  | targetResolve (error : ResolveError)
  | operandResolve (error : ResolveError)
  | join (error : CheckedIndexColumnError)
  | missingIndexedAncestor (field : FieldId)
  | multipleIndexedAncestors (field : FieldId) (groups : List GroupPath)
  | targetNotNumber (field : FieldId)
  | operandNotNumber (path : List String)
  | incoherentTargetPolicy (field : FieldId)
  | incoherentTargetScope (path : List String)
  | incoherentOperandScope (path : List String)
  deriving Repr, DecidableEq

/-- Structural failures while deriving post-loop marks from one checked preliminary document. Index-column failure and malformed target addressing never become semantic invalidity. -/
inductive ParallelComputationMarkingError where
  | targetRows (error : ActualRowEnvironmentError)
  | indexColumn (error : CheckedIndexColumnError)
  | targetEnvironment (error : EnvBindingError)
  deriving Repr, DecidableEq

/-- Structural failures while projecting every actual target to its exact address and checked post-loop index disposition. -/
inductive ParallelNumericTargetCoverageError where
  | marking (side : ParallelComputationIndexSide)
      (error : ParallelComputationMarkingError)
  | targetRows (error : ActualRowEnvironmentError)
  | targetEnvironment (error : EnvBindingError)
  deriving Repr, DecidableEq

/-- Structural failures while projecting checked post-loop marks to source-relative public clears. -/
inductive ParallelNumericClearingError where
  | marking (side : ParallelComputationIndexSide)
      (error : ParallelComputationMarkingError)
  | targetRows (error : ActualRowEnvironmentError)
  | targetEnvironment (error : EnvBindingError)
  | sourceTarget (error : NumericSourceTargetError)
  deriving Repr, DecidableEq

/-- One actual target paired with the exact post-loop index disposition derived from both checked index sides. -/
structure ParallelNumericTargetCoverage where
  environment : Env
  address : CellAddr
  indexInvalid : Bool
  deriving Repr, DecidableEq

/-- The repeatable Number fragment of the public computation result. Collection order is not public. -/
structure ParallelNumericClearingView where
  private mk ::
  cleared : List CellAddr
  deriving Repr, DecidableEq

namespace ParallelNumericClearingView

def empty : ParallelNumericClearingView := { cleared := [] }

def ExtensionalEq (left right : ParallelNumericClearingView) : Prop :=
  left.cleared.Perm right.cleared

end ParallelNumericClearingView

/-- One model-certified parallel route from a repeatable Number target to any directly observed field. The source field's kind is deliberately unconstrained because computation presence guards are kind-neutral. -/
structure CheckedParallelNumericTargetRoute (model : FlatModel) where
  private mk ::
  declaringGroup : GroupPath
  sourceReference : SurfaceFieldPath
  targetField : FieldId
  targetDeclaration : FlatFieldDecl
  sourceDeclaration : FlatFieldDecl
  target : FlatNumberField
  targetPolicy : NumericTargetPolicy
  groups : CheckedParallelIndexGroups model
  targetResolved :
    model.lookupUniqueId targetField = .ok targetDeclaration
  sourceResolved :
    model.resolveFieldDeclarationUnchecked declaringGroup sourceReference =
      .ok sourceDeclaration
  targetNumber : targetDeclaration.toNumberField? = some target
  targetPolicyOwned :
    targetDeclaration.toNumericTargetPolicy? = some targetPolicy
  targetGroup :
    groups.leftGroup.path.isPrefixOf targetDeclaration.groupPath = true
  sourceGroup :
    groups.rightGroup.path.isPrefixOf sourceDeclaration.groupPath = true
  targetScope :
    (targetDeclaration.repeatableScope ==
      model.repeatableScopeForGroupPath groups.leftGroup.path) = true
  sourceScope :
    (sourceDeclaration.repeatableScope ==
      model.repeatableScopeForGroupPath groups.rightGroup.path) = true

namespace CheckedParallelNumericTargetRoute

def WellFormed (route : CheckedParallelNumericTargetRoute model) : Prop :=
  route.groups.WellFormed ∧
    model.lookupUniqueId route.targetField =
      .ok route.targetDeclaration ∧
    model.resolveFieldDeclarationUnchecked route.declaringGroup
      route.sourceReference = .ok route.sourceDeclaration ∧
    route.targetDeclaration.toNumberField? = some route.target ∧
    route.targetDeclaration.toNumericTargetPolicy? =
      some route.targetPolicy ∧
    route.groups.leftGroup.path.isPrefixOf
      route.targetDeclaration.groupPath = true ∧
    route.groups.rightGroup.path.isPrefixOf
      route.sourceDeclaration.groupPath = true ∧
    (route.targetDeclaration.repeatableScope ==
      model.repeatableScopeForGroupPath route.groups.leftGroup.path) = true ∧
    (route.sourceDeclaration.repeatableScope ==
      model.repeatableScopeForGroupPath route.groups.rightGroup.path) = true

/-- Enumerate exactly the physically instantiated target rows from the checked document. The target declaration owns the complete scope; callers cannot supply environments or fabricate rows. The inherited document order is an internal canonicalization because Kernel clearing order is not observable. -/
def targetEnvironments (route : CheckedParallelNumericTargetRoute model)
    (checked : CheckedDocument model) :
    Except ActualRowEnvironmentError (List Env) :=
  checked.actualRowEnvironments
    route.targetDeclaration.repeatableScope

/-- Derive one checked index side's cause-blind invalid-mark plan. The target's complete scope remains the coverage domain for every observed group. -/
def markPlanFor (route : CheckedParallelNumericTargetRoute model) :
    ParallelComputationIndexSide → ParallelComputationMarkPlan
  | .target =>
      ParallelComputationMarkPlan.ofScopes
        route.targetDeclaration.repeatableScope
        (model.repeatableScopeForGroupPath
          route.groups.leftGroup.path).dropLast
  | .operand =>
      ParallelComputationMarkPlan.ofScopes
        route.targetDeclaration.repeatableScope
        (model.repeatableScopeForGroupPath
          route.groups.rightGroup.path).dropLast

/-- Derive cause-blind post-loop mark keys for one checked index side. Each column is resolved at the target instance's inherited outer bindings, duplicate keys are collapsed, and the returned order is private execution detail. -/
def invalidIndexMarks (route : CheckedParallelNumericTargetRoute model)
    (preliminary : CheckedIndexPreliminary model)
    (side : ParallelComputationIndexSide) :
    Except ParallelComputationMarkingError
      (List (ParallelComputationMark (route.markPlanFor side))) := do
  let targetEnvironments ←
    route.targetEnvironments preliminary.base
      |>.mapError .targetRows
  let group := match side with
    | .target => route.groups.leftGroup
    | .operand => route.groups.rightGroup
  let candidates ← targetEnvironments.mapM fun targetEnvironment => do
    let column ←
      preliminary.resolveIndexColumn group targetEnvironment
        |>.mapError ParallelComputationMarkingError.indexColumn
    (route.markPlanFor side).markForUnavailable
      column.unavailableKey targetEnvironment
        |>.mapError ParallelComputationMarkingError.targetEnvironment
  pure (candidates.filterMap id).eraseDups

/-- Classify one already-enumerated target list against already-derived marks from both checked sides. This is the shared coverage crossing used by execution and public clearing. -/
def targetCoverageWithMarks
    (route : CheckedParallelNumericTargetRoute model)
    (preliminary : CheckedIndexPreliminary model)
    (targetMarks :
      List (ParallelComputationMark (route.markPlanFor .target)))
    (operandMarks :
      List (ParallelComputationMark (route.markPlanFor .operand))) :
    Except ParallelNumericTargetCoverageError
      (List ParallelNumericTargetCoverage) := do
  let targetEnvironments ←
    route.targetEnvironments preliminary.base
      |>.mapError .targetRows
  targetEnvironments.mapM fun environment => do
    let path ←
      environment.pathForScope route.targetDeclaration.repeatableScope
        |>.mapError ParallelNumericTargetCoverageError.targetEnvironment
    let coveredByTarget ←
      (route.markPlanFor .target).coversAny environment targetMarks
        |>.mapError ParallelNumericTargetCoverageError.targetEnvironment
    let coveredByOperand ←
      (route.markPlanFor .operand).coversAny environment operandMarks
        |>.mapError ParallelNumericTargetCoverageError.targetEnvironment
    pure {
      environment
      address := { field := route.targetField, path }
      indexInvalid := coveredByTarget || coveredByOperand
    }

/-- Derive both checked mark sets and project every actual target through their shared coverage decision. -/
def targetCoverage
    (route : CheckedParallelNumericTargetRoute model)
    (preliminary : CheckedIndexPreliminary model) :
    Except ParallelNumericTargetCoverageError
      (List ParallelNumericTargetCoverage) := do
  let targetMarks ←
    route.invalidIndexMarks preliminary .target
      |>.mapError (ParallelNumericTargetCoverageError.marking .target)
  let operandMarks ←
    route.invalidIndexMarks preliminary .operand
      |>.mapError (ParallelNumericTargetCoverageError.marking .operand)
  route.targetCoverageWithMarks preliminary targetMarks operandMarks

/-- Project both checked index sides to exact source-filled target addresses. A runtime invalid mark remains private unless it covers a target whose immutable source value is nonempty. -/
def clearedSourceTargets
    (route : CheckedParallelNumericTargetRoute model)
    (preliminary : CheckedIndexPreliminary model) :
    Except ParallelNumericClearingError ParallelNumericClearingView := do
  let targetMarks ←
    route.invalidIndexMarks preliminary .target
      |>.mapError (ParallelNumericClearingError.marking .target)
  let operandMarks ←
    route.invalidIndexMarks preliminary .operand
      |>.mapError (ParallelNumericClearingError.marking .operand)
  if targetMarks.isEmpty && operandMarks.isEmpty then
    pure ParallelNumericClearingView.empty
  else
    let coverage ←
      route.targetCoverageWithMarks preliminary targetMarks operandMarks
        |>.mapError fun
          | .marking side error => .marking side error
          | .targetRows error => .targetRows error
          | .targetEnvironment error => .targetEnvironment error
    let candidates ← coverage.mapM fun target => do
      if !target.indexInvalid then
        pure none
      else
        let source ←
          preliminary.base.numericTargetStateAt target.address
            |>.mapError ParallelNumericClearingError.sourceTarget
        if source.sourceIdentity.isSome then
          pure (some target.address)
        else
          pure none
    pure { cleared := candidates.filterMap id }

end CheckedParallelNumericTargetRoute

/-- One model-certified direct Number parallel route. `operandReference` is the parser-independent ordinary field-path shape; starred and semantic-index paths cannot inhabit it. -/
structure CheckedParallelNumericClearingPlan (model : FlatModel) where
  private mk ::
  declaringGroup : GroupPath
  operandReference : SurfaceFieldPath
  targetField : FieldId
  targetDeclaration : FlatFieldDecl
  operandDeclaration : FlatFieldDecl
  target : FlatNumberField
  operand : FlatNumberField
  targetPolicy : NumericTargetPolicy
  groups : CheckedParallelIndexGroups model
  targetResolved :
    model.lookupUniqueId targetField = .ok targetDeclaration
  operandResolved :
    model.resolveFieldDeclarationUnchecked declaringGroup operandReference =
      .ok operandDeclaration
  targetNumber : targetDeclaration.toNumberField? = some target
  operandNumber : operandDeclaration.toNumberField? = some operand
  targetPolicyOwned :
    targetDeclaration.toNumericTargetPolicy? = some targetPolicy
  targetGroup :
    groups.leftGroup.path.isPrefixOf targetDeclaration.groupPath = true
  operandGroup :
    groups.rightGroup.path.isPrefixOf operandDeclaration.groupPath = true
  targetScope :
    (targetDeclaration.repeatableScope ==
      model.repeatableScopeForGroupPath groups.leftGroup.path) = true
  operandScope :
    (operandDeclaration.repeatableScope ==
      model.repeatableScopeForGroupPath groups.rightGroup.path) = true

namespace CheckedParallelNumericClearingPlan

def WellFormed (plan : CheckedParallelNumericClearingPlan model) : Prop :=
  plan.groups.WellFormed ∧
    model.lookupUniqueId plan.targetField =
      .ok plan.targetDeclaration ∧
    model.resolveFieldDeclarationUnchecked plan.declaringGroup
      plan.operandReference = .ok plan.operandDeclaration ∧
    plan.targetDeclaration.toNumberField? = some plan.target ∧
    plan.operandDeclaration.toNumberField? = some plan.operand ∧
    plan.targetDeclaration.toNumericTargetPolicy? =
      some plan.targetPolicy ∧
    plan.groups.leftGroup.path.isPrefixOf
      plan.targetDeclaration.groupPath = true ∧
    plan.groups.rightGroup.path.isPrefixOf
      plan.operandDeclaration.groupPath = true ∧
    (plan.targetDeclaration.repeatableScope ==
      model.repeatableScopeForGroupPath plan.groups.leftGroup.path) = true ∧
    (plan.operandDeclaration.repeatableScope ==
      model.repeatableScopeForGroupPath plan.groups.rightGroup.path) = true

/-- Erase only the Number-specific source certificate; target, group, scope, and marking evidence remain unchanged. -/
def asTargetRoute
    (plan : CheckedParallelNumericClearingPlan model) :
    CheckedParallelNumericTargetRoute model := {
  declaringGroup := plan.declaringGroup
  sourceReference := plan.operandReference
  targetField := plan.targetField
  targetDeclaration := plan.targetDeclaration
  sourceDeclaration := plan.operandDeclaration
  target := plan.target
  targetPolicy := plan.targetPolicy
  groups := plan.groups
  targetResolved := plan.targetResolved
  sourceResolved := plan.operandResolved
  targetNumber := plan.targetNumber
  targetPolicyOwned := plan.targetPolicyOwned
  targetGroup := plan.targetGroup
  sourceGroup := plan.operandGroup
  targetScope := plan.targetScope
  sourceScope := plan.operandScope
}

def targetEnvironments (plan : CheckedParallelNumericClearingPlan model)
    (checked : CheckedDocument model) :
    Except ActualRowEnvironmentError (List Env) :=
  plan.asTargetRoute.targetEnvironments checked

def markPlanFor (plan : CheckedParallelNumericClearingPlan model) :
    ParallelComputationIndexSide → ParallelComputationMarkPlan
  | side => plan.asTargetRoute.markPlanFor side

def invalidIndexMarks (plan : CheckedParallelNumericClearingPlan model)
    (preliminary : CheckedIndexPreliminary model)
    (side : ParallelComputationIndexSide) :
    Except ParallelComputationMarkingError
      (List (ParallelComputationMark (plan.markPlanFor side))) := do
  plan.asTargetRoute.invalidIndexMarks preliminary side

def targetCoverageWithMarks
    (plan : CheckedParallelNumericClearingPlan model)
    (preliminary : CheckedIndexPreliminary model)
    (targetMarks :
      List (ParallelComputationMark (plan.markPlanFor .target)))
    (operandMarks :
      List (ParallelComputationMark (plan.markPlanFor .operand))) :
    Except ParallelNumericTargetCoverageError
      (List ParallelNumericTargetCoverage) :=
  plan.asTargetRoute.targetCoverageWithMarks
    preliminary targetMarks operandMarks

def targetCoverage
    (plan : CheckedParallelNumericClearingPlan model)
    (preliminary : CheckedIndexPreliminary model) :
    Except ParallelNumericTargetCoverageError
      (List ParallelNumericTargetCoverage) :=
  plan.asTargetRoute.targetCoverage preliminary

def clearedSourceTargets
    (plan : CheckedParallelNumericClearingPlan model)
    (preliminary : CheckedIndexPreliminary model) :
    Except ParallelNumericClearingError ParallelNumericClearingView :=
  plan.asTargetRoute.clearedSourceTargets preliminary

end CheckedParallelNumericClearingPlan

private def indexedGroupForParallelComputation (model : FlatModel)
    (declaration : FlatFieldDecl) :
    Except ParallelComputationPlanError RepeatableGroupDecl :=
  match model.indexedAncestorGroups declaration with
  | [] => .error (.missingIndexedAncestor declaration.id)
  | [group] => .ok group
  | groups =>
      .error (.multipleIndexedAncestors declaration.id
        (groups.map (·.path)))

/-- Check one kind-neutral observed field as a parallel route to a repeatable Number target. The source kind remains with the consuming operation or presence guard. -/
def checkParallelNumericTargetRoute (model : FlatModel)
    (declaringGroup : GroupPath) (targetField : FieldId)
    (sourceReference : SurfaceFieldPath) :
    Except ParallelComputationPlanError
      (CheckedParallelNumericTargetRoute model) :=
  match hTarget : model.lookupUniqueId targetField with
  | .error error => .error (.targetResolve error)
  | .ok targetDeclaration =>
      match hSource :
          model.resolveFieldDeclarationUnchecked
            declaringGroup sourceReference with
      | .error error => .error (.operandResolve error)
      | .ok sourceDeclaration =>
          match hTargetNumber : targetDeclaration.toNumberField? with
          | none => .error (.targetNotNumber targetField)
          | some target =>
              match hPolicy :
                  targetDeclaration.toNumericTargetPolicy? with
              | none => .error (.incoherentTargetPolicy targetField)
              | some targetPolicy => do
                  let targetGroup ←
                    indexedGroupForParallelComputation
                      model targetDeclaration
                  let sourceGroup ←
                    indexedGroupForParallelComputation
                      model sourceDeclaration
                  let groups ←
                    checkParallelIndexGroups model targetGroup sourceGroup
                      |>.mapError .join
                  if hTargetGroup :
                      groups.leftGroup.path.isPrefixOf
                        targetDeclaration.groupPath = true then
                    if hSourceGroup :
                        groups.rightGroup.path.isPrefixOf
                          sourceDeclaration.groupPath = true then
                      if hTargetScope :
                          (targetDeclaration.repeatableScope ==
                            model.repeatableScopeForGroupPath
                              groups.leftGroup.path) = true then
                        if hSourceScope :
                            (sourceDeclaration.repeatableScope ==
                              model.repeatableScopeForGroupPath
                                groups.rightGroup.path) = true then
                          pure {
                            declaringGroup
                            sourceReference
                            targetField
                            targetDeclaration
                            sourceDeclaration
                            target
                            targetPolicy
                            groups
                            targetResolved := hTarget
                            sourceResolved := hSource
                            targetNumber := hTargetNumber
                            targetPolicyOwned := hPolicy
                            targetGroup := hTargetGroup
                            sourceGroup := hSourceGroup
                            targetScope := hTargetScope
                            sourceScope := hSourceScope
                          }
                        else
                          throw (.incoherentOperandScope
                            sourceDeclaration.path)
                      else
                        throw (.incoherentTargetScope
                          targetDeclaration.path)
                    else
                      throw (.incoherentOperandScope
                        sourceDeclaration.path)
                  else
                    throw (.incoherentTargetScope
                      targetDeclaration.path)

/-- Check one direct non-starred Number operand as a bounded parallel route to a repeatable Number target. No caller chooses the indexed groups or mark prefixes. -/
def checkParallelNumericComputationClearingPlan (model : FlatModel)
    (declaringGroup : GroupPath) (targetField : FieldId)
    (operandReference : SurfaceFieldPath) :
    Except ParallelComputationPlanError
      (CheckedParallelNumericClearingPlan model) := do
  let route ←
    checkParallelNumericTargetRoute
      model declaringGroup targetField operandReference
  match hOperandNumber : route.sourceDeclaration.toNumberField? with
  | none => throw (.operandNotNumber route.sourceDeclaration.path)
  | some operand =>
      pure {
        declaringGroup := route.declaringGroup
        operandReference := route.sourceReference
        targetField := route.targetField
        targetDeclaration := route.targetDeclaration
        operandDeclaration := route.sourceDeclaration
        target := route.target
        operand
        targetPolicy := route.targetPolicy
        groups := route.groups
        targetResolved := route.targetResolved
        operandResolved := route.sourceResolved
        targetNumber := route.targetNumber
        operandNumber := hOperandNumber
        targetPolicyOwned := route.targetPolicyOwned
        targetGroup := route.targetGroup
        operandGroup := route.sourceGroup
        targetScope := route.targetScope
        operandScope := route.sourceScope
      }

end A12Kernel
