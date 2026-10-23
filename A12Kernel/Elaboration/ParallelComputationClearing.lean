import A12Kernel.Elaboration.CheckedIndexColumn
import A12Kernel.Elaboration.NumericComputation.SourceTarget
import A12Kernel.Semantics.ParallelComputationClearing

/-! # Checked parallel-computation clearing plans

This boundary recognizes one direct non-starred observed field in an indexed group parallel to a repeatable Number target's indexed group. Both declarations and both groups come from one validated model; the existing checked parallel-group owner proves index-name/kind and scope compatibility. It derives side-specific mark scopes, resolves checked index columns over actual target rows, and projects covered source-filled targets to an extensional clearing fragment. The original direct Number-operand plan is retained as a stronger specialization; presence guards reuse the kind-neutral route without weakening Number expression admission. The key join under the route, with its target rows and index marks, is independent of the target's kind, so a joined String or temporal target uses it directly. Starred operands, table execution, successful repeatable outcomes, and application remain separate. -/

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
  | targetIsIndexField (field : FieldId)
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
  /-- The row lies beyond its own group's declared repeatability. It stays in this inventory rather
  than being dropped from it, because the Kernel writes a clear there: measured on this carrier with
  a **resolvable** join at the excess row, which separates capacity exclusion from an empty
  execution domain ([`SPEC-2026-08-31-08`](https://github.com/mbackschat/a12-kernel-lean/blob/a050f1506bedaab7078d4121ad2b3378c2a43052/docs/archived/A12-DMKITS-SPEC-SYNC-LEDGER-ACCEPTED-THROUGH-2026-09-24.md#spec-2026-08-31-08)). -/
  overLimit : Bool
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

/-- One model-certified key join from a repeatable target row to the indexed group of one observed field. It is independent of the target's kind: a Number route adds the target's Number certificate, and a String or temporal target's joined step uses the join alone. The target row inventory and both index sides' invalid marks belong here, because they read only the target declaration and the two groups. -/
structure CheckedParallelTargetJoin (model : FlatModel) where
  private mk ::
  declaringGroup : GroupPath
  sourceReference : SurfaceFieldPath
  targetField : FieldId
  targetDeclaration : FlatFieldDecl
  sourceDeclaration : FlatFieldDecl
  groups : CheckedParallelIndexGroups model
  targetResolved :
    model.lookupUniqueId targetField = .ok targetDeclaration
  sourceResolved :
    model.resolveFieldDeclarationUnchecked declaringGroup sourceReference =
      .ok sourceDeclaration
  targetGroup :
    groups.leftGroup.path.isPrefixOf targetDeclaration.groupPath = true
  sourceGroup :
    groups.rightGroup.path.isPrefixOf sourceDeclaration.groupPath = true
  targetScope :
    (model.repeatableScopeForGroupPath groups.leftGroup.path).isPrefixOf
      targetDeclaration.repeatableScope = true
  targetScopeUnique : targetDeclaration.repeatableScope.Nodup
  sourceScope :
    (sourceDeclaration.repeatableScope ==
      model.repeatableScopeForGroupPath groups.rightGroup.path) = true

namespace CheckedParallelTargetJoin

/-- Enumerate every physically instantiated target row from the checked document, over-limit rows included. The two dispositions are taken later: execution skips an over-limit row and clearing writes one. Enumerating only in-capacity rows here would collapse the distinction the Kernel draws, since a dropped row and a cleared row differ exactly on a seeded cell. The target declaration owns the complete scope; callers cannot supply environments or fabricate rows. The inherited document order is an internal canonicalization because Kernel clearing order is not observable. -/
def targetEnvironments (join : CheckedParallelTargetJoin model)
    (checked : CheckedDocument model) :
    Except ActualRowEnvironmentError (List Env) :=
  checked.actualRowEnvironments
    join.targetDeclaration.repeatableScope

/-- Derive one checked index side's cause-blind invalid-mark plan. The target's complete scope remains the coverage domain for every observed group. -/
def markPlanFor (join : CheckedParallelTargetJoin model) :
    ParallelComputationIndexSide → ParallelComputationMarkPlan
  | .target =>
      ParallelComputationMarkPlan.ofScopes
        join.targetDeclaration.repeatableScope
        (model.repeatableScopeForGroupPath
          join.groups.leftGroup.path).dropLast
  | .operand =>
      ParallelComputationMarkPlan.ofScopes
        join.targetDeclaration.repeatableScope
        (model.repeatableScopeForGroupPath
          join.groups.rightGroup.path).dropLast

/-- Derive cause-blind post-loop mark keys for one checked index side. Each column is resolved at the target instance's inherited outer bindings, duplicate keys are collapsed, and the returned order is private execution detail. -/
def invalidIndexMarks (join : CheckedParallelTargetJoin model)
    (preliminary : CheckedIndexPreliminary model)
    (side : ParallelComputationIndexSide) :
    Except ParallelComputationMarkingError
      (List (ParallelComputationMark (join.markPlanFor side))) := do
  let targetEnvironments ←
    join.targetEnvironments preliminary.base
      |>.mapError .targetRows
  let group := match side with
    | .target => join.groups.leftGroup
    | .operand => join.groups.rightGroup
  let candidates ← targetEnvironments.mapM fun targetEnvironment => do
    let column ←
      preliminary.resolveIndexColumn group targetEnvironment
        |>.mapError ParallelComputationMarkingError.indexColumn
    (join.markPlanFor side).markForUnavailable
      column.unavailableKey targetEnvironment
        |>.mapError ParallelComputationMarkingError.targetEnvironment
  pure (candidates.filterMap id).eraseDups

/-- Classify one already-enumerated target list against already-derived marks from both checked sides. This is the shared coverage crossing used by execution and public clearing. -/
def targetCoverageWithMarks
    (join : CheckedParallelTargetJoin model)
    (preliminary : CheckedIndexPreliminary model)
    (targetMarks :
      List (ParallelComputationMark (join.markPlanFor .target)))
    (operandMarks :
      List (ParallelComputationMark (join.markPlanFor .operand))) :
    Except ParallelNumericTargetCoverageError
      (List ParallelNumericTargetCoverage) := do
  let targetEnvironments ←
    join.targetEnvironments preliminary.base
      |>.mapError .targetRows
  targetEnvironments.mapM fun environment => do
    let path ←
      environment.pathForScope join.targetDeclaration.repeatableScope
        |>.mapError ParallelNumericTargetCoverageError.targetEnvironment
    let coveredByTarget ←
      (join.markPlanFor .target).coversAny environment targetMarks
        |>.mapError ParallelNumericTargetCoverageError.targetEnvironment
    let coveredByOperand ←
      (join.markPlanFor .operand).coversAny environment operandMarks
        |>.mapError ParallelNumericTargetCoverageError.targetEnvironment
    pure {
      environment
      address := { field := join.targetField, path }
      indexInvalid := coveredByTarget || coveredByOperand
      overLimit :=
        preliminary.base.environmentOverLimit
          join.targetDeclaration.repeatableScope environment
    }

/-- Derive both checked mark sets and project every actual target through their shared coverage decision. -/
def targetCoverage
    (join : CheckedParallelTargetJoin model)
    (preliminary : CheckedIndexPreliminary model) :
    Except ParallelNumericTargetCoverageError
      (List ParallelNumericTargetCoverage) := do
  let targetMarks ←
    join.invalidIndexMarks preliminary .target
      |>.mapError (ParallelNumericTargetCoverageError.marking .target)
  let operandMarks ←
    join.invalidIndexMarks preliminary .operand
      |>.mapError (ParallelNumericTargetCoverageError.marking .operand)
  join.targetCoverageWithMarks preliminary targetMarks operandMarks

end CheckedParallelTargetJoin

/-- One model-certified parallel route from a repeatable Number target to any directly observed field: a key join (`join`) with the target's Number certificate. The source field's kind is deliberately unconstrained because computation presence guards are kind-neutral. -/
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
    (model.repeatableScopeForGroupPath groups.leftGroup.path).isPrefixOf
      targetDeclaration.repeatableScope = true
  targetScopeUnique : targetDeclaration.repeatableScope.Nodup
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
    (model.repeatableScopeForGroupPath route.groups.leftGroup.path).isPrefixOf
      route.targetDeclaration.repeatableScope = true ∧
    route.targetDeclaration.repeatableScope.Nodup ∧
    (route.sourceDeclaration.repeatableScope ==
      model.repeatableScopeForGroupPath route.groups.rightGroup.path) = true

/-- The route's key join, without its Number certificate. -/
def join (route : CheckedParallelNumericTargetRoute model) : CheckedParallelTargetJoin model := {
  declaringGroup := route.declaringGroup
  sourceReference := route.sourceReference
  targetField := route.targetField
  targetDeclaration := route.targetDeclaration
  sourceDeclaration := route.sourceDeclaration
  groups := route.groups
  targetResolved := route.targetResolved
  sourceResolved := route.sourceResolved
  targetGroup := route.targetGroup
  sourceGroup := route.sourceGroup
  targetScope := route.targetScope
  targetScopeUnique := route.targetScopeUnique
  sourceScope := route.sourceScope
}

/-- Whether one classified target contributes a public clear, and at which address.

    A target is cleared when a runtime invalid mark on either index side covers it, or when its row
    lies beyond the group's declared repeatability. Either way the clear stays private unless the
    target's immutable source value is nonempty, so the result reports a value the Kernel removes
    rather than an intent to remove one.

    Named rather than inlined because the clearing law reasons about this step at every classified
    target; an anonymous lambda there is not addressable by a rewrite. -/
def clearCandidate (base : CheckedDocument model)
    (target : ParallelNumericTargetCoverage) :
    Except ParallelNumericClearingError (Option CellAddr) := do
  if !target.indexInvalid && !target.overLimit then
    pure none
  else
    let source ←
      base.numericTargetStateAt target.address
        |>.mapError ParallelNumericClearingError.sourceTarget
    if source.sourceIdentity.isSome then
      pure (some target.address)
    else
      pure none

/-- Project every actual target to the addresses this route clears: one covered by a runtime invalid mark on either index side, and one beyond its group's declared repeatability. Both remain private unless the target's immutable source value is nonempty, so a clear reports a value the Kernel removes rather than an intent. There is no short circuit on an empty mark set, because an over-limit row clears in a document whose every index column is clean. -/
def clearedSourceTargets
    (route : CheckedParallelNumericTargetRoute model)
    (preliminary : CheckedIndexPreliminary model) :
    Except ParallelNumericClearingError ParallelNumericClearingView := do
  let targetMarks ←
    route.join.invalidIndexMarks preliminary .target
      |>.mapError (ParallelNumericClearingError.marking .target)
  let operandMarks ←
    route.join.invalidIndexMarks preliminary .operand
      |>.mapError (ParallelNumericClearingError.marking .operand)
  let coverage ←
    route.join.targetCoverageWithMarks preliminary targetMarks operandMarks
      |>.mapError fun
        | .marking side error => .marking side error
        | .targetRows error => .targetRows error
        | .targetEnvironment error => .targetEnvironment error
  let candidates ← coverage.mapM (clearCandidate preliminary.base)
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
    (model.repeatableScopeForGroupPath groups.leftGroup.path).isPrefixOf
      targetDeclaration.repeatableScope = true
  targetScopeUnique : targetDeclaration.repeatableScope.Nodup
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
    (model.repeatableScopeForGroupPath plan.groups.leftGroup.path).isPrefixOf
      plan.targetDeclaration.repeatableScope = true ∧
    plan.targetDeclaration.repeatableScope.Nodup ∧
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
  targetScopeUnique := plan.targetScopeUnique
  sourceScope := plan.operandScope
}

def targetEnvironments (plan : CheckedParallelNumericClearingPlan model)
    (checked : CheckedDocument model) :
    Except ActualRowEnvironmentError (List Env) :=
  plan.asTargetRoute.join.targetEnvironments checked

def markPlanFor (plan : CheckedParallelNumericClearingPlan model) :
    ParallelComputationIndexSide → ParallelComputationMarkPlan
  | side => plan.asTargetRoute.join.markPlanFor side

def invalidIndexMarks (plan : CheckedParallelNumericClearingPlan model)
    (preliminary : CheckedIndexPreliminary model)
    (side : ParallelComputationIndexSide) :
    Except ParallelComputationMarkingError
      (List (ParallelComputationMark (plan.markPlanFor side))) := do
  plan.asTargetRoute.join.invalidIndexMarks preliminary side

def targetCoverageWithMarks
    (plan : CheckedParallelNumericClearingPlan model)
    (preliminary : CheckedIndexPreliminary model)
    (targetMarks :
      List (ParallelComputationMark (plan.markPlanFor .target)))
    (operandMarks :
      List (ParallelComputationMark (plan.markPlanFor .operand))) :
    Except ParallelNumericTargetCoverageError
      (List ParallelNumericTargetCoverage) :=
  plan.asTargetRoute.join.targetCoverageWithMarks
    preliminary targetMarks operandMarks

def targetCoverage
    (plan : CheckedParallelNumericClearingPlan model)
    (preliminary : CheckedIndexPreliminary model) :
    Except ParallelNumericTargetCoverageError
      (List ParallelNumericTargetCoverage) :=
  plan.asTargetRoute.join.targetCoverage preliminary

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

/-- Check one observed field's key join to a repeatable target of any kind. The target is never an index field; each side's single indexed group must form a checked parallel pair. The source's scope must be exactly its group's; the target's may continue below its joined group, each of its rows then joining its joined row's key ([checkpoint](../../docs/sources/model-structure-and-declaration-probes.md#src-group-target-nested-join), `computations`). -/
def checkParallelTargetJoin (model : FlatModel)
    (declaringGroup : GroupPath) (targetField : FieldId)
    (sourceReference : SurfaceFieldPath) :
    Except ParallelComputationPlanError
      (CheckedParallelTargetJoin model) :=
  match hTarget : model.lookupUniqueId targetField with
  | .error error => .error (.targetResolve error)
  | .ok targetDeclaration =>
      match hSource :
          model.resolveFieldDeclarationUnchecked
            declaringGroup sourceReference with
      | .error error => .error (.operandResolve error)
      | .ok sourceDeclaration => do
          if model.isIndexField targetField then
            throw (.targetIsIndexField targetField)
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
                  (model.repeatableScopeForGroupPath groups.leftGroup.path).isPrefixOf
                    targetDeclaration.repeatableScope = true then
                if hTargetScopeUnique :
                    targetDeclaration.repeatableScope.Nodup then
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
                      groups
                      targetResolved := hTarget
                      sourceResolved := hSource
                      targetGroup := hTargetGroup
                      sourceGroup := hSourceGroup
                      targetScope := hTargetScope
                      targetScopeUnique := hTargetScopeUnique
                      sourceScope := hSourceScope
                    }
                  else
                    throw (.incoherentOperandScope
                      sourceDeclaration.path)
                else
                  throw (.incoherentTargetScope
                    targetDeclaration.path)
              else
                throw (.incoherentTargetScope
                  targetDeclaration.path)
            else
              throw (.incoherentOperandScope
                sourceDeclaration.path)
          else
            throw (.incoherentTargetScope
              targetDeclaration.path)

/-- Check one kind-neutral observed field as a parallel route to a repeatable Number target: its key join, then the target's Number certificate. The source kind remains with the consuming operation or presence guard. -/
def checkParallelNumericTargetRoute (model : FlatModel)
    (declaringGroup : GroupPath) (targetField : FieldId)
    (sourceReference : SurfaceFieldPath) :
    Except ParallelComputationPlanError
      (CheckedParallelNumericTargetRoute model) := do
  let join ← checkParallelTargetJoin model declaringGroup targetField sourceReference
  match hTargetNumber : join.targetDeclaration.toNumberField? with
  | none => throw (.targetNotNumber targetField)
  | some target =>
      match hPolicy : join.targetDeclaration.toNumericTargetPolicy? with
      | none => throw (.incoherentTargetPolicy targetField)
      | some targetPolicy =>
          pure {
            declaringGroup := join.declaringGroup
            sourceReference := join.sourceReference
            targetField := join.targetField
            targetDeclaration := join.targetDeclaration
            sourceDeclaration := join.sourceDeclaration
            target
            targetPolicy
            groups := join.groups
            targetResolved := join.targetResolved
            sourceResolved := join.sourceResolved
            targetNumber := hTargetNumber
            targetPolicyOwned := hPolicy
            targetGroup := join.targetGroup
            sourceGroup := join.sourceGroup
            targetScope := join.targetScope
            targetScopeUnique := join.targetScopeUnique
            sourceScope := join.sourceScope
          }

/-- Check one direct non-starred Number operand as a bounded parallel route to a repeatable Number target. No caller chooses the indexed groups or mark prefixes.

    The operand is a field-value read, so a group draws the group class and a raw String and a
    partially known Date their value classes, ahead of the Number check
    ([checkpoint](../../docs/sources/static-admission-and-class-probes.md#src-field-value-read-predictions)).
    A group meets the computation reader's walk from the target's scope, which passes the operand's
    own keyed level as a legal parallel iteration, so that group and a fixed group inside it draw the
    group class, measured, while a repeatable group the join does not bind keeps the walk's class.
    The kind-neutral route stays ungated, since a presence guard's operand is not a value read. -/
def checkParallelNumericComputationClearingPlan (model : FlatModel)
    (declaringGroup : GroupPath) (targetField : FieldId)
    (operandReference : SurfaceFieldPath) :
    Except ParallelComputationPlanError
      (CheckedParallelNumericClearingPlan model) := do
  let route ←
    (checkParallelNumericTargetRoute model declaringGroup targetField operandReference).mapError fun
      | .operandResolve miss =>
          let targetGroup := match model.lookupUniqueId targetField with
            | .ok declaration => declaration.groupPath
            | .error _ => declaringGroup
          .operandResolve (displaceGroupMiss miss
            (model.computationGroupRead declaringGroup targetGroup operandReference))
      | error => error
  if let some refusal := route.sourceDeclaration.fieldValueReadRefusal? then
    throw (.operandResolve refusal)
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
        targetScopeUnique := route.targetScopeUnique
        operandScope := route.sourceScope
      }

end A12Kernel
