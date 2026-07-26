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

/-- Enumerate exactly the physically instantiated target rows from the checked document. The target declaration owns the complete scope; callers cannot supply environments or fabricate rows. The inherited document order is an internal canonicalization because Kernel clearing order is not observable. -/
def targetEnvironments (plan : CheckedParallelNumericClearingPlan model)
    (checked : CheckedDocument model) :
    Except ActualRowEnvironmentError (List Env) :=
  checked.actualRowEnvironments
    plan.targetDeclaration.repeatableScope

/-- Derive the invalid-column mark plan for either checked index group. The target's complete scope remains the coverage domain in both cases. -/
def markPlanFor (plan : CheckedParallelNumericClearingPlan model) :
    ParallelComputationIndexSide → ParallelComputationMarkPlan
  | .target =>
      ParallelComputationMarkPlan.ofScopes
        plan.targetDeclaration.repeatableScope
        (model.repeatableScopeForGroupPath
          plan.groups.leftGroup.path).dropLast
  | .operand =>
      ParallelComputationMarkPlan.ofScopes
        plan.targetDeclaration.repeatableScope
        (model.repeatableScopeForGroupPath
          plan.groups.rightGroup.path).dropLast

/-- Derive the cause-blind post-loop mark keys for one checked index side. Each column is resolved at the target instance's inherited outer bindings, duplicate keys are collapsed, and the returned order is private execution detail. -/
def invalidIndexMarks (plan : CheckedParallelNumericClearingPlan model)
    (preliminary : CheckedIndexPreliminary model)
    (side : ParallelComputationIndexSide) :
    Except ParallelComputationMarkingError
      (List (ParallelComputationMark (plan.markPlanFor side))) := do
  let targetEnvironments ←
    plan.targetEnvironments preliminary.base
      |>.mapError .targetRows
  let group := match side with
    | .target => plan.groups.leftGroup
    | .operand => plan.groups.rightGroup
  let candidates ← targetEnvironments.mapM fun targetEnvironment => do
    let column ←
      preliminary.resolveIndexColumn group targetEnvironment
        |>.mapError ParallelComputationMarkingError.indexColumn
    (plan.markPlanFor side).markForUnavailable
      column.unavailableKey targetEnvironment
        |>.mapError ParallelComputationMarkingError.targetEnvironment
  pure (candidates.filterMap id).eraseDups

/-- Classify one already-enumerated target list against already-derived marks. This is the shared coverage crossing used by execution and public clearing. -/
def targetCoverageWithMarks
    (plan : CheckedParallelNumericClearingPlan model)
    (preliminary : CheckedIndexPreliminary model)
    (targetMarks :
      List (ParallelComputationMark (plan.markPlanFor .target)))
    (operandMarks :
      List (ParallelComputationMark (plan.markPlanFor .operand))) :
    Except ParallelNumericTargetCoverageError
      (List ParallelNumericTargetCoverage) := do
  let targetEnvironments ←
    plan.targetEnvironments preliminary.base
      |>.mapError .targetRows
  targetEnvironments.mapM fun environment => do
    let path ←
      environment.pathForScope plan.targetDeclaration.repeatableScope
        |>.mapError ParallelNumericTargetCoverageError.targetEnvironment
    let coveredByTarget ←
      (plan.markPlanFor .target).coversAny environment targetMarks
        |>.mapError ParallelNumericTargetCoverageError.targetEnvironment
    let coveredByOperand ←
      (plan.markPlanFor .operand).coversAny environment operandMarks
        |>.mapError ParallelNumericTargetCoverageError.targetEnvironment
    pure {
      environment
      address := { field := plan.targetField, path }
      indexInvalid := coveredByTarget || coveredByOperand
    }

/-- Derive both checked mark sets and project every actual target through their shared coverage decision. -/
def targetCoverage
    (plan : CheckedParallelNumericClearingPlan model)
    (preliminary : CheckedIndexPreliminary model) :
    Except ParallelNumericTargetCoverageError
      (List ParallelNumericTargetCoverage) := do
  let targetMarks ←
    plan.invalidIndexMarks preliminary .target
      |>.mapError (ParallelNumericTargetCoverageError.marking .target)
  let operandMarks ←
    plan.invalidIndexMarks preliminary .operand
      |>.mapError (ParallelNumericTargetCoverageError.marking .operand)
  plan.targetCoverageWithMarks preliminary targetMarks operandMarks

/-- Project both checked index sides to exact source-filled target addresses. A runtime invalid mark remains private unless it covers a target whose immutable source value is nonempty. -/
def clearedSourceTargets
    (plan : CheckedParallelNumericClearingPlan model)
    (preliminary : CheckedIndexPreliminary model) :
    Except ParallelNumericClearingError ParallelNumericClearingView := do
  let targetMarks ←
    plan.invalidIndexMarks preliminary .target
      |>.mapError (ParallelNumericClearingError.marking .target)
  let operandMarks ←
    plan.invalidIndexMarks preliminary .operand
      |>.mapError (ParallelNumericClearingError.marking .operand)
  if targetMarks.isEmpty && operandMarks.isEmpty then
    pure ParallelNumericClearingView.empty
  else
    let coverage ←
      plan.targetCoverageWithMarks preliminary targetMarks operandMarks
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

/-- Check one direct non-starred Number operand as a bounded parallel route to a repeatable Number target. No caller chooses the indexed groups or mark prefixes. -/
def checkParallelNumericComputationClearingPlan (model : FlatModel)
    (declaringGroup : GroupPath) (targetField : FieldId)
    (operandReference : SurfaceFieldPath) :
    Except ParallelComputationPlanError
      (CheckedParallelNumericClearingPlan model) :=
  match hTarget : model.lookupUniqueId targetField with
  | .error error => .error (.targetResolve error)
  | .ok targetDeclaration =>
      match hOperand :
          model.resolveFieldDeclarationUnchecked
            declaringGroup operandReference with
      | .error error => .error (.operandResolve error)
      | .ok operandDeclaration =>
          match hTargetNumber : targetDeclaration.toNumberField? with
          | none => .error (.targetNotNumber targetField)
          | some target =>
              match hOperandNumber : operandDeclaration.toNumberField? with
              | none => .error (.operandNotNumber operandDeclaration.path)
              | some operand =>
                  match hPolicy :
                      targetDeclaration.toNumericTargetPolicy? with
                  | none => .error (.incoherentTargetPolicy targetField)
                  | some targetPolicy => do
                      let targetGroup ←
                        indexedGroupForParallelComputation
                          model targetDeclaration
                      let operandGroup ←
                        indexedGroupForParallelComputation
                          model operandDeclaration
                      let groups ←
                        checkParallelIndexGroups model targetGroup operandGroup
                          |>.mapError .join
                      if hTargetGroup :
                          groups.leftGroup.path.isPrefixOf
                            targetDeclaration.groupPath = true then
                        if hOperandGroup :
                            groups.rightGroup.path.isPrefixOf
                              operandDeclaration.groupPath = true then
                          if hTargetScope :
                              (targetDeclaration.repeatableScope ==
                                model.repeatableScopeForGroupPath
                                  groups.leftGroup.path) = true then
                            if hOperandScope :
                                (operandDeclaration.repeatableScope ==
                                  model.repeatableScopeForGroupPath
                                    groups.rightGroup.path) = true then
                              pure {
                                declaringGroup
                                operandReference
                                targetField
                                targetDeclaration
                                operandDeclaration
                                target
                                operand
                                targetPolicy
                                groups
                                targetResolved := hTarget
                                operandResolved := hOperand
                                targetNumber := hTargetNumber
                                operandNumber := hOperandNumber
                                targetPolicyOwned := hPolicy
                                targetGroup := hTargetGroup
                                operandGroup := hOperandGroup
                                targetScope := hTargetScope
                                operandScope := hOperandScope
                              }
                            else
                              throw (.incoherentOperandScope
                                operandDeclaration.path)
                          else
                            throw (.incoherentTargetScope
                              targetDeclaration.path)
                        else
                          throw (.incoherentOperandScope
                            operandDeclaration.path)
                      else
                        throw (.incoherentTargetScope
                          targetDeclaration.path)

end A12Kernel
