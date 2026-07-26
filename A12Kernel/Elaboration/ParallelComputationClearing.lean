import A12Kernel.Elaboration.CheckedIndexColumn

/-! # Checked parallel-computation clearing plans

This bounded constructor recognizes one direct non-starred Number operand in an indexed group parallel to a repeatable Number target's indexed group. Both declarations and both groups come from one validated model; the existing checked parallel-group owner proves index-name/kind and scope compatibility. The resulting mark plans derive their truncation scopes from those declarations. General computation expressions, guards, starred operands, table execution, index-column evaluation, and public clearing remain separate. -/

namespace A12Kernel

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
