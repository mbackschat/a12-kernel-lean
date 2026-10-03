import A12Kernel.Semantics.ComputationGroupDependency
import A12Kernel.Elaboration.ComputationGroupDependency

/-! # Syntactic group-protection laws

These laws connect the shared Boolean fold to the dependency profile and establish that its
exemptions cannot erase ordinary reads. They make no runtime truth or kernel-equivalence claim.
-/

namespace A12Kernel.ComputationGroupDependency

theorem conditionProtects_and (protectsLeaf : Leaf → Bool)
    (left right : ConditionTree Leaf) :
    conditionProtects protectsLeaf (.and left right) =
      (conditionProtects protectsLeaf left || conditionProtects protectsLeaf right) := by
  simp only [conditionProtects, ConditionTree.evalBool]
  cases left.evalBool (fun leaf => !protectsLeaf leaf) <;>
    cases right.evalBool (fun leaf => !protectsLeaf leaf) <;> rfl

theorem conditionProtects_or (protectsLeaf : Leaf → Bool)
    (left right : ConditionTree Leaf) :
    conditionProtects protectsLeaf (.or left right) =
      (conditionProtects protectsLeaf left && conditionProtects protectsLeaf right) := by
  simp only [conditionProtects, ConditionTree.evalBool]
  cases left.evalBool (fun leaf => !protectsLeaf leaf) <;>
    cases right.evalBool (fun leaf => !protectsLeaf leaf) <;> rfl

/-- Inserting an unconditional alternative anywhere leaves the profile unchanged, even though
it can change first-match execution. This is the split-target grid's nearest non-law. -/
theorem alternativesProtect_insert_absent (protectsLeaf : Leaf → Bool)
    (before after : List (Option (ConditionTree Leaf))) :
    alternativesProtect protectsLeaf (before ++ none :: after) =
      alternativesProtect protectsLeaf (before ++ after) := by
  simp [alternativesProtect, List.filterMap_append]

theorem requiresProducer_of_ordinary (conditionalReference sameTarget producerProtected : Bool) :
    requiresProducer true conditionalReference sameTarget producerProtected = true := by
  rfl

end A12Kernel.ComputationGroupDependency

namespace A12Kernel

theorem negativeGroupRead_preservesOperandDependency (reference : ResolvedGroupReference)
    (model : FlatModel) (consumer producer : FieldId) (producerProtected : Bool) :
    reference.requiresComputationProducer .notFilled model consumer producer producerProtected =
      reference.referencesField model producer := by
  simp [ResolvedGroupReference.requiresComputationProducer,
    ComputationGroupDependency.requiresProducer]

theorem positiveGroupRead_excludesOwnDependency (reference : ResolvedGroupReference)
    (model : FlatModel) (target : FieldId) (producerProtected : Bool) :
    reference.requiresComputationProducer .filled model target target producerProtected = false := by
  cases member : reference.referencesField model target <;>
    simp [ResolvedGroupReference.requiresComputationProducer,
      ComputationGroupDependency.requiresProducer, member]

theorem implicitGroupProtection_preserved (model : FlatModel) (target : FieldId)
    (declaration : FlatFieldDecl)
    (queriedGroup : GroupPath)
    (groupLeaf : Leaf → Option (GroupPresenceOperator × ResolvedGroupReference))
    (conditions : List (Option (ConditionTree Leaf)))
    (resolved : model.lookupUniqueId target = .ok declaration)
    (ownedGroup : model.hasGroupPath queriedGroup = true)
    (implicitProtection : model.computationImplicitGroupProtection declaration.groupPath queriedGroup = true) :
    model.computationProtectsGroup target queriedGroup groupLeaf conditions = true := by
  simp [FlatModel.computationProtectsGroup, resolved, ownedGroup, implicitProtection]

end A12Kernel
