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

/-- Without implicit guards, inserting an absent condition leaves the profile unchanged, even
though it can change first-match execution. The fixed split-target grid separates these roles. -/
theorem alternativesProtect_insert_absent (protectsLeaf : Leaf → Bool)
    (before after : List (Option (ConditionTree Leaf))) :
    alternativesProtect protectsLeaf (before ++ none :: after) =
      alternativesProtect protectsLeaf (before ++ after) := by
  simp [alternativesProtect, List.filterMap_append]

theorem requiresProducer_of_ordinary (conditionalReference sameTarget producerProtected : Bool) :
    requiresProducer true conditionalReference sameTarget producerProtected = true := by
  rfl

/-- An implicit condition that misses the queried group prevents protection at that group,
regardless of every explicit alternative around it. -/
theorem alternativesProtect_insert_unprotected (protectsLeaf : Leaf → Bool)
    (before after : List (Option (ConditionTree Leaf))) :
    alternativesProtect protectsLeaf (before ++ none :: after) (some false) = false := by
  simp [alternativesProtect, List.filterMap_append]

theorem alternativesProtect_perm (protectsLeaf : Leaf → Bool)
    {left right : List (Option (ConditionTree Leaf))} (permuted : left.Perm right)
    (absentProtection : Option Bool := none) :
    alternativesProtect protectsLeaf left absentProtection =
      alternativesProtect protectsLeaf right absentProtection := by
  have profiles := permuted.filterMap (fun condition =>
    (condition.map (conditionProtects protectsLeaf)).or absentProtection)
  dsimp only [alternativesProtect]
  rw [profiles.isEmpty_eq, profiles.all_eq]

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

/-- Self-dependency is exactly the static target ban, independently of producer protection. -/
@[simp] theorem computationCondition_requires_own (condition : ComputationCondition)
    (target : FieldId) (producerProtected : ResolvedGroupReference → Bool) :
    condition.requiresProducer target target producerProtected = condition.forbidsTarget target := by
  induction condition with
  | leaf leaf =>
      cases leaf with
      | groupPresence operator source =>
          cases operator with
          | filled =>
              simp [ComputationCondition.requiresProducer, ComputationCondition.forbidsTarget,
                ComputationGroupDependency.requiresProducer]
          | notFilled =>
              simp [ComputationCondition.requiresProducer, ComputationCondition.forbidsTarget,
                ComputationCondition.referencesField, ComputationGroupDependency.requiresProducer]
      | _ => rfl
  | and left right leftIH rightIH | or left right leftIH rightIH =>
      simp [ComputationCondition.requiresProducer, ComputationCondition.forbidsTarget, leftIH, rightIH]

/-- Reordering computations cannot change a producer's syntactic group profile. -/
theorem computationProducerProtection_perm (model : FlatModel) (targetOf : Step → FieldId)
    (conditionsOf : Step → List (Option ComputationCondition)) {left right : List Step}
    (permuted : left.Perm right) (producer : FieldId) (reference : ResolvedGroupReference) :
    computationProducerProtection model targetOf conditionsOf left producer reference =
      computationProducerProtection model targetOf conditionsOf right producer reference := by
  unfold computationProducerProtection FlatModel.computationProtectsGroup
  have conditionsPerm := (permuted.filter (fun step => targetOf step == producer)).flatMap_right conditionsOf
  cases resolution : model.lookupUniqueId producer with
  | error error => rfl
  | ok declaration =>
      simp only
      rw [ComputationGroupDependency.alternativesProtect_perm _ conditionsPerm _]

end A12Kernel
