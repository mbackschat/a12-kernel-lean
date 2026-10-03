import A12Kernel.Semantics.ComputationGroupDependency

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
