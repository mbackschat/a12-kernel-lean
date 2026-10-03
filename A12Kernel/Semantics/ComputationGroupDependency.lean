import A12Kernel.Semantics.Condition

/-! # Conditional computation dependency algebra

For one queried ancestor group, the caller identifies positive group leaves that protect it.
Protection is syntactic: a conjunction needs one protecting side, a disjunction needs both, and
absent alternative conditions are omitted. The retained `src-group-conditional-profiles` grid
separates this rule from a claim that every successful computation requires the group to be filled.
Resolved group ownership, implicit repeatable guards and ordinary operand inventory remain with
the checked caller; this module neither chooses an execution order nor evaluates document values.
-/

namespace A12Kernel.ComputationGroupDependency

/-- A path avoiding every protective leaf defeats protection. Reuse the condition tree's Boolean
fold on avoidance, so connective shape is retained without a second condition representation. -/
def conditionProtects (protectsLeaf : Leaf → Bool) (condition : ConditionTree Leaf) : Bool :=
  !(condition.evalBool fun leaf => !protectsLeaf leaf)

/-- Only present alternative conditions contribute to the target's syntactic profile. An empty
collection supplies no protection; an absent condition is not an unprotected condition. -/
def alternativesProtect (protectsLeaf : Leaf → Bool)
    (conditions : List (Option (ConditionTree Leaf))) : Bool :=
  let present := conditions.filterMap id
  !present.isEmpty && present.all (conditionProtects protectsLeaf)

/-- Conditional ancestor-group references omit self and group-protected producers. Ordinary
references survive both exemptions, as the direct-field cycle controls require. -/
def requiresProducer (ordinaryReference conditionalReference sameTarget producerProtected : Bool) : Bool :=
  ordinaryReference || (conditionalReference && !sameTarget && !producerProtected)

end A12Kernel.ComputationGroupDependency
