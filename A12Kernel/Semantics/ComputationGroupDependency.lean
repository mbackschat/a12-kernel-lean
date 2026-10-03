import A12Kernel.Semantics.Condition

/-! # Conditional computation dependency algebra

For one queried ancestor group, the caller identifies positive group leaves that protect it.
Protection is syntactic: a conjunction needs one protecting side, a disjunction needs both, and
absent alternative conditions use the caller's implicit-guard context. The retained `src-group-conditional-profiles` grid
separates this rule from a claim that every successful computation requires the group to be filled.
Resolved group ownership, implicit repeatable guards and ordinary operand inventory remain with
the checked caller; this module neither chooses an execution order nor evaluates document values.
-/

namespace A12Kernel.ComputationGroupDependency

/-- A path avoiding every protective leaf defeats protection. Reuse the condition tree's Boolean
fold on avoidance, so connective shape is retained without a second condition representation. -/
def conditionProtects (protectsLeaf : Leaf → Bool) (condition : ConditionTree Leaf) : Bool :=
  !(condition.evalBool fun leaf => !protectsLeaf leaf)

/-- Assemble alternative protection after the caller supplies the implicit-guard context.
An absent condition is omitted only without an implicit guard; a guard that does not protect
this queried group contributes false, as the repeatable split-target controls require. -/
def alternativesProtect (protectsLeaf : Leaf → Bool)
    (conditions : List (Option (ConditionTree Leaf)))
    (absentProtection : Option Bool := none) : Bool :=
  let profiles := conditions.filterMap fun condition =>
    (condition.map (conditionProtects protectsLeaf)).or absentProtection
  !profiles.isEmpty && profiles.all id

/-- Conditional ancestor-group references omit self and group-protected producers. Ordinary
references survive both exemptions, as the direct-field cycle controls require. -/
def requiresProducer (ordinaryReference conditionalReference sameTarget producerProtected : Bool) : Bool :=
  ordinaryReference || (conditionalReference && !sameTarget && !producerProtected)

end A12Kernel.ComputationGroupDependency
