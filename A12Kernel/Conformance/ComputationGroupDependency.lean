import A12Kernel.Semantics.ComputationGroupDependency
import A12Kernel.Elaboration.ComputationRunPlan

/-! # Conditional dependency separators

Leaf annotations answer one already-resolved ancestor-group query. The static controls and split
target outcomes in `src-group-conditional-profiles` distinguish these profiles from runtime truth.
Model/path resolution and computation scheduling are separate consumers of this algebra.
-/

namespace A12Kernel.ComputationGroupDependencyConformance

open ComputationGroupDependency

private def groupGuard : ConditionTree Bool := .leaf true
private def unrelated : ConditionTree Bool := .leaf false

example : conditionProtects id (.and groupGuard unrelated) = true ∧
    conditionProtects id (.or groupGuard unrelated) = false := by native_decide

example : alternativesProtect id [some groupGuard, none] = true ∧
    alternativesProtect id [none, some groupGuard] = true ∧
    alternativesProtect id [none] = false ∧
    alternativesProtect id [] = false := by native_decide

example : alternativesProtect id [some groupGuard, some unrelated] = false ∧
    alternativesProtect id [some (.and groupGuard unrelated), some groupGuard] = true := by
  native_decide

private def protectsGroup (targetGroup queriedGroup : List String)
    (positiveGroup : Option (List String)) : Bool :=
  positiveGroup.any fun group =>
    group.isPrefixOf targetGroup && queriedGroup.isPrefixOf group

private def rootGuard : ConditionTree (Option (List String)) := .leaf (some ["Form"])
private def boxGuard : ConditionTree (Option (List String)) := .leaf (some ["Form", "Box"])

private def depthCycle (guard : ConditionTree (Option (List String))) :
    Option (FieldId × FieldId) :=
  let producerProtected := alternativesProtect
    (protectsGroup ["Form", "Box"] ["Form", "Box"]) [some guard]
  let reads (consumer producer : FieldId) := match consumer, producer with
    | 1, 2 => requiresProducer false true false producerProtected
    | 2, 1 => requiresProducer true false false true
    | _, _ => false
  let ordered := computationAuthoredOrder id reads 2 [1, 2]
  firstForwardComputationDependency? id reads ordered

example : depthCycle (.and rootGuard boxGuard) = none ∧
    depthCycle (.or rootGuard boxGuard) = some (1, 2) := by native_decide

-- The depth grid changes one connective while retaining the reverse ordinary field edge.
example :
    let protectedAtBox := protectsGroup ["Form", "Box"] ["Form", "Box"]
    let andProfile := alternativesProtect protectedAtBox [some (.and rootGuard boxGuard)]
    let orProfile := alternativesProtect protectedAtBox [some (.or rootGuard boxGuard)]
    (requiresProducer false true false andProfile,
      requiresProducer false true false orProfile) = (false, true) := by native_decide

example :
    conditionProtects (protectsGroup ["Form", "Box"] ["Form"])
      (.leaf (some ["Form", "Other"])) = false ∧
    conditionProtects (protectsGroup ["Form", "Box"] ["Form"]) boxGuard = true := by
  native_decide

-- A distributed common guard protects both tiers; an ordinary second tier defeats protection.
example :
    alternativesProtect id [some (.and groupGuard unrelated),
      some (.and groupGuard unrelated)] = true ∧
    alternativesProtect id [some groupGuard, some unrelated] = false := by native_decide

example :
    ([(false, false, false, false), (false, true, false, false),
      (false, true, false, true), (false, true, true, false), (true, true, true, true)].map
      fun (ordinary, conditional, self, producerProtected) =>
        requiresProducer ordinary conditional self producerProtected) = [false, true, false, false, true] := by
  native_decide

end A12Kernel.ComputationGroupDependencyConformance
