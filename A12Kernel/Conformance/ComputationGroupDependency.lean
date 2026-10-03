import A12Kernel.Semantics.ComputationGroupDependency
import A12Kernel.Elaboration.ComputationRunPlan
import A12Kernel.Elaboration.ComputationGroupDependency
import A12Kernel.Elaboration.CheckedGroupPresence
import A12Kernel.Elaboration.ComputationCondition

/-! # Conditional dependency separators

Leaf annotations answer one already-resolved ancestor-group query. The static controls and split
target outcomes in `src-group-conditional-profiles` distinguish these profiles from runtime truth.
The binding section uses a validated model and resolved group references. Full guard admission and
checked-plan integration remain separate from these bounded queries through the existing scheduler.
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
    ({ path := group, origin := .path } : ResolvedGroupReference).protectsComputationGroup
      .filled targetGroup queriedGroup

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

namespace A12Kernel.ComputationGroupDependencyBindingConformance

private def model : FlatModel := {
  fields := [
    { id := 1, groupPath := ["Form"], name := "X", policy := { kind := .number { scale := 0, signed := true } } },
    { id := 2, groupPath := ["Form", "Box"], name := "Y", policy := { kind := .number { scale := 0, signed := true } } },
    { id := 3, groupPath := ["Form", "Rows"], name := "Y", policy := { kind := .number { scale := 0, signed := true } }, repeatableScope := [10] },
    { id := 4, groupPath := ["Form", "Rows", "Child"], name := "Z", policy := { kind := .number { scale := 0, signed := true } }, repeatableScope := [10] },
    { id := 5, groupPath := ["Other"], name := "Y", policy := { kind := .number { scale := 0, signed := true } } }]
  repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 3 }] }

private def root : ResolvedGroupReference := { path := ["Form"], origin := .path }
private def box : ResolvedGroupReference := { path := ["Form", "Box"], origin := .path }
private def rows : ResolvedGroupReference := { path := ["Form", "Rows"], origin := .path }
private def child : ResolvedGroupReference := { path := ["Form", "Rows", "Child"], origin := .path }

private def boundProfile (target : FieldId) (query : ResolvedGroupReference)
    (conditions : List (Option (ConditionTree (Option (GroupPresenceOperator × ResolvedGroupReference))))) :
    Bool :=
  model.computationProtectsGroup target query.path id conditions

example : model.validate.isOk = true := by native_decide

example : boundProfile 1 root [] = false ∧
    boundProfile 3 root [] = true ∧
    boundProfile 4 rows [some (.leaf none)] = true ∧
    boundProfile 4 child [] = false := by native_decide

example : boundProfile 2 root [some (.leaf (some (.filled, box)))] = true ∧
    boundProfile 2 box [some (.leaf (some (.filled, root)))] = false ∧
    boundProfile 2 root [some (.leaf (some (.notFilled, box)))] = false ∧
    boundProfile 5 root [some (.leaf (some (.filled, root)))] = false := by native_decide

example : root.referencesField model 3 = true ∧
    root.computationForbidsTarget .filled model 3 = false ∧
    root.computationForbidsTarget .notFilled model 3 = true ∧
    root.requiresComputationProducer .filled model 1 3 true = false ∧
    root.requiresComputationProducer .filled model 1 3 false = true ∧
    root.requiresComputationProducer .filled model 5 3 true = true := by native_decide

example : root.requiresComputationProducer .filled model 1 1 false = false ∧
    root.requiresComputationProducer .notFilled model 1 1 true = true ∧
    root.referencesField model 5 = false := by native_decide

example : boundProfile 2 root [some (.leaf (some (.filled, root))), none] = true ∧
    boundProfile 2 root [some (.leaf (some (.filled, root))), some (.leaf none)] = false ∧
    boundProfile 4 child [some (.leaf (some (.filled, child)))] = true := by native_decide

-- The repeatable-profile grid rejects both split-target orders below a fixed child; the
-- containing row still protects its own level, and nonrepeatable omission remains unchanged.
example : boundProfile 4 child [some (.leaf (some (.filled, child))), none] = false ∧
    boundProfile 4 child [none, some (.leaf (some (.filled, child)))] = false ∧
    boundProfile 4 rows [some (.leaf (some (.filled, child))), none] = true ∧
    boundProfile 2 box [some (.leaf (some (.filled, box))), none] = true := by
  native_decide

example : (model.computationGroupSource root.path).fields.contains 3 = false ∧
    root.referencesField model 3 = true := by native_decide

example : boundProfile 99 root [some (.leaf (some (.filled, root)))] = false ∧
    boundProfile 3 { path := [], origin := .path } [] = false := by native_decide

private def rootCycle (guard : ConditionTree (Option (GroupPresenceOperator × ResolvedGroupReference))) :
    Option (FieldId × FieldId) :=
  let reads (consumer producer : FieldId) :=
    root.requiresComputationProducer .filled model consumer producer
      (model.computationProtectsGroup producer root.path id [some guard])
  firstForwardComputationDependency? id reads (computationAuthoredOrder id reads 2 [1, 2])

example :
    let positive := ConditionTree.leaf (some (GroupPresenceOperator.filled, root))
    rootCycle positive = none ∧ rootCycle (.or positive (.leaf none)) = some (1, 2) := by
  native_decide

example : root.computationForbidsTarget .notFilled model 5 = false ∧
    root.requiresComputationProducer .filled model 1 5 false = false := by native_decide

private def rootCondition : Except ComputationConditionElabError ComputationCondition :=
  model.elaborateComputationCondition ["Form"] ["Form"]
    (.groupPresence .filled (.path { base := .absolute, groups := ["Form"] }))

example : rootCondition.toOption.map (fun guard =>
    (guard.referencesField 1, guard.referencesField 3, guard.forbidsTarget 1)) = some (true, true, false) := by native_decide

example : rootCondition.toOption.map (fun guard => match guard.evalChecked {
    read := fun _ => { rawPresent := false, parsed := none, findings := [] } } with
    | .error .groupContextRequired => true | _ => false) = some true := by native_decide

example : rootCondition.toOption.map (fun guard => match guard.evalChecked {
    read := fun _ => { rawPresent := false, parsed := none, findings := [] }
    addressed := some {
      document := { instantiatedRows := [], rawCells := fun _ => none }
      read := fun _ _ => { rawPresent := true, parsed := none, findings := [.computedDependency] } } } with
    | .ok .notTrue => true | _ => false) = some true := by native_decide

example : rootCondition.toOption.map (fun guard => match guard with
    | .leaf (.groupPresence operator source) =>
        (!ComputationCondition.wellFormedBool (.leaf (.groupPresence operator { source with members := [] })) model) &&
        (!ComputationCondition.wellFormedBool (.leaf (.groupPresence operator
          { source with reference := { source.reference with boundRepeatableScope := [10] } })) model)
    | _ => false) = some true := by native_decide

example : (model.elaborateComputationCondition ["Form", "Rows"] ["Form", "Rows"]
    (.groupPresence .filled (.ruleGroup false))).toOption.map (fun guard => match guard with
    | .leaf (.groupPresence _ source) =>
        source.reference.origin == .ruleGroup && source.reference.boundRepeatableScope == [10]
    | _ => false) = some true := by native_decide

end A12Kernel.ComputationGroupDependencyBindingConformance
