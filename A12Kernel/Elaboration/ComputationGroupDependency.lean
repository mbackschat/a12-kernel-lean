import A12Kernel.Elaboration.SingleGroup
import A12Kernel.Semantics.GroupPresence
import A12Kernel.Semantics.ComputationGroupDependency
import A12Kernel.Semantics.ComputationCondition

/-! # Model-bound computation group dependencies

These queries resolve target identities and consume resolved group references after model
validation. Group membership remains the complete subtree inventory, independently of which cells
presence evaluation reads. Positive ancestor-group references alone receive the conditional
scheduling exemption; negative and foreign-group reads retain their ordinary field dependencies.
The profile query also retains the target's implicit repeatable-group protection. Static guard
admission and construction of a complete computation plan remain caller responsibilities.
-/

namespace A12Kernel

/-- A positive group leaf protects an ancestor query only when the leaf's group contains the
computed target. The depth and connective controls are in `src-group-conditional-profiles`. -/
def ResolvedGroupReference.protectsComputationGroup (reference : ResolvedGroupReference)
    (operator : GroupPresenceOperator) (targetGroup queriedGroup : GroupPath) : Bool :=
  match operator with
  | .filled => reference.path.isPrefixOf targetGroup && queriedGroup.isPrefixOf reference.path
  | .notFilled => false

/-- An enclosing repeatable group supplies implicit protection of itself and its ancestors.
Fixed descendants below that group still need their own positive guard; the one-level producer
control is retained in `src-group-conditional-profiles`. -/
def FlatModel.computationImplicitGroupProtection (model : FlatModel)
    (targetGroup queriedGroup : GroupPath) : Bool :=
  model.repeatableGroups.any fun group =>
    group.path.isPrefixOf targetGroup && queriedGroup.isPrefixOf group.path

/-- Query a resolved target's profile after common-precondition distribution and same-target
assembly. The leaf selector retains operator and resolved group identity; ordinary leaves return
none. Kernel dependency preparation supplies implicit row guards before target assembly
(`src-repeatable-group-profiles`), so absence below that row is an unprotected condition rather
than an omitted condition. Static admission permits absence only in a sole alternative
(`src-repeatable-row-alternatives`), so this projection needs no authored-computation partition.
Implicit protection of the row itself remains unconditional. Unknown targets or group paths
establish no protection; this query does not replace static admission. -/
def FlatModel.computationProtectsGroup (model : FlatModel) (target : FieldId)
    (queriedGroup : GroupPath)
    (groupLeaf : Leaf → Option (GroupPresenceOperator × ResolvedGroupReference))
    (conditions : List (Option (ConditionTree Leaf))) : Bool :=
  match model.lookupUniqueId target with
  | .error _ => false
  | .ok declaration =>
      let implicitProtection := model.computationImplicitGroupProtection declaration.groupPath queriedGroup
      let absentProtection := if declaration.repeatableScope.isEmpty then none else some implicitProtection
      model.hasGroupPath queriedGroup &&
        (implicitProtection ||
          ComputationGroupDependency.alternativesProtect (fun leaf =>
            (groupLeaf leaf).any fun (operator, reference) =>
              model.hasGroupPath reference.path &&
                reference.protectsComputationGroup operator declaration.groupPath queriedGroup) conditions absentProtection)

/-- Positive reads of a containing group are exempt from the computed-target reference ban;
negative reads retain it, as `spec/09` §5's paired group controls establish. -/
def ResolvedGroupReference.computationForbidsTarget (reference : ResolvedGroupReference)
    (operator : GroupPresenceOperator) (model : FlatModel) (target : FieldId) : Bool :=
  match operator with
  | .filled => false
  | .notFilled => reference.referencesField model target

/-- Only a positive reference containing the consumer uses producer protection. Preserve the
full group inventory for other reads; the profile does not change operand membership. -/
def ResolvedGroupReference.requiresComputationProducer (reference : ResolvedGroupReference)
    (operator : GroupPresenceOperator) (model : FlatModel) (consumer producer : FieldId)
    (producerProtected : Bool) : Bool :=
  let referenced := reference.referencesField model producer
  let conditional := match operator with
    | .filled => reference.referencesField model consumer
    | .notFilled => false
  ComputationGroupDependency.requiresProducer (referenced && !conditional)
    (referenced && conditional) (consumer == producer) producerProtected

/-- Assemble a producer's present conditions across every authored computation of that target.
Callers supply common-expanded conditions; the model-bound query accounts for implicit guards. -/
def computationProducerProtection (model : FlatModel) (targetOf : Step → FieldId)
    (conditionsOf : Step → List (Option (ComputationConditionOf Atom Predicate))) (steps : List Step)
    (producer : FieldId) (reference : ResolvedGroupReference) : Bool :=
  model.computationProtectsGroup producer reference.path ComputationConditionLeaf.groupReference?
    ((steps.filter (fun step => targetOf step == producer)).flatMap conditionsOf)

end A12Kernel
