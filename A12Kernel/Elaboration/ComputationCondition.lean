import A12Kernel.Elaboration.Flat.Model
import A12Kernel.Semantics.ComputationCondition

/-! # Model-certified computation conditions

Direct computation-presence guards accept every nonrepeatable scalar declaration. Value-kind restrictions belong to the operation that consumes the field, not to presence.
-/

namespace A12Kernel

namespace ComputationCondition

/-- Check that every direct computation-presence leaf names one model-owned nonrepeatable scalar declaration. -/
def wellFormedBool (condition : ComputationCondition) (model : FlatModel) : Bool :=
  match condition with
  | .leaf (.fieldFilled field) | .leaf (.fieldNotFilled field) =>
      match model.lookupUniqueId field with
      | .ok declaration => declaration.repeatableScope.isEmpty
      | .error _ => false
  | .and left right | .or left right =>
      left.wellFormedBool model && right.wellFormedBool model

/-- Check that every presence leaf names one model-owned declaration whose repeatable levels the row
scope `scope` binds, so one row of that scope reads each leaf at exactly one cell. -/
def rowBoundBool (condition : ComputationCondition) (model : FlatModel)
    (scope : List RepeatableLevel) : Bool :=
  match condition with
  | .leaf (.fieldFilled field) | .leaf (.fieldNotFilled field) =>
      match model.lookupUniqueId field with
      | .ok declaration => declaration.repeatableScope.isPrefixOf scope
      | .error _ => false
  | .and left right | .or left right =>
      left.rowBoundBool model scope && right.rowBoundBool model scope

def WellFormed (condition : ComputationCondition) (model : FlatModel) : Prop :=
  condition.wellFormedBool model = true

end ComputationCondition

/-- A computation precondition as authored, its presence leaves naming their field by path. -/
inductive SurfaceComputationCondition where
  | fieldFilled (field : SurfaceFieldPath)
  | fieldNotFilled (field : SurfaceFieldPath)
  | and (left right : SurfaceComputationCondition)
  | or (left right : SurfaceComputationCondition)
  deriving Repr, DecidableEq

/-- Resolve one presence leaf's field as a computation operand, bound by the target's scope rather
than the declaring group's, a name reaching a group taking the group slot's class: a fixed group draws
`MVK_NO_GROUPS_ALLOWED` and an unbound repeatable one its level's class, as an unbound field does
([checkpoint](../../docs/sources/computation-scheduling-probes.md#src-computation-precondition-names)). -/
private def FlatModel.resolveComputationPresence (model : FlatModel)
    (declaringGroup targetGroup : GroupPath) (reference : SurfaceFieldPath) :
    Except ResolveError FieldId :=
  (·.id) <$> model.resolvePresenceOperand declaringGroup targetGroup reference
    (model.resolveNonrepeatableComputationOperandUnchecked declaringGroup targetGroup reference)

/-- Resolve a precondition's names left to right against a validated model, so its first unresolved
name is the one reported. -/
def FlatModel.elaborateComputationCondition (model : FlatModel)
    (declaringGroup targetGroup : GroupPath) :
    SurfaceComputationCondition → Except ResolveError ComputationCondition
  | .fieldFilled reference =>
      (.leaf ∘ .fieldFilled) <$> model.resolveComputationPresence declaringGroup targetGroup reference
  | .fieldNotFilled reference =>
      (.leaf ∘ .fieldNotFilled) <$> model.resolveComputationPresence declaringGroup targetGroup reference
  | .and left right => do
      let left ← model.elaborateComputationCondition declaringGroup targetGroup left
      pure (.and left (← model.elaborateComputationCondition declaringGroup targetGroup right))
  | .or left right => do
      let left ← model.elaborateComputationCondition declaringGroup targetGroup left
      pure (.or left (← model.elaborateComputationCondition declaringGroup targetGroup right))

/-- The one-based position of the first alternative whose guard its carrier refuses. A table's
certifier asks this of every alternative before any alternative's own class, as the Kernel asks a
guard's name and its index gates ahead of an unguarded alternative wherever either stands
([checkpoint](../../docs/sources/computation-scheduling-probes.md#src-join-operators-and-guards)). -/
def ComputationAlternative.firstUnadmittedGuard? {Operation : Type}
    (admits : ComputationCondition → Bool) (alternatives : List (ComputationAlternative Operation)) :
    Option Nat :=
  (alternatives.zipIdx.find? fun (alternative, _) => !alternative.precondition.all admits).map
    (·.2 + 1)

end A12Kernel
