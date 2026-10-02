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
