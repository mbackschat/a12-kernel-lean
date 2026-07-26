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

def WellFormed (condition : ComputationCondition) (model : FlatModel) : Prop :=
  condition.wellFormedBool model = true

end ComputationCondition

end A12Kernel
