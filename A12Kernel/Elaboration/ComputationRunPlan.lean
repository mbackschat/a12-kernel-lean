import A12Kernel.Document

/-! # Shared supplied-order computation dependency check

This helper checks one invariant shared by typed computation families: a step may not read a target owned by itself or a later supplied step. It does not construct a graph, choose an order, or erase the family's checked table type.
-/

namespace A12Kernel

/-- Return the first supplied-order step that reads a target owned by itself or a later step. -/
def firstForwardComputationDependency?
    (targetOf : Step → FieldId)
    (references : Step → FieldId → Bool) :
    List Step → Option (FieldId × FieldId)
  | [] => none
  | step :: remaining =>
      match remaining.find? fun later =>
          references step (targetOf later) with
      | some dependency => some (targetOf step, targetOf dependency)
      | none => firstForwardComputationDependency?
          targetOf references remaining

end A12Kernel
