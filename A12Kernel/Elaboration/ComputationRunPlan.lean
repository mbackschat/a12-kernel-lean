import A12Kernel.Document

/-! # Shared computation dependency check and authored order

The first helper checks one invariant shared by typed computation families: a step may not read a target owned by a later supplied step. The second puts an authored plan into dependency order by running the earliest authored step that reads no other pending target. Both deliberately say nothing about a step reading its own target; each family must state separately what its checked construction establishes. Neither constructs a graph or erases the family's checked step type.
-/

namespace A12Kernel

/-- Return the first supplied-order step that reads a target owned by a later step. -/
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

/-- The first step of `scan` that reads no target of another step in `pending`, and `scan`
without it. A step's own target does not block it: a self-read is the family owner's refusal. -/
def firstReadyComputationStep?
    (targetOf : Step → FieldId)
    (references : Step → FieldId → Bool)
    (pending : List Step) : List Step → Option (Step × List Step)
  | [] => none
  | step :: rest =>
      if pending.all fun other =>
          targetOf other == targetOf step || !references step (targetOf other) then
        some (step, rest)
      else
        (firstReadyComputationStep? targetOf references pending rest).map
          fun (ready, remaining) => (ready, step :: remaining)

/-- Run the earliest authored step that reads no other pending target, then repeat. When every
pending step reads another pending target, the steps left form or wait on a cycle and stay in
authored order, where the family's certification reports the first forward read among them.
Among the orders that run every producer before its readers, the result is the least by authored
position, compared step by step. Which of those orders the Kernel takes is unmeasured: independent
steps read nothing of each other, and no retained row separates two of them. -/
def computationAuthoredOrder
    (targetOf : Step → FieldId)
    (references : Step → FieldId → Bool) : Nat → List Step → List Step
  | 0, pending => pending
  | fuel + 1, pending =>
      match firstReadyComputationStep? targetOf references pending pending with
      | none => pending
      | some (ready, remaining) =>
          ready :: computationAuthoredOrder targetOf references fuel remaining

/-- Steps none of which can run first: the list is nonempty and each member reads the target of
another member. Following reads inside such a list must revisit a step, so it closes a cycle, and a
step waiting on a cycle lies in one with it. -/
def ComputationStepsReadClosed
    (targetOf : Step → FieldId)
    (references : Step → FieldId → Bool) (stuck : List Step) : Prop :=
  stuck ≠ [] ∧ ∀ step ∈ stuck, ∃ other ∈ stuck,
    targetOf other ≠ targetOf step ∧ references step (targetOf other) = true

end A12Kernel
