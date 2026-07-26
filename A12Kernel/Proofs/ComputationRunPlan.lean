import A12Kernel.Elaboration.ComputationRunPlan

/-! # Shared supplied-order dependency-check laws -/

namespace A12Kernel

theorem firstForwardComputationDependency_none_tail
    (targetOf : Step → FieldId)
    (references : Step → FieldId → Bool)
    (step : Step) (remaining : List Step)
    (ordered :
      firstForwardComputationDependency?
        targetOf references (step :: remaining) = none) :
    firstForwardComputationDependency?
      targetOf references remaining = none := by
  unfold firstForwardComputationDependency? at ordered
  cases found : remaining.find? fun later =>
      references step (targetOf later) with
  | none => simpa [found] using ordered
  | some later => simp [found] at ordered

theorem firstForwardComputationDependency_none_suffix
    (targetOf : Step → FieldId)
    (references : Step → FieldId → Bool)
    (earlier suffix : List Step)
    (ordered :
      firstForwardComputationDependency?
        targetOf references (earlier ++ suffix) = none) :
    firstForwardComputationDependency?
      targetOf references suffix = none := by
  induction earlier with
  | nil => simpa using ordered
  | cons step remaining inductionHypothesis =>
      apply inductionHypothesis
      exact firstForwardComputationDependency_none_tail
        targetOf references step (remaining ++ suffix) (by
          simpa using ordered)

theorem firstForwardComputationDependency_none_head
    (targetOf : Step → FieldId)
    (references : Step → FieldId → Bool)
    (step : Step) (remaining : List Step)
    (ordered :
      firstForwardComputationDependency?
        targetOf references (step :: remaining) = none)
    (later : Step) (member : later ∈ remaining) :
    references step (targetOf later) = false := by
  unfold firstForwardComputationDependency? at ordered
  cases found : remaining.find? fun candidate =>
      references step (targetOf candidate) with
  | some candidate => simp [found] at ordered
  | none =>
      have notReferenced :=
        (List.find?_eq_none.mp found) later member
      cases referenced : references step (targetOf later) with
      | false => rfl
      | true => exact False.elim (notReferenced referenced)

end A12Kernel
