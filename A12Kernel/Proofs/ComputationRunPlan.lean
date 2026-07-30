import A12Kernel.Elaboration.ComputationRunPlan

/-! # Shared supplied-order computation-plan laws -/

namespace A12Kernel

/-- A successful exceptional list traversal inherits any property proved for each successful step. -/
theorem exceptMapM_all_of_step
    (action : α → Except ε β) (property : β → Prop)
    (inputs : List α) (outputs : List β)
    (step :
      ∀ input ∈ inputs, ∀ output,
        action input = .ok output → property output)
    (mapped : inputs.mapM action = .ok outputs) :
    ∀ output ∈ outputs, property output := by
  induction inputs generalizing outputs with
  | nil =>
      change Except.ok [] = Except.ok outputs at mapped
      cases mapped
      simp
  | cons input remaining ih =>
      have remainingStep :
          ∀ candidate ∈ remaining, ∀ output,
            action candidate = .ok output → property output := by
        intro candidate member output executed
        exact step candidate (List.mem_cons_of_mem input member)
          output executed
      simp only [List.mapM_cons] at mapped
      cases head : action input with
      | error error =>
          simp [head, Bind.bind, Except.bind] at mapped
      | ok output =>
          cases tail : remaining.mapM action with
          | error error =>
              simp [head, tail, Bind.bind, Except.bind] at mapped
          | ok rest =>
              simp [head, tail, Bind.bind, Pure.pure,
                Except.bind] at mapped
              cases mapped
              intro candidate member
              rcases List.mem_cons.mp member with equal | member
              · rw [equal]
                exact step input (by simp) output head
              · exact ih rest remainingStep tail candidate member

/-- A successful exceptional traversal preserves any projection that each successful step preserves. -/
theorem exceptMapM_map_eq_of_step
    (action : α → Except ε β)
    (inputProjection : α → γ) (outputProjection : β → γ)
    (inputs : List α) (outputs : List β)
    (step :
      ∀ input ∈ inputs, ∀ output,
        action input = .ok output →
          outputProjection output = inputProjection input)
    (mapped : inputs.mapM action = .ok outputs) :
    outputs.map outputProjection = inputs.map inputProjection := by
  induction inputs generalizing outputs with
  | nil =>
      change Except.ok [] = Except.ok outputs at mapped
      cases mapped
      rfl
  | cons input remaining inductionHypothesis =>
      simp only [List.mapM_cons] at mapped
      cases head : action input with
      | error error =>
          simp [head, Bind.bind, Except.bind] at mapped
      | ok output =>
          cases tail : remaining.mapM action with
          | error error =>
              simp [head, tail, Bind.bind, Except.bind] at mapped
          | ok rest =>
              simp [head, tail, Bind.bind, Except.bind] at mapped
              cases mapped
              rw [List.map_cons, List.map_cons,
                step input (by simp) output head]
              apply congrArg (List.cons (inputProjection input))
              apply inductionHypothesis rest
              · intro candidate member result executed
                exact step candidate
                  (List.mem_cons_of_mem input member) result executed
              · exact tail

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
