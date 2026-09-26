import A12Kernel.Elaboration.ComputationRunPlan

/-! # Shared computation-plan laws

The supplied-order dependency check and the authored-order rule are proved once here; each family plan specializes them to its own step type.
-/

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

/-- Selecting a ready step removes it from the scanned list and changes nothing else. -/
theorem firstReadyComputationStep_perm
    (targetOf : Step → FieldId) (references : Step → FieldId → Bool)
    (pending : List Step) :
    ∀ (scan rest : List Step) (ready : Step),
      firstReadyComputationStep? targetOf references pending scan = some (ready, rest) →
        (ready :: rest).Perm scan := by
  intro scan
  induction scan with
  | nil => intro _ _ selected; simp [firstReadyComputationStep?] at selected
  | cons step tail ih =>
    intro rest ready selected
    unfold firstReadyComputationStep? at selected
    split at selected
    · simp only [Option.some.injEq, Prod.mk.injEq] at selected
      obtain ⟨rfl, rfl⟩ := selected
      exact List.Perm.refl _
    · cases hTail : firstReadyComputationStep? targetOf references pending tail with
      | none => simp [hTail] at selected
      | some found =>
        obtain ⟨found, remaining⟩ := found
        simp only [hTail, Option.map_some, Option.some.injEq, Prod.mk.injEq] at selected
        obtain ⟨sameReady, sameRest⟩ := selected
        rw [← sameReady, ← sameRest]
        exact (List.Perm.swap _ _ remaining).trans
          (List.Perm.cons step (ih remaining found hTail))

/-- Ordering only reorders: every authored step is run exactly once. -/
theorem computationAuthoredOrder_perm
    (targetOf : Step → FieldId) (references : Step → FieldId → Bool) :
    ∀ (fuel : Nat) (pending : List Step),
      (computationAuthoredOrder targetOf references fuel pending).Perm pending := by
  intro fuel
  induction fuel with
  | zero => intro pending; exact List.Perm.refl _
  | succ fuel ih =>
    intro pending
    unfold computationAuthoredOrder
    split
    · exact List.Perm.refl _
    · rename_i ready remaining selected
      exact (List.Perm.cons ready (ih remaining)).trans
        (firstReadyComputationStep_perm targetOf references pending pending remaining ready
          selected)

/-- A selected step reads no target of another pending step. -/
theorem firstReadyComputationStep_ready
    (targetOf : Step → FieldId) (references : Step → FieldId → Bool)
    (pending : List Step) :
    ∀ (scan rest : List Step) (ready : Step),
      firstReadyComputationStep? targetOf references pending scan = some (ready, rest) →
        ∀ other ∈ pending, targetOf other ≠ targetOf ready →
          references ready (targetOf other) = false := by
  intro scan
  induction scan with
  | nil => intro _ _ selected; simp [firstReadyComputationStep?] at selected
  | cons step tail ih =>
    intro rest ready selected other member distinct
    unfold firstReadyComputationStep? at selected
    split at selected
    · rename_i allReady
      simp only [Option.some.injEq, Prod.mk.injEq] at selected
      obtain ⟨rfl, rfl⟩ := selected
      have := List.all_eq_true.mp allReady other member
      simpa [beq_false_of_ne distinct] using this
    · cases hTail : firstReadyComputationStep? targetOf references pending tail with
      | none => simp [hTail] at selected
      | some found =>
        obtain ⟨found, remaining⟩ := found
        simp only [hTail, Option.map_some, Option.some.injEq, Prod.mk.injEq] at selected
        rw [← selected.1]
        exact ih remaining found hTail other member (selected.1 ▸ distinct)

/-- When no step is ready, every scanned step reads the target of another pending step. -/
theorem firstReadyComputationStep_none
    (targetOf : Step → FieldId) (references : Step → FieldId → Bool)
    (pending : List Step) :
    ∀ scan : List Step,
      firstReadyComputationStep? targetOf references pending scan = none →
        ∀ step ∈ scan, ∃ other ∈ pending,
          targetOf other ≠ targetOf step ∧ references step (targetOf other) = true := by
  intro scan
  induction scan with
  | nil => intro _ step member; simp at member
  | cons head tail ih =>
    intro stuck step member
    unfold firstReadyComputationStep? at stuck
    split at stuck
    · simp at stuck
    · rename_i notReady
      rcases List.mem_cons.mp member with rfl | member
      · have blockedBy : ∃ other ∈ pending,
            (targetOf other == targetOf step || !references step (targetOf other)) =
              false := by
          simpa [List.all_eq_true] using notReady
        obtain ⟨other, otherMember, blocked⟩ := blockedBy
        have blocked : targetOf other ≠ targetOf step ∧
            references step (targetOf other) = true := by
          simpa using blocked
        exact ⟨other, otherMember, blocked⟩
      · cases hTail : firstReadyComputationStep? targetOf references pending tail with
        | none => exact ih hTail step member
        | some found => simp [hTail] at stuck

/-- Where the authored order keeps a forward read, some of the ordered steps are read-closed. -/
theorem computationAuthoredOrder_forward_readClosed
    (targetOf : Step → FieldId) (references : Step → FieldId → Bool) :
    ∀ (fuel : Nat) (pending : List Step),
      pending.length ≤ fuel →
      (pending.map targetOf).Nodup →
      firstForwardComputationDependency? targetOf references
          (computationAuthoredOrder targetOf references fuel pending) ≠ none →
        ∃ stuck, ComputationStepsReadClosed targetOf references stuck ∧
          ∀ step ∈ stuck, step ∈ pending := by
  intro fuel
  induction fuel with
  | zero =>
    intro pending short _ forward
    have : pending = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp short)
    subst this
    simp [computationAuthoredOrder, firstForwardComputationDependency?] at forward
  | succ fuel ih =>
    intro pending short unique forward
    unfold computationAuthoredOrder at forward
    split at forward
    · rename_i noneReady
      refine ⟨pending, ⟨?_, firstReadyComputationStep_none targetOf references pending pending
        noneReady⟩, fun _ member => member⟩
      intro empty
      subst empty
      simp [firstForwardComputationDependency?] at forward
    · rename_i ready remaining selected
      have selectedPerm :=
        firstReadyComputationStep_perm targetOf references pending pending remaining ready selected
      have orderPerm := computationAuthoredOrder_perm targetOf references fuel remaining
      have uniqueSelected : ((ready :: remaining).map targetOf).Nodup :=
        (selectedPerm.map _).nodup_iff.mpr unique
      have readyAbsent : targetOf ready ∉ remaining.map targetOf :=
        (List.nodup_cons.mp uniqueSelected).1
      unfold firstForwardComputationDependency? at forward
      split at forward
      · rename_i later found
        have laterMember := List.mem_of_find?_eq_some found
        have reads := List.find?_some found
        have laterRemaining := orderPerm.mem_iff.mp laterMember
        have laterPending := selectedPerm.mem_iff.mp (List.mem_cons_of_mem ready laterRemaining)
        have distinct : targetOf later ≠ targetOf ready := fun same =>
          readyAbsent (same ▸ List.mem_map_of_mem laterRemaining)
        have unread := firstReadyComputationStep_ready targetOf references pending pending
          remaining ready selected later laterPending distinct
        simp [unread] at reads
      · rename_i _
        obtain ⟨stuck, closed, within⟩ := ih remaining
          (by
            have := selectedPerm.length_eq
            simp at this
            omega)
          (List.nodup_cons.mp uniqueSelected).2 forward
        exact ⟨stuck, closed, fun step member =>
          selectedPerm.mem_iff.mp (List.mem_cons_of_mem ready (within step member))⟩

/-- Steps with no forward read hold no read-closed steps. -/
theorem computationSteps_not_readClosed
    (targetOf : Step → FieldId) (references : Step → FieldId → Bool) :
    ∀ (steps stuck : List Step),
      firstForwardComputationDependency? targetOf references steps = none →
      ComputationStepsReadClosed targetOf references stuck →
        ¬ ∀ member ∈ stuck, member ∈ steps := by
  intro steps
  induction steps with
  | nil =>
    intro stuck _ closed within
    obtain ⟨step, member⟩ := List.exists_mem_of_ne_nil _ closed.1
    simpa using within step member
  | cons head tail ih =>
    intro stuck ordered closed within
    have tailOrdered :=
      firstForwardComputationDependency_none_tail targetOf references head tail ordered
    by_cases headStuck : head ∈ stuck
    · obtain ⟨other, otherStuck, distinct, reads⟩ := closed.2 head headStuck
      have otherTail : other ∈ tail := by
        rcases List.mem_cons.mp (within other otherStuck) with same | member
        · exact absurd (same ▸ rfl) distinct
        · exact member
      have := firstForwardComputationDependency_none_head targetOf references head tail ordered
        other otherTail
      simp [reads] at this
    · apply ih stuck tailOrdered closed
      intro member memberStuck
      rcases List.mem_cons.mp (within member memberStuck) with same | inTail
      · exact absurd (same ▸ memberStuck) headStuck
      · exact inTail

/-- Two authored steps with distinct targets, where the first reads the second's target and the
second does not read the first's, run producer first: the two-step case of the authored order. -/
theorem computationAuthoredOrder_pair_forward
    (targetOf : Step → FieldId) (references : Step → FieldId → Bool)
    (first second : Step)
    (distinct : targetOf first ≠ targetOf second)
    (forward : references first (targetOf second) = true)
    (backward : references second (targetOf first) = false) :
    computationAuthoredOrder targetOf references 2 [first, second] = [second, first] := by
  have firstSecond := beq_false_of_ne distinct
  have secondFirst := beq_false_of_ne (Ne.symm distinct)
  simp [computationAuthoredOrder, firstReadyComputationStep?, firstSecond, secondFirst,
    forward, backward]

/-- Two authored steps where the first does not read the second's target keep authored order. -/
theorem computationAuthoredOrder_pair_preserved
    (targetOf : Step → FieldId) (references : Step → FieldId → Bool)
    (first second : Step)
    (forward : references first (targetOf second) = false) :
    computationAuthoredOrder targetOf references 2 [first, second] = [first, second] := by
  simp [computationAuthoredOrder, firstReadyComputationStep?, forward]

end A12Kernel
