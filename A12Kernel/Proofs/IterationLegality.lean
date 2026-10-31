import A12Kernel.Elaboration.IterationLegality

/-! # Iteration and semantic-index legality laws

Three properties carry the clause. A wildcard is *absorbing*: once one has been seen, no later level may iterate or carry a semantic index. The scan is *prefix-determined*, so a refusal cannot be undone by appending levels. And the iteration class is *decided by where the reference stands*, inside a semantic index's key or outside it, rather than by which of the three illegal-iteration conditions fired — which is why a consumer cannot read the cause off the code.
-/

namespace A12Kernel

namespace FilterRuleFacts

/-- Regrouping already admitted fragments preserves the complete global admission summary.
This permits common and alternative guards to share the generated rule's final gate (spec/09 §6). -/
theorem merge_assoc (first second third : FilterRuleFacts) :
    (first.merge second).merge third = first.merge (second.merge third) := by
  cases first
  cases second
  cases third
  simp [FilterRuleFacts.merge, Bool.or_assoc, Nat.add_assoc]

end FilterRuleFacts

/-- A wildcard absorbs: with the bit already set, any later level that iterates or carries a
semantic index refuses. This is the law behind "a wildcard poisons every level below it", and it is
what makes the same reference legal above a wildcard and illegal below it. -/
theorem indexScan_wildcard_absorbs (semantic : Bool) (levels : List IndexLevel)
    (h : ∃ level ∈ levels, level.marker = .iteration ∨ level.marker = .semanticIndex) :
    (indexScan semantic levels true).isSome := by
  induction levels with
  | nil => simp at h
  | cons level rest ih =>
    obtain ⟨witness, hMem, hWitness⟩ := h
    have tail : level.marker ≠ .iteration → level.marker ≠ .semanticIndex →
        ∃ x ∈ rest, x.marker = .iteration ∨ x.marker = .semanticIndex := by
      intro h1 h2
      rcases List.mem_cons.mp hMem with rfl | hRest
      · rcases hWitness with hq | hq
        · exact absurd hq h1
        · exact absurd hq h2
      · exact ⟨witness, hRest, hWitness⟩
    unfold indexScan
    cases hm : level.marker with
    | iteration => simp [levelIterationRefusal, hm]
    | semanticIndex => simp [levelIterationRefusal, hm]
    | fixed => simpa [levelIterationRefusal, hm] using ih (tail (by simp [hm]) (by simp [hm]))
    | unspecified => simpa [levelIterationRefusal, hm] using ih (tail (by simp [hm]) (by simp [hm]))
    | wildcard => simpa [levelIterationRefusal, hm] using ih (tail (by simp [hm]) (by simp [hm]))

/-- The scan is prefix-determined: a refusal found in a prefix is the answer for every extension, so
"first match wins" is a theorem rather than a reading of the recursion. -/
theorem indexScan_prefix_determines (semantic : Bool) :
    ∀ (prefixLevels suffixLevels : List IndexLevel) (outerWildcard : Bool)
      (refusal : IterationRefusal),
      indexScan semantic prefixLevels outerWildcard = some refusal →
        indexScan semantic (prefixLevels ++ suffixLevels) outerWildcard = some refusal := by
  intro prefixLevels
  induction prefixLevels with
  | nil => intro _ _ _ h; simp [indexScan] at h
  | cons level rest ih =>
    intro suffixLevels outerWildcard refusal h
    rw [List.cons_append]
    unfold indexScan at h ⊢
    cases hl : levelIterationRefusal level outerWildcard semantic <;> simp only [hl] at h ⊢
    · cases hm : level.marker <;> simp only [hm] at h ⊢
      case fixed => exact ih _ _ _ h
      case wildcard => exact ih _ _ _ h
      case iteration => exact ih _ _ _ h
      case unspecified => exact ih _ _ _ h
      case semanticIndex =>
        cases outerWildcard
        · simpa using ih _ _ _ (by simpa using h)
        · simpa using h
    · exact h

/-- The iteration class is chosen by where the reference stands, not by the defect: a reference
outside a semantic index's key never reports the semantic-index class, and one read inside the key
never reports the wildcard class. A consumer reading the code therefore learns where the reference
stood, and learns nothing about which of the three illegal-iteration conditions fired. -/
theorem indexScan_class_follows_reference (semantic : Bool) :
    ∀ (levels : List IndexLevel) (outerWildcard : Bool) (refusal : IterationRefusal),
      indexScan semantic levels outerWildcard = some refusal →
        refusal ≠ (if semantic then IterationRefusal.noWildcard
                   else IterationRefusal.semanticIndexInvalidIter) := by
  intro levels
  induction levels with
  | nil => intro _ _ h; simp [indexScan] at h
  | cons level rest ih =>
    intro outerWildcard refusal h
    unfold indexScan at h
    cases hl : levelIterationRefusal level outerWildcard semantic <;> simp only [hl] at h
    · cases hm : level.marker <;> simp only [hm] at h
      case fixed => exact ih _ _ h
      case wildcard => exact ih _ _ h
      case iteration => exact ih _ _ h
      case unspecified => exact ih _ _ h
      case semanticIndex =>
        cases outerWildcard
        · exact ih _ _ (by simpa using h)
        · simp only [ite_true, Option.some.injEq] at h
          cases h; cases semantic <;> simp
    · simp only [Option.some.injEq] at h
      cases h
      unfold levelIterationRefusal at hl
      split at hl
      · exact absurd hl (by simp)
      · split at hl
        · cases semantic <;> simp only [ite_true, Option.some.injEq] at hl <;>
            cases hl <;> simp
        · exact absurd hl (by simp)

/-- Removing outer parallel iteration preserves all filter-owned and earlier global refusals. -/
theorem conditionRefusal_without_parallelIteration (facts : FilterRuleFacts) (guards : ConditionTree Bool)
    (h : facts.parallelIteration = false) : conditionRefusal facts guards = facts.beforeIterationRefusal? := by
  cases earlier : facts.beforeIterationRefusal? <;> simp [conditionRefusal, earlier, h]

/-- An earlier global or raw-Length refusal masks the final structural guard independently of its tree. -/
theorem conditionRefusal_preserves_earlier_refusal (facts : FilterRuleFacts) (guards : ConditionTree Bool)
    (diagnostic : KernelStaticDiagnostic) (h : facts.beforeIterationRefusal? = some diagnostic) :
    conditionRefusal facts guards = some diagnostic := by
  simp [conditionRefusal, h]

/-- After the shared pre-iteration gate passes, parallel admission is exactly structural guardedness. -/
theorem conditionRefusal_parallel_guard_iff (facts : FilterRuleFacts) (guards : ConditionTree Bool)
    (hp : facts.parallelIteration = true) (he : facts.beforeIterationRefusal? = none) :
    conditionRefusal facts guards = none ↔ guards.iterationGuarded id = true := by
  cases hg : guards.iterationGuarded id <;> simp [conditionRefusal, hp, he, hg]

/-- A refused reference prefix fixes the filter walk's diagnostic independently of later reads. -/
theorem filterReferenceWalk_prefix_determines (front suffix : List FilterIndexedReference)
    (diagnostic : KernelStaticDiagnostic) (h : filterReferenceWalk front = .error diagnostic) :
    filterReferenceWalk (front ++ suffix) = .error diagnostic := by
  induction front with
  | nil => simp [filterReferenceWalk] at h
  | cons reference rest ih =>
      cases hMarked : reference.marked <;>
        cases hHere : filterIndexScan reference.levels false <;>
        cases hRest : filterReferenceWalk rest <;>
        simp_all [filterReferenceWalk, Bind.bind, Pure.pure, Except.pure, Except.bind]

end A12Kernel
