import A12Kernel.Elaboration.IterationLegality

/-! # Iteration and semantic-index legality laws

Three properties carry the clause. A wildcard is *absorbing*: once one has been seen, no later level may iterate or carry a semantic index. The scan is *prefix-determined*, so a refusal cannot be undone by appending levels. And the iteration class is *decided by the reference's shape* rather than by which of the three illegal-iteration conditions fired — which is why a consumer cannot read the cause off the code.
-/

namespace A12Kernel

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

/-- The iteration class is chosen by the reference's shape, not by the defect: an ordinary reference
never reports the semantic-index class and a semantic-indexed one never reports the wildcard class.
A consumer reading the code therefore learns what the reference looked like, and learns nothing
about which of the three illegal-iteration conditions fired. -/
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
        · simp only [if_true, Option.some.injEq] at h
          cases h; cases semantic <;> simp
    · simp only [Option.some.injEq] at h
      cases h
      unfold levelIterationRefusal at hl
      split at hl
      · exact absurd hl (by simp)
      · split at hl
        · cases semantic <;> simp only [if_true, Option.some.injEq] at hl <;>
            cases hl <;> simp
        · exact absurd hl (by simp)

/-- No whole-condition class arrives without parallel iteration. `RepetitionNotUnique` on its own,
a filter that iterates on its own, and an all-negative condition on its own are each admitted; only
the combination refuses. The measured control that isolates this is a rule using
`RepetitionNotUnique` and nothing else. -/
theorem conditionRefusal_needs_parallelIteration (shape : ConditionShape)
    (h : shape.parallelIteration = false) : conditionRefusal shape = none := by
  simp [conditionRefusal, h]

/-- The whole-condition gate reports `parallelIterationInvalid` only when nothing earlier fired, so
adding a positive leaf is the *only* repair for it — and a repair that leaves the two earlier
conditions untouched. -/
theorem conditionRefusal_invalid_implies_earlier_clear (shape : ConditionShape)
    (h : conditionRefusal shape = some .parallelIterationInvalid) :
    shape.repetitionNotUnique = false ∧ shape.filterIteratesOrIndexes = false ∧
      shape.parallelIteration = true ∧ shape.allLeavesNegative = true := by
  unfold conditionRefusal at h
  cases hp : shape.parallelIteration <;> cases hr : shape.repetitionNotUnique <;>
    cases hf : shape.filterIteratesOrIndexes <;> cases hn : shape.allLeavesNegative <;>
    simp_all

end A12Kernel
