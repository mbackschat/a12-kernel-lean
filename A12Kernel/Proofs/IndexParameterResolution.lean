import A12Kernel.Elaboration.IndexParameterResolution

/-! # Laws of the `index(...)` parameter's resolution and repeatability stages

Three consequences a consumer can rely on without re-deriving the cascade.

The **mismatch class is exactly disagreement**, in both directions, which is the fact a repair tool needs
in order to know that either side may be the one to change.

The **two branch-local classes are mutually exclusive for a fixed model**, not merely for a fixed
condition. Which of them is even reachable is settled by the error field's own group before any condition
is read, so an Explain consumer may present them as alternatives rather than as a pair, and a diagnostic
corpus containing both is evidence of two models.

**Resolution dominates**, so a resolution class is reported whatever the condition contains.
-/

namespace A12Kernel

/-- The mismatch class is raised exactly when the two sides disagree about repeatability, so it is
symmetric in them and names neither side's state. -/
theorem repeatabilityRefusal_mismatch_iff (errorPathRepeatable : Bool)
    (referenced : ReferencedIndexField) :
    repeatabilityRefusal errorPathRepeatable referenced =
        some .indexFieldRepeatabilityMismatch ↔
      referenced.repeatable ≠ errorPathRepeatable := by
  obtain ⟨rep, iter, ft⟩ := referenced
  cases rep <;> cases errorPathRepeatable <;> cases iter <;>
    cases hft : ft.admitsNonRepeatable <;>
    simp [repeatabilityRefusal, hft]

/-- The not-iterating class is reachable only from a repeatable error path. -/
theorem repeatabilityRefusal_notIterating_repeatable {errorPathRepeatable : Bool}
    {referenced : ReferencedIndexField}
    (h : repeatabilityRefusal errorPathRepeatable referenced = some .indexFieldNotIterating) :
    errorPathRepeatable = true := by
  obtain ⟨rep, iter, ft⟩ := referenced
  cases rep <;> cases errorPathRepeatable <;> cases iter <;>
    cases hft : ft.admitsNonRepeatable <;>
    simp [repeatabilityRefusal, hft] at h ⊢

/-- The non-repeatable-Enumeration class is reachable only from a non-repeatable error path. -/
theorem repeatabilityRefusal_nonRepEnum_not_repeatable {errorPathRepeatable : Bool}
    {referenced : ReferencedIndexField}
    (h : repeatabilityRefusal errorPathRepeatable referenced = some .indexFieldNonRepeatableEnum) :
    errorPathRepeatable = false := by
  obtain ⟨rep, iter, ft⟩ := referenced
  cases rep <;> cases errorPathRepeatable <;> cases iter <;>
    cases hft : ft.admitsNonRepeatable <;>
    simp [repeatabilityRefusal, hft] at h ⊢

/-- Both branch facts survive the scan over the condition's referenced set. -/
theorem repeatabilityScan_notIterating_repeatable {errorPathRepeatable : Bool} :
    ∀ referenced : List ReferencedIndexField,
      repeatabilityScan errorPathRepeatable referenced = some .indexFieldNotIterating →
        errorPathRepeatable = true
  | [], h => by simp [repeatabilityScan] at h
  | row :: rest, h => by
      rw [repeatabilityScan] at h
      cases hrow : repeatabilityRefusal errorPathRepeatable row with
      | none =>
          rw [hrow] at h
          exact repeatabilityScan_notIterating_repeatable rest h
      | some refusal =>
          rw [hrow] at h
          simp only [Option.some.injEq] at h
          exact repeatabilityRefusal_notIterating_repeatable (h ▸ hrow)

theorem repeatabilityScan_nonRepEnum_not_repeatable {errorPathRepeatable : Bool} :
    ∀ referenced : List ReferencedIndexField,
      repeatabilityScan errorPathRepeatable referenced = some .indexFieldNonRepeatableEnum →
        errorPathRepeatable = false
  | [], h => by simp [repeatabilityScan] at h
  | row :: rest, h => by
      rw [repeatabilityScan] at h
      cases hrow : repeatabilityRefusal errorPathRepeatable row with
      | none =>
          rw [hrow] at h
          exact repeatabilityScan_nonRepEnum_not_repeatable rest h
      | some refusal =>
          rw [hrow] at h
          simp only [Option.some.injEq] at h
          exact repeatabilityRefusal_nonRepEnum_not_repeatable (h ▸ hrow)

/-- **The payoff law.** For one model — one error field, one indexed group — no two conditions can
produce these two classes between them. The branch is fixed before any condition is read, so the pair is
unreachable rather than merely unobserved. -/
theorem indexFieldBranchClassesExclusive (errorPathRepeatable : Bool)
    (first second : List ReferencedIndexField) :
    ¬(repeatabilityScan errorPathRepeatable first = some .indexFieldNotIterating ∧
      repeatabilityScan errorPathRepeatable second = some .indexFieldNonRepeatableEnum) := by
  rintro ⟨hFirst, hSecond⟩
  have hTrue := repeatabilityScan_notIterating_repeatable first hFirst
  have hFalse := repeatabilityScan_nonRepEnum_not_repeatable second hSecond
  rw [hTrue] at hFalse
  exact Bool.noConfusion hFalse

/-- A resolution refusal is reported whatever the condition references, so the three resolution classes
carry no information about the condition. -/
theorem resolution_dominates {path : ErrorPathIndexFields} {refusal : KernelStaticDiagnostic}
    (h : resolutionRefusal path = some refusal) (referenced : List ReferencedIndexField) :
    indexParameterRefusal true path referenced = some refusal := by
  simp [indexParameterRefusal, h]

/-- With no parsed condition the whole cascade is suppressed, including the resolution stage, which
needs no condition of its own. -/
theorem indexParameterRefusal_unavailable (path : ErrorPathIndexFields)
    (referenced : List ReferencedIndexField) :
    indexParameterRefusal false path referenced = none := by
  simp [indexParameterRefusal]

end A12Kernel
