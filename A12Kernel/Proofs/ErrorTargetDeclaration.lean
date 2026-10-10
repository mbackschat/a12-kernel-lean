import A12Kernel.Elaboration.ErrorTargetDeclaration

/-! # Laws of the error-target declaration gates

Four results carry the family. The declaration gate is asymmetric under a lenient parse and decides
before every condition-side class, so a rule missing its error field reports that and nothing else.
The three reference roles overlap rather than partition, and the overlap is what decides which branch
of the cascade runs. The cascade itself is split by model kind, so no single model produces all three
of its classes, and within an A12 model parallel iteration decides before plain. And the custom
error-entity gate accumulates where every other gate here is first-match-wins, while still reporting
at most once per slot.
-/

namespace A12Kernel

/-- **The lenient asymmetry.** A lenient parse excuses an error field the model does not know and
does not excuse one the rule never declared. -/
theorem declarationRefusal_lenient_asymmetry :
    declarationRefusal true .absent = some .missingErrorField ∧
      declarationRefusal true (.declared false) = none :=
  ⟨rfl, rfl⟩

/-- Its strict counterpart, which is the nearest false generalisation of the law above: strict mode
refuses both, so the asymmetry is a property of lenience and not of the two classes. -/
theorem declarationRefusal_strict_refuses_both :
    declarationRefusal false .absent = some .missingErrorField ∧
      declarationRefusal false (.declared false) = some .errorFieldNotValid :=
  ⟨rfl, rfl⟩

/-- A known error field is admitted in either mode. -/
theorem declarationRefusal_known (lenient : Bool) :
    declarationRefusal lenient (.declared true) = none := by
  simp [declarationRefusal]

/-- **Nothing in the condition is read while the declaration gate refuses.** The gate throws before
the grammar runs, so the condition's own classes — syntax included — are unreachable. -/
theorem conditionParsed_iff_declaration_clear (lenient : Bool)
    (declaration : ErrorFieldDeclaration) :
    conditionParsed lenient declaration = true ↔ declarationRefusal lenient declaration = none := by
  unfold conditionParsed
  cases declarationRefusal lenient declaration <;> simp

/-- **The direct and containing roles overlap**, witnessed by an error field that is itself a
non-root group. A consumer that partitions the three roles loses this reference. -/
theorem reference_roles_overlap_direct_containing :
    ∃ reference : ConditionReference,
      reference.isDirect = true ∧ reference.isContaining = true :=
  ⟨{ sameEntity := true, isGroup := true, isRootGroup := false, ancestorOrEqual := true },
    rfl, rfl⟩

/-- The direct and form roles overlap too, witnessed by an error field that is a repeatable root
group. The two overlaps differ in consequence: this one still takes the form-only branch out, because
the branch test consults the direct role. -/
theorem reference_roles_overlap_direct_form :
    ∃ reference : ConditionReference,
      reference.isDirect = true ∧ reference.isForm = true :=
  ⟨{ sameEntity := true, isGroup := true, isRootGroup := true, ancestorOrEqual := true },
    rfl, rfl⟩

/-- A direct reference anywhere closes the form-only branch, whatever else the condition holds. -/
theorem reachedThroughFormAlone_false_of_direct (references : List ConditionReference)
    (reference : ConditionReference) (hmem : reference ∈ references)
    (hdirect : reference.isDirect = true) :
    reachedThroughFormAlone references = false := by
  simp only [reachedThroughFormAlone, Bool.and_eq_false_iff, Bool.not_eq_false']
  exact Or.inl (List.any_eq_true.2 ⟨reference, hmem, hdirect⟩)

/-- **An H model reaches only the row-iteration class**, so neither of the two the A12 branch owns. -/
theorem formOnlyIterationRefusal_hModel_classes (profile : IterationProfile) :
    formOnlyIterationRefusal true profile = none ∨
      formOnlyIterationRefusal true profile = some .errorFieldAndZIterationInvalid := by
  unfold formOnlyIterationRefusal
  cases profile.rowIteration <;> simp

/-- **An A12 model never reaches the row-iteration class.** Together with the law above this makes
the cascade's three classes unproduceable by any one model. -/
theorem formOnlyIterationRefusal_a12_never_zIteration (profile : IterationProfile) :
    formOnlyIterationRefusal false profile ≠ some .errorFieldAndZIterationInvalid := by
  unfold formOnlyIterationRefusal
  simp only [Bool.false_eq_true, if_false]
  split
  · simp
  · cases profile.firstInnerLevel <;> simp

/-- **Parallel iteration decides before plain.** Once the rule parallel-iterates at a nonzero
index-field level the inner plain level is not consulted at all, so a consumer testing plain
iteration first reports a class the Kernel does not. This module held the opposite order until the
peer measured a profile offending both in either authored text order. -/
theorem formOnlyIterationRefusal_parallel_precedes_inner (profile : IterationProfile)
    (hparallel : profile.parallelIteration = true) (hlevel : 0 < profile.indexFieldLevel) :
    formOnlyIterationRefusal false profile = some .errorFieldGroupIteration5Invalid := by
  simp [formOnlyIterationRefusal, hparallel, hlevel]

/-- **The plain class therefore needs the parallel guard clear**, which is the half a reproduction
keyed on the inner level alone loses. -/
theorem formOnlyIterationRefusal_inner_when_parallel_clear (profile : IterationProfile) (level : Nat)
    (h : profile.firstInnerLevel = some level)
    (hclear : ¬(profile.parallelIteration = true ∧ 0 < profile.indexFieldLevel)) :
    formOnlyIterationRefusal false profile = some .errorFieldGroupIteration4Invalid := by
  simp [formOnlyIterationRefusal, h, hclear]

/-- **Parallel iteration is admitted exactly at the root-group index level.** The guard reads the
rule's own index-field level, so the same condition is refused under one rule placement and admitted
under another. -/
theorem formOnlyIterationRefusal_root_index_admits_parallel (profile : IterationProfile)
    (hinner : profile.firstInnerLevel = none) (hlevel : profile.indexFieldLevel = 0) :
    formOnlyIterationRefusal false profile = none := by
  simp [formOnlyIterationRefusal, hinner, hlevel]

/-- **The declaration decides first**, ahead of every condition-side class. -/
theorem conditionSideRefusal_declaration_first (input : ErrorTargetInput)
    (refusal : KernelStaticDiagnostic)
    (h : declarationRefusal input.lenient input.declaration = some refusal) :
    conditionSideRefusal input = some refusal := by
  simp [conditionSideRefusal, h]

/-- **The sub-scope-count escape admits an unreferenced error field but does not skip the cascade.**
A condition with no references at all still runs the iteration checks, which is the corner a consumer
misses by treating the escape as an exemption from the whole gate. -/
theorem conditionSideRefusal_usb_enters_cascade (input : ErrorTargetInput)
    (hdecl : declarationRefusal input.lenient input.declaration = none)
    (hrefs : input.references = []) (husb : input.anzahlAngegebenerUsb = true) :
    conditionSideRefusal input = formOnlyIterationRefusal input.hModel input.iteration := by
  simp [conditionSideRefusal, hdecl, hrefs, husb, referencesErrorField, reachedThroughFormAlone]

/-- **The custom gate accumulates**, witnessed by a rule offending in both slots. This is the one
gate in the family that is not first-match-wins. -/
theorem customErrorEntityRefusals_accumulates :
    customErrorEntityRefusals false true [] { ifFilled := ["a"], ifNotFilled := ["b"] } =
      [.refErrorEntityIfFilledNotReferenced, .refErrorEntityIfNotFilledNotReferenced] :=
  rfl

/-- **One finding per slot**, however many paths offend. The count reports offending slots, never
offending paths. -/
theorem customErrorEntityRefusals_length_le_two (hModel conditionParsed : Bool)
    (fromCondition : List String) (declaration : CustomErrorEntityDeclaration) :
    (customErrorEntityRefusals hModel conditionParsed fromCondition declaration).length ≤ 2 := by
  unfold customErrorEntityRefusals
  split
  · simp
  · exact Nat.le_trans (List.length_filterMap_le _ _) (by simp)

/-- A condition that failed to parse suppresses both classes, because the check abandons before it
compares anything. -/
theorem customErrorEntityRefusals_unparsed (hModel : Bool) (fromCondition : List String)
    (declaration : CustomErrorEntityDeclaration) :
    customErrorEntityRefusals hModel false fromCondition declaration = [] := by
  simp [customErrorEntityRefusals]

/-- **An H model refuses every declared path**, because it offers no candidates at all. The same rule
and the same condition are therefore admitted in one model kind and refused in the other. -/
theorem customErrorEntityRefusals_hModel_refuses_declared (fromCondition : List String)
    (declaration : CustomErrorEntityDeclaration) (h : declaration.ifFilled ≠ []) :
    KernelStaticDiagnostic.refErrorEntityIfFilledNotReferenced ∈
      customErrorEntityRefusals true true fromCondition declaration := by
  have hcandidates : unreferencedPaths (candidateRelpaths true fromCondition)
      (declaration.slot .ifFilled) = declaration.ifFilled := by
    simp [unreferencedPaths, candidateRelpaths, CustomErrorEntityDeclaration.slot]
  simp [customErrorEntityRefusals, hcandidates, CustomErrorEntitySlot.refusal,
    List.isEmpty_iff, h]

end A12Kernel
