import A12Kernel.Elaboration.IndexGroupResolution

/-! # Laws of the index-group walk

Three results carry the family. Only the innermost index group's declared count is examined, so a
second index group above it outranks its own multiplicity — and the two classes therefore swap when
one nesting is spelled the other way round. The name is resolved strictly after the walk, so a path
that already refuses never reports the name class. And a path with no index group is a clear result
rather than a refusal, which is what keeps the ordinary model out of this vocabulary entirely.
-/

namespace A12Kernel

/-- Groups declaring no index are invisible to the walk, so inserting one changes nothing. -/
theorem indexGroupWalk_skips_nonIndex (found : Option IndexDeclaringGroup)
    (group : IndexDeclaringGroup) (outer : List IndexDeclaringGroup)
    (h : group.declaresIndex = false) :
    indexGroupWalk found (group :: outer) = indexGroupWalk found outer := by
  simp [indexGroupWalk, h]

/-- **A path with no index group never refuses**, and resolves to nothing. -/
theorem indexResolution_none_of_no_index (path : List IndexDeclaringGroup)
    (h : ∀ group ∈ path, group.declaresIndex = false) :
    indexResolution path = .ok none := by
  have walk : ∀ found, indexGroupWalk found path = .ok found := by
    intro found
    induction path with
    | nil => rfl
    | cons group outer ih =>
      rw [indexGroupWalk_skips_nonIndex found group outer (h group (by simp))]
      exact ih fun g hg => h g (by simp [hg])
  simp [indexResolution, walk none]

/-- **The two-groups class outranks the several-names class**, witnessed by one nesting spelled two
ways: the inner group's count decides only when it is the sole index group. -/
theorem indexGroupWalk_outer_outranks_inner_count :
    indexResolutionRefusal [{ declaredNames := 1 }, { declaredNames := 3 }] =
        some .multipleIndexFields ∧
      indexResolutionRefusal [{ declaredNames := 3 }, { declaredNames := 1 }] =
        some .multipleIndexFields2 :=
  ⟨rfl, rfl⟩

/-- The walk is therefore **not** symmetric in the path: the same two groups in the other order give
a different class. Stated separately because it is the property a consumer collecting index groups
into a set silently loses. -/
theorem indexResolutionRefusal_order_matters :
    ∃ inner outer : IndexDeclaringGroup,
      indexResolutionRefusal [inner, outer] ≠ indexResolutionRefusal [outer, inner] := by
  refine ⟨{ declaredNames := 1 }, { declaredNames := 3 }, ?_⟩
  decide

/-- Membership in the index-group list survives prepending any group. -/
theorem mem_indexDeclaringGroups_cons (target group : IndexDeclaringGroup)
    (outer : List IndexDeclaringGroup) (h : target ∈ indexDeclaringGroups outer) :
    target ∈ indexDeclaringGroups (group :: outer) := by
  simp only [indexDeclaringGroups, List.mem_filter] at h ⊢
  exact ⟨List.mem_cons_of_mem group h.1, h.2⟩

/-- **Several-names implies the innermost index group declares several.** The class cannot be
reported for an outer group, which is what makes the pair above a genuine ordering and not a
coincidence of the witness. -/
theorem multipleIndexFields2_is_innermost :
    ∀ (found : Option IndexDeclaringGroup) (path : List IndexDeclaringGroup),
      indexGroupWalk found path = .error .multipleIndexFields2 →
        ∃ group ∈ indexDeclaringGroups path, group.declaredNames > 1 := by
  intro found path
  induction path generalizing found with
  | nil => intro hp; simp [indexGroupWalk] at hp
  | cons group outer ih =>
    intro hp
    by_cases hdecl : group.declaresIndex = true
    · simp only [indexGroupWalk, hdecl, Bool.not_true, Bool.false_eq_true, ite_false] at hp
      cases found with
      | some _ => simp at hp
      | none =>
        by_cases hcount : group.declaredNames > 1
        · refine ⟨group, ?_, hcount⟩
          simp only [indexDeclaringGroups, List.mem_filter]
          exact ⟨List.mem_cons_self, hdecl⟩
        · simp only [hcount, ite_false] at hp
          obtain ⟨target, hmem, hgt⟩ := ih (some group) hp
          exact ⟨target, mem_indexDeclaringGroups_cons target group outer hmem, hgt⟩
    · simp only [Bool.not_eq_true] at hdecl
      rw [indexGroupWalk_skips_nonIndex found group outer hdecl] at hp
      obtain ⟨target, hmem, hgt⟩ := ih found hp
      exact ⟨target, mem_indexDeclaringGroups_cons target group outer hmem, hgt⟩

/-- The walk reports only its own two classes, never the name class. -/
theorem indexGroupWalk_error_classes :
    ∀ (found : Option IndexDeclaringGroup) (path : List IndexDeclaringGroup)
      (refusal : KernelStaticDiagnostic),
      indexGroupWalk found path = .error refusal →
        refusal = .multipleIndexFields ∨ refusal = .multipleIndexFields2 := by
  intro found path
  induction path generalizing found with
  | nil => intro refusal hp; simp [indexGroupWalk] at hp
  | cons group outer ih =>
    intro refusal hp
    by_cases hdecl : group.declaresIndex = true
    · simp only [indexGroupWalk, hdecl, Bool.not_true, Bool.false_eq_true, ite_false] at hp
      cases found with
      | some _ => exact Or.inl (by simpa [eq_comm] using hp)
      | none =>
        by_cases hcount : group.declaredNames > 1
        · exact Or.inr (by simpa [hcount, eq_comm] using hp)
        · simp only [hcount, ite_false] at hp
          exact ih (some group) refusal hp
    · simp only [Bool.not_eq_true] at hdecl
      rw [indexGroupWalk_skips_nonIndex found group outer hdecl] at hp
      exact ih found refusal hp

/-- **The name is resolved strictly after the walk.** A path the walk refuses reports the walk's
class whatever its names resolve to, so a consumer checking names during the walk reports a class the
Kernel does not. -/
theorem indexResolution_walk_precedes_name (path : List IndexDeclaringGroup)
    (refusal : KernelStaticDiagnostic) (h : indexGroupWalk none path = .error refusal) :
    indexResolution path = .error refusal := by
  simp [indexResolution, h]

/-- And the name class needs the walk to have settled on exactly one group. -/
theorem indexFieldInvalid_needs_resolved_group (path : List IndexDeclaringGroup)
    (h : indexResolution path = .error .indexFieldInvalid) :
    ∃ group, indexGroupWalk none path = .ok (some group) ∧
      group.nameResolvesToField = false := by
  unfold indexResolution at h
  cases hwalk : indexGroupWalk none path with
  | error other =>
    rcases indexGroupWalk_error_classes none path other hwalk with rfl | rfl <;>
      rw [hwalk] at h <;> simp at h
  | ok found =>
    cases found with
    | none => rw [hwalk] at h; simp at h
    | some group =>
      rw [hwalk] at h
      cases hname : group.nameResolvesToField
      · exact ⟨group, rfl, hname⟩
      · simp [hname] at h

/-- A single index group whose name resolves is the admitted shape, and it is the only one. -/
theorem indexResolution_single_ok (group : IndexDeclaringGroup)
    (hcount : group.declaredNames = 1) (hname : group.nameResolvesToField = true) :
    indexResolution [group] = .ok (some group) := by
  have hdecl : group.declaresIndex = true := by simp [IndexDeclaringGroup.declaresIndex, hcount]
  simp [indexResolution, indexGroupWalk, hdecl, hcount, hname]

end A12Kernel
