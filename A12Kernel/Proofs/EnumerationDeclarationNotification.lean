import A12Kernel.Elaboration.EnumerationDeclarationNotification

/-! # A12Kernel.Proofs.EnumerationDeclarationNotification — declaration notification laws

The collection is a duplicate-free list, and it extends rather than contradicts the first-refusal validator: a validated default-charset declaration without supplementary scalars raises nothing.
-/

namespace A12Kernel

/-- Collapsing identical entries leaves a duplicate-free list, proved by induction on length because each step filters the remainder. -/
theorem eraseDups_nodup_of_length_le {α : Type} [BEq α] [LawfulBEq α] :
    ∀ (bound : Nat) (entries : List α), entries.length ≤ bound → entries.eraseDups.Nodup
  | 0, entries, small => by
      have empty : entries = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst empty
      simp
  | _ + 1, [], _ => by simp
  | bound + 1, first :: rest, small => by
      rw [List.eraseDups_cons]
      refine List.nodup_cons.mpr ⟨?_, ?_⟩
      · intro member
        rw [List.mem_eraseDups] at member
        simp at member
      · exact eraseDups_nodup_of_length_le bound _
          (Nat.le_trans (List.length_filter_le _ _) (by simp at small; omega))

/-- Without a token-less entry the value entries are the stored tokens, one `some` each. -/
theorem EnumerationDeclaration.valueEntries_eq_map_some (declaration : EnumerationDeclaration)
    (holeless : declaration.tokenlessPositions = []) :
    declaration.valueEntries = declaration.storedTokens.map some := by
  unfold EnumerationDeclaration.valueEntries
  rw [holeless]
  apply List.ext_getElem
  · simp
  · intro index bound _
    simp only [List.length_map, List.length_range, List.length_nil, Nat.add_zero] at bound
    simp [List.getElem_map, List.getElem_range, List.getElem?_eq_getElem bound]

/-- No notification is reported twice, whatever the charset and declaration. -/
theorem enumerationDeclaration_notifications_nodup (charset : LegalCharset)
    (declaration : EnumerationDeclaration) :
    (declaration.notifications charset).Nodup := by
  unfold EnumerationDeclaration.notifications
  split
  · exact List.nodup_nil
  · exact eraseDups_nodup_of_length_le _ _ (Nat.le_refl _)

/-- A declaration the first-refusal validator admits, under the default charset and without supplementary scalars in its stored tokens, display texts, category tokens or default, and whose category names and tokens are none of them blank, raises no notification. The validator refuses an empty category name or token but admits a blank one, which kernel 31.1.1 states as a class of its own (`MVK_NAME_MISSING`, `MVK_MISSING_CATEGORY_VALUE`), so the filled hypothesis is what keeps the collection from rejecting what the validator admitted. It still never does so unless the model restricts its characters, the declaration holds a supplementary-plane scalar, or a name or token is blank. -/
theorem enumerationDeclaration_notifications_eq_nil_of_validate_ok
    (declaration : EnumerationDeclaration) (valid : declaration.validate = .ok ())
    (noSupplementary : declaration.containsSupplementaryScalar = false)
    (filled : ∀ category ∈ declaration.categories,
      ExecutableDeclaration.blank category.name = false ∧
        ∀ token ∈ category.tokens, ExecutableDeclaration.blank token = false) :
    declaration.notifications .defaultBmp = [] := by
  obtain ⟨holeless, trimmedNodup, arity⟩ := declaration.validate_ok_shape valid
  have entries := declaration.valueEntries_eq_map_some holeless
  have unrepeated : ∀ tokens : List String, tokens.Nodup → EnumerationDeclaration.duplicated tokens = [] := by
    intro tokens nodup
    simp only [EnumerationDeclaration.duplicated, List.filter_eq_nil_iff, decide_eq_true_eq]
    intro token member
    simp [nodup.count, List.mem_eraseDups.mp member]
  have noDuplicates : declaration.duplicatedStoredTokens = [] :=
    unrepeated _ (List.Pairwise.of_map javaTrim (fun _ _ trimmed same => trimmed (same ▸ rfl)) trimmedNodup)
  have noTrimmedDuplicates : declaration.duplicatedTrimmedTokens = [] := unrepeated _ trimmedNodup
  have emptyBlocks : declaration.invalidCharacterNotifications .defaultBmp = [] ∧
      declaration.supplementaryNotifications = [] ∧
      declaration.categoryNameNotifications = [] ∧
      declaration.shortfallNotifications = [] ∧
      declaration.surplusNotifications = [] ∧
      declaration.categoryDuplicateNotifications = [] ∧
      declaration.internalDuplicateNotifications = [] ∧
      declaration.repeatedValueNotifications = [] ∧
      declaration.valuesMissingNotifications = [] := by
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [EnumerationDeclaration.supplementaryNotifications, noSupplementary]
    · have unblank : ¬ (declaration.categories.any fun category =>
          ExecutableDeclaration.blank category.name) = true := by
        simp only [List.any_eq_true, not_exists, not_and, Bool.not_eq_true]
        intro category member
        exact (filled category member).1
      simp [EnumerationDeclaration.categoryNameNotifications, unblank]
    · simp only [EnumerationDeclaration.shortfallNotifications, List.flatMap_eq_nil_iff]
      intro category member
      have declared := (List.mem_filter.mp member).1
      simp only [List.filterMap_eq_nil_iff, List.mem_mapIdx, entries]
      rintro ⟨entry, token⟩ ⟨index, bound, same⟩
      simp only [Prod.mk.injEq] at same
      obtain ⟨rfl, rfl⟩ := same
      have inside : index < category.tokens.length := by
        rw [arity category declared]; simpa using bound
      rw [List.getElem?_eq_getElem inside]
      simp [(filled category declared).2 _ (List.getElem_mem inside)]
    · simp only [EnumerationDeclaration.surplusNotifications, List.flatMap_eq_nil_iff]
      intro category member
      have declared := (List.mem_filter.mp member).1
      simp only [List.filterMap_eq_nil_iff, List.mem_mapIdx, entries]
      rintro ⟨entry, token⟩ ⟨index, bound, same⟩
      simp only [Prod.mk.injEq] at same
      obtain ⟨rfl, rfl⟩ := same
      have inside : index < declaration.storedTokens.length := by
        rw [← arity category declared]; exact bound
      simp [List.getElem?_eq_getElem inside]
    · simp [EnumerationDeclaration.categoryDuplicateNotifications, noTrimmedDuplicates]
    · simp [EnumerationDeclaration.internalDuplicateNotifications, noTrimmedDuplicates]
    · simp [EnumerationDeclaration.repeatedValueNotifications, noDuplicates, holeless]
    · simp [EnumerationDeclaration.valuesMissingNotifications, holeless]
  obtain ⟨invalid, supplementary, categoryName, shortfall, surplus, categoryDuplicate, internalDuplicate,
    repeated, valuesMissing⟩ := emptyBlocks
  unfold EnumerationDeclaration.notifications
  split
  · rfl
  · simp [invalid, supplementary, categoryName, shortfall, surplus, categoryDuplicate, internalDuplicate,
      repeated, valuesMissing]

end A12Kernel
