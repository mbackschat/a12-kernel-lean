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

/-- No notification is reported twice, whatever the charset and declaration. -/
theorem enumerationDeclaration_notifications_nodup (charset : LegalCharset)
    (declaration : EnumerationDeclaration) :
    (declaration.notifications charset).Nodup := by
  unfold EnumerationDeclaration.notifications
  split
  · exact List.nodup_nil
  · exact eraseDups_nodup_of_length_le _ _ (Nat.le_refl _)

/-- A declaration the first-refusal validator admits, under the default charset and without supplementary scalars in its stored tokens or display texts, raises no notification. The collection therefore never rejects what the validator admitted unless the model restricts its characters or the declaration holds a supplementary-plane scalar. -/
theorem enumerationDeclaration_notifications_eq_nil_of_validate_ok
    (declaration : EnumerationDeclaration) (valid : declaration.validate = .ok ())
    (noSupplementary : declaration.containsSupplementaryScalar = false) :
    declaration.notifications .defaultBmp = [] := by
  obtain ⟨nodup, arity⟩ := declaration.validate_ok_shape valid
  have noDuplicates : declaration.duplicatedStoredTokens = [] := by
    simp only [EnumerationDeclaration.duplicatedStoredTokens, List.filter_eq_nil_iff,
      List.mem_eraseDups, decide_eq_true_eq]
    intro token member
    simp [nodup.count, member]
  have emptyBlocks : declaration.invalidCharacterNotifications .defaultBmp = [] ∧
      declaration.supplementaryNotifications = [] ∧
      declaration.shortfallNotifications = [] ∧
      declaration.surplusNotifications = [] ∧
      declaration.categoryDuplicateNotifications = [] ∧
      declaration.internalDuplicateNotifications = [] ∧
      declaration.repeatedValueNotifications = [] := by
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [EnumerationDeclaration.supplementaryNotifications, noSupplementary]
    · simp only [EnumerationDeclaration.shortfallNotifications, List.flatMap_eq_nil_iff]
      intro category member
      simp [arity category member]
    · simp only [EnumerationDeclaration.surplusNotifications, List.flatMap_eq_nil_iff]
      intro category member
      simp [arity category member]
    · simp [EnumerationDeclaration.categoryDuplicateNotifications, noDuplicates]
    · simp [EnumerationDeclaration.internalDuplicateNotifications, noDuplicates]
    · simp [EnumerationDeclaration.repeatedValueNotifications, noDuplicates]
  obtain ⟨invalid, supplementary, shortfall, surplus, categoryDuplicate, internalDuplicate,
    repeated⟩ := emptyBlocks
  unfold EnumerationDeclaration.notifications
  split
  · rfl
  · simp [invalid, supplementary, shortfall, surplus, categoryDuplicate, internalDuplicate,
      repeated]

end A12Kernel
