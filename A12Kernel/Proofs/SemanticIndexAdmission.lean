import A12Kernel.Elaboration.SemanticIndexAdmission
import A12Kernel.Proofs.IndexGroupResolution

/-! # Laws of the semantic-index admission cascade

The cascade's content is its order and its arm split, so the laws are about both.

`semanticIndexAdmissionRefusal_source` is the workhorse: it says where each reported class can have come
from, which is what lets every later law be settled stage by stage instead of by re-walking the
whole cascade. It is also directly useful to a consumer asking *why* a site was refused.

`keyStar_outranks_valueSpecStar` and `semanticIndexAndWildcard_needs_every_earlier_gate` pin the two
wildcard classes to opposite ends: a site starred on both sides reports the key's class, and the value
spec's class is reachable only once every other gate has passed. A consumer holding one "semantic index
and wildcard" rule gets both the class and the precedence wrong.

`constantKey_never_reports_reference_classes` and `referenceKey_never_reports_constantInvalid` state
the forced axis: five classes need one arm and cannot appear from the other, so neither arm alone is a
complete fixture set for this construct.

`emptyConstant_refused_however_applicable` isolates the empty disjunct from the type test, and
`lenience_swaps_the_class` shows that a lenient parse does not simply refuse less here — the same site
reports a *different* class, so a lenient reader's vocabulary is not the strict one minus a member.

**Not claimed:** nothing here establishes that the Kernel raises these classes at all, only that this
project's chosen account orders them so. The whole family is `external evidence pending`.
-/

namespace A12Kernel

/-- The composed walk contributes exactly its own three classes and no other. -/
private theorem indexResolution_error_classes (path : List IndexDeclaringGroup)
    (refusal : KernelStaticDiagnostic) (h : indexResolution path = .error refusal) :
    refusal = .multipleIndexFields ∨ refusal = .multipleIndexFields2 ∨
      refusal = .indexFieldInvalid := by
  unfold indexResolution at h
  cases hw : indexGroupWalk none path with
  | error r =>
      rw [hw] at h
      simp only [Except.error.injEq] at h
      subst h
      rcases indexGroupWalk_error_classes none path r hw with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)
  | ok found =>
      rw [hw] at h
      cases found with
      | none => simp at h
      | some g =>
          by_cases hn : g.nameResolvesToField = true
          · simp [hn] at h
          · simp only [hn, Bool.false_eq_true, if_false, Except.error.injEq] at h
            exact Or.inr (Or.inr h.symm)

/-- The key-shape stage reports only its own two classes. -/
private theorem keyShapeRefusal_range (key : SemanticIndexAdmissionKey) (d : KernelStaticDiagnostic)
    (h : keyShapeRefusal key = some d) :
    d = .semanticIndexKeyNotField ∨ d = .semanticIndexKeyStarred := by
  cases key with
  | constant _ _ => simp [keyShapeRefusal] at h
  | reference _ => simp only [keyShapeRefusal] at h; split at h <;> simp_all

/-- The key-agreement stage reports only its two arm-specific classes. -/
private theorem keyAgreementRefusal_range (key : SemanticIndexAdmissionKey) (d : KernelStaticDiagnostic)
    (h : keyAgreementRefusal key = some d) :
    d = .indexTypeInconsistent ∨ d = .semanticIndexConstantInvalid := by
  cases key with
  | constant _ _ => simp only [keyAgreementRefusal] at h; split at h <;> simp_all
  | reference _ => simp only [keyAgreementRefusal] at h; split at h <;> simp_all

/-- The key-usage stage reports only its two classes. -/
private theorem keyUsageRefusal_range (lenient : Bool) (key : SemanticIndexAdmissionKey)
    (d : KernelStaticDiagnostic) (h : keyUsageRefusal lenient key = some d) :
    d = .rawTypeOperandInvalid ∨ d = .semanticIndexKeyWithCategory := by
  cases key with
  | constant _ _ => simp [keyUsageRefusal] at h
  | reference _ =>
      simp only [keyUsageRefusal] at h
      split at h
      · simp_all
      · split at h <;> simp_all

/-- **Where a reported class came from.** Eight positions, each either a stage's own verdict or one of
the four classes the cascade raises directly. Every other law here is a corollary. -/
theorem semanticIndexAdmissionRefusal_source (site : SemanticIndexAdmissionSite) (key : SemanticIndexAdmissionKey)
    (d : KernelStaticDiagnostic) (h : semanticIndexAdmissionRefusal site key = some d) :
    keyShapeRefusal key = some d ∨ d = .semanticIndexOnSemanticIndex ∨
      indexResolution site.indexPath = .error d ∨ d = .noIndexField ∨
      keyAgreementRefusal key = some d ∨ d = .semanticIndexContainedInIndex ∨
      keyUsageRefusal site.lenient key = some d ∨ d = .semanticIndexAndWildcard := by
  unfold semanticIndexAdmissionRefusal at h
  split at h
  · rename_i refusal heq
    simp only [Option.some.injEq] at h
    exact Or.inl (by rw [heq, h])
  · split at h
    · simp only [Option.some.injEq] at h
      exact Or.inr (Or.inl h.symm)
    · split at h
      · rename_i refusal heq
        simp only [Option.some.injEq] at h
        exact Or.inr (Or.inr (Or.inl (by rw [heq, h])))
      · simp only [Option.some.injEq] at h
        exact Or.inr (Or.inr (Or.inr (Or.inl h.symm)))
      · split at h
        · rename_i refusal heq
          simp only [Option.some.injEq] at h
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [heq, h])))))
        · split at h
          · simp only [Option.some.injEq] at h
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h.symm)))))
          · split at h
            · rename_i refusal heq
              simp only [Option.some.injEq] at h
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                (Or.inl (by rw [heq, h])))))))
            · split at h
              · simp only [Option.some.injEq] at h
                exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                  (Or.inr h.symm))))))
              · simp at h

/-- **A star on the key outranks a star on the value spec.** The two are different classes, and the
site carrying both reports the earlier one. -/
theorem keyStar_outranks_valueSpecStar (site : SemanticIndexAdmissionSite)
    (r : SemanticIndexAdmissionKeyRef) (hstar : r.starred = true) (hfield : r.resolvesToField = true) :
    semanticIndexAdmissionRefusal { site with starredAtIndexLevel := true } (.reference r) =
      some .semanticIndexKeyStarred := by
  simp [semanticIndexAdmissionRefusal, keyShapeRefusal, hstar, hfield]

/-- **The value spec's star is the last gate**, so its class carries the information that every other
gate passed — which is why it is the one refusal a repair tool can act on without re-checking the
rest. -/
theorem semanticIndexAndWildcard_needs_every_earlier_gate (site : SemanticIndexAdmissionSite)
    (key : SemanticIndexAdmissionKey)
    (h : semanticIndexAdmissionRefusal site key = some .semanticIndexAndWildcard) :
    keyShapeRefusal key = none ∧ site.valueSpecIsSemanticIndex = false ∧
      keyAgreementRefusal key = none ∧ keyContainedInIndexGroup key = false ∧
      keyUsageRefusal site.lenient key = none ∧ site.starredAtIndexLevel = true := by
  unfold semanticIndexAdmissionRefusal at h
  split at h
  · rename_i refusal heq
    simp only [Option.some.injEq] at h
    rcases keyShapeRefusal_range _ refusal heq with h1 | h1 <;> subst h1 <;> simp at h
  · rename_i hshape
    split at h
    · simp at h
    · rename_i hsem
      split at h
      · rename_i refusal heq
        simp only [Option.some.injEq] at h
        rcases indexResolution_error_classes site.indexPath refusal heq with h1 | h1 | h1 <;>
          subst h1 <;> simp at h
      · simp at h
      · split at h
        · rename_i refusal heq
          simp only [Option.some.injEq] at h
          rcases keyAgreementRefusal_range _ refusal heq with h1 | h1 <;> subst h1 <;> simp at h
        · rename_i hagree
          split at h
          · simp at h
          · rename_i hcontained
            split at h
            · rename_i refusal heq
              simp only [Option.some.injEq] at h
              rcases keyUsageRefusal_range _ _ refusal heq with h1 | h1 <;> subst h1 <;> simp at h
            · rename_i husage
              split at h
              · exact ⟨hshape, by simpa using hsem, hagree, by simpa using hcontained, husage,
                  by assumption⟩
              · simp at h

/-- **Four classes need a reference key.** A grid built only from constant keys cannot reach any of
them, so it is not a complete fixture set for this construct. -/
theorem constantKey_never_reports_reference_classes (site : SemanticIndexAdmissionSite)
    (text : String) (applicable : Bool) (d : KernelStaticDiagnostic)
    (h : semanticIndexAdmissionRefusal site (.constant text applicable) = some d) :
    d ≠ .semanticIndexKeyNotField ∧ d ≠ .semanticIndexKeyStarred ∧
      d ≠ .semanticIndexKeyWithCategory ∧ d ≠ .rawTypeOperandInvalid ∧
      d ≠ .indexTypeInconsistent := by
  rcases semanticIndexAdmissionRefusal_source site _ d h with
    hs | hs | hs | hs | hs | hs | hs | hs
  · simp [keyShapeRefusal] at hs
  · subst hs; simp
  · rcases indexResolution_error_classes site.indexPath d hs with h1 | h1 | h1 <;> subst h1 <;> simp
  · subst hs; simp
  · simp only [keyAgreementRefusal] at hs
    split at hs
    · simp only [Option.some.injEq] at hs; subst hs; simp
    · simp at hs
  · subst hs; simp
  · simp [keyUsageRefusal] at hs
  · subst hs; simp

/-- Its other side: the constant arm's class is unreachable from a reference key. -/
theorem referenceKey_never_reports_constantInvalid (site : SemanticIndexAdmissionSite)
    (r : SemanticIndexAdmissionKeyRef) :
    semanticIndexAdmissionRefusal site (.reference r) ≠ some .semanticIndexConstantInvalid := by
  intro h
  rcases semanticIndexAdmissionRefusal_source site _ _ h with hs | hs | hs | hs | hs | hs | hs | hs
  · rcases keyShapeRefusal_range _ _ hs with h1 | h1 <;> simp at h1
  · simp at hs
  · rcases indexResolution_error_classes site.indexPath _ hs with h1 | h1 | h1 <;> simp at h1
  · simp at hs
  · simp only [keyAgreementRefusal] at hs
    split at hs <;> simp at hs
  · simp at hs
  · rcases keyUsageRefusal_range _ _ _ hs with h1 | h1 <;> simp at h1
  · simp at hs

/-- **The empty constant is refused by its own disjunct**, so a type that accepts it does not rescue
it. -/
theorem emptyConstant_refused_however_applicable (applicable : Bool) :
    keyAgreementRefusal (.constant "" applicable) = some .semanticIndexConstantInvalid := by
  cases applicable <;> rfl

/-- **Lenience swaps the class rather than admitting the site.** The same reference offending both the
value-validation gate and the category gate reports the first under a strict parse and the second under
a lenient one, so a lenient vocabulary is not the strict one with a member removed. -/
theorem lenience_swaps_the_class (r : SemanticIndexAdmissionKeyRef)
    (hraw : r.expandsToNoValueValidation = true) (hcat : r.carriesCategory = true) :
    keyUsageRefusal false (.reference r) = some .rawTypeOperandInvalid ∧
      keyUsageRefusal true (.reference r) = some .semanticIndexKeyWithCategory := by
  simp [keyUsageRefusal, hraw, hcat]

/-- And the value-validation class is strict-only across the **whole** cascade, not just at that
witness. -/
theorem rawTypeOperandInvalid_needs_strict (site : SemanticIndexAdmissionSite) (key : SemanticIndexAdmissionKey)
    (hlen : site.lenient = true) :
    semanticIndexAdmissionRefusal site key ≠ some .rawTypeOperandInvalid := by
  intro h
  rcases semanticIndexAdmissionRefusal_source site key _ h with hs | hs | hs | hs | hs | hs | hs | hs
  · rcases keyShapeRefusal_range _ _ hs with h1 | h1 <;> simp at h1
  · simp at hs
  · rcases indexResolution_error_classes site.indexPath _ hs with h1 | h1 | h1 <;> simp at h1
  · simp at hs
  · rcases keyAgreementRefusal_range _ _ hs with h1 | h1 <;> simp at h1
  · simp at hs
  · cases key with
    | constant _ _ => simp [keyUsageRefusal] at hs
    | reference _ =>
        simp only [keyUsageRefusal, hlen, Bool.not_true, Bool.false_and,
          Bool.false_eq_true, if_false] at hs
        split at hs <;> simp at hs
  · simp at hs

end A12Kernel
