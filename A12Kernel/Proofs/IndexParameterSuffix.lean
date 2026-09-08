import A12Kernel.Elaboration.IndexParameterSuffix

/-! # Laws of the `index(...)` parameter's two suffix readings

The stage's consumer-facing content is that the two suffixes are **not** two spellings of one check.

`valueSuffix_admits_uniform_non_enumeration` and `categorySuffix_refuses_non_enumeration` are the pair a
Translate or Explain consumer needs: the same referenced set is legal under one suffix and refused under
the other, so a suffix cannot be rewritten to its sibling while preserving legality.

That each suffix ignores the part the other reads is locked by **separators** rather than proved in
general: one pair of declarations differing solely in their category mapping, one differing solely in
their display mapping, each refused under one suffix and admitted under the other
([`Conformance/IndexParameterSuffix.lean`](../Conformance/IndexParameterSuffix.lean)). A general
quantified form would say more, and is not claimed here.
-/

namespace A12Kernel

/-- The value suffix never raises the Enumeration class, because it tests agreement rather than kind. -/
theorem valueSuffix_admits_uniform_non_enumeration :
    ∀ referenced : List ReferencedDeclaration,
      (∀ declaration ∈ referenced, declaration.isEnumeration = false) →
        ∀ first : ReferencedDeclaration, first.isEnumeration = false →
          valueSuffixScan first referenced = none
  | [], _, _, _ => rfl
  | declaration :: rest, hAll, first, hFirst => by
      have hDecl : declaration.isEnumeration = false := hAll declaration (List.mem_cons_self ..)
      have hRest : ∀ d ∈ rest, d.isEnumeration = false :=
        fun d hd => hAll d (List.mem_cons_of_mem _ hd)
      rw [valueSuffixScan, hDecl, hFirst]
      simpa using valueSuffix_admits_uniform_non_enumeration rest hRest first hFirst

/-- The category suffix refuses the very same set at its first member. -/
theorem categorySuffix_refuses_non_enumeration (previous : Option ReferencedDeclaration)
    (declaration : ReferencedDeclaration) (rest : List ReferencedDeclaration)
    (h : declaration.isEnumeration = false) :
    categorySuffixScan previous (declaration :: rest) = some .indexFieldNoEnumeration := by
  simp [categorySuffixScan, h]

/-- **The separator, as one statement.** A nonempty referenced set whose declarations are uniformly
non-Enumeration is admitted under `.value` and refused under `->Category`, so the two suffixes are not
interchangeable and a rewrite between them does not preserve legality. -/
theorem suffixes_disagree_on_non_enumeration (declaration : ReferencedDeclaration)
    (rest : List ReferencedDeclaration) (h : declaration.isEnumeration = false)
    (hRest : ∀ d ∈ rest, d.isEnumeration = false) :
    suffixRefusal .value (declaration :: rest) = none ∧
      suffixRefusal .category (declaration :: rest) = some .indexFieldNoEnumeration := by
  refine ⟨?_, categorySuffix_refuses_non_enumeration none declaration rest h⟩
  show valueSuffixScan declaration (declaration :: rest) = none
  refine valueSuffix_admits_uniform_non_enumeration (declaration :: rest) ?_ declaration h
  intro d hd
  rcases List.mem_cons.mp hd with rfl | hd
  · exact h
  · exact hRest d hd

/-- An absent suffix refuses whatever the condition referenced, so the class carries no information
about the referenced set. -/
theorem suffixRefusal_absent (referenced : List ReferencedDeclaration) :
    suffixRefusal .absent referenced = some .indexFieldSuffixMissing := rfl

/-- An empty referenced set is admitted under both suffixes. -/
theorem suffixRefusal_empty_admits :
    suffixRefusal .category [] = none ∧ suffixRefusal .value [] = none := ⟨rfl, rfl⟩

end A12Kernel
