import A12Kernel.Elaboration.Enumeration

/-! # A12Kernel.Proofs.EnumerationElaboration — ordinary declaration laws -/

namespace A12Kernel

@[simp]
theorem checkedEnumeration_wellFormed
    (checked : CheckedEnumerationDeclaration) :
    checked.declaration.validate = .ok () :=
  checked.wellFormed

@[simp]
theorem checkedEnumeration_displayFacts_exact
    (checked : CheckedEnumerationDeclaration) :
    checked.displayProfile.facts = checked.declaration.displayFacts := by
  rfl

@[simp]
theorem checkedEnumeration_directComparableField_exact
    (checked : CheckedEnumerationDeclaration) :
    checked.directComparableField = .enumeration checked.displayProfile := by
  rfl

@[simp]
theorem checkedEnumeration_storedProjection_exact
    (checked : CheckedEnumerationDeclaration) :
    checked.storedProjection = .stored := by
  rfl

/-- Exact category-name lookup reuses the declaration's checked stored-token order rather than constructing a second domain. -/
theorem checkedEnumeration_categoryProjection_exact
    (checked : CheckedEnumerationDeclaration) (name : String)
    (category : EnumerationCategoryDeclaration)
    (found : checked.declaration.categories.find?
      (fun candidate => candidate.name == name) = some category) :
    checked.categoryProjection? name =
      some (.category {
        storedTokens := checked.declaration.storedTokens
        categoryTokens := category.tokens }) := by
  simp [CheckedEnumerationDeclaration.categoryProjection?, found]

end A12Kernel
