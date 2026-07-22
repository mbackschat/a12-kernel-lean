import A12Kernel.Elaboration.StarEnumerationValueList
import A12Kernel.Proofs.Correlation

/-! # Checked nested Enumeration-star literal value-list laws -/

namespace A12Kernel

/-- The projected operand is certified against the exact Enumeration metadata retained by the starred field declaration. -/
theorem checkedStarEnumerationSource_declaration_exact
    (checked : CheckedStarEnumerationSource model) :
    checked.source.declaration.enumeration =
      some checked.operand.declaration.declaration :=
  checked.enumerationOwned

/-- The checked literal side is nonempty and every member belongs to the selected stored/category domain. -/
theorem checkedStarEnumerationValueList_literals_admitted
    (checked : CheckedStarEnumerationValueListSource model) :
    checked.values ≠ [] ∧
      checked.values.all
        (checked.fields.operand.declaration.literalAllowed
          checked.fields.operand.projection) = true := by
  exact ⟨by simp [CheckedStarEnumerationValueListSource.values], checked.literalsAllowed⟩

/-- A filtered Enumeration star delegates selection and classification to the shared kind-neutral checked-star route. -/
theorem checkedStarEnumerationSource_filtered_delegates
    (checked : CheckedStarEnumerationSource model)
    (filter : CheckedStarHaving model checked.source checked.declaringGroup)
    (document : Document) (outer : Env)
    (filterRead : Env → FieldId → CheckedCell)
    (read : Env → FieldId → RawCell) (owned : checked.filter = some filter) :
    checked.resolvedValueSide document outer filterRead read =
      checked.source.resolvedValidationHavingValueListSide document outer
        filter.condition filterRead (checked.valueListCell read) := by
  simp [CheckedStarEnumerationSource.resolvedValueSide,
    CheckedStarFieldPath.resolvedOptionalValidationHavingValueListSide, owned]

/-- Once topology resolution succeeds, full evaluation is exactly the shared token-list dispatcher. -/
theorem checkedStarEnumerationValueList_evaluateFull_of_resolved
    (checked : CheckedStarEnumerationValueListSource model)
    (document : Document) (outer : Env)
    (filterRead : Env → FieldId → CheckedCell)
    (read : Env → FieldId → RawCell)
    (fields : ResolvedValueListSide .token)
    (resolved : checked.fields.resolvedValueSide document outer filterRead read = .ok fields) :
    checked.evaluateFull document outer filterRead read =
      .ok (checked.quantifier.eval fields checked.resolvedValuesSide) := by
  simp [CheckedStarEnumerationValueListSource.evaluateFull, resolved]
  rfl

/-- Once partial topology resolution succeeds, the classified fields and always-relevant literal side enter the shared dispatcher unchanged. -/
theorem checkedStarEnumerationValueList_evaluatePartial_of_resolved
    (checked : CheckedStarEnumerationValueListSource model)
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (read : Env → FieldId → RawCell)
    (fields : ResolvedValueListQuantifierSide .token)
    (unfiltered : checked.fields.filter.isNone = true)
    (resolved : checked.fields.resolvedPartialValueSide document outer scope read
      unfiltered = .ok fields) :
    checked.evaluatePartial document outer scope read =
      .ok (.evaluated (checked.quantifier.evalClassified fields
        (.ofResolved checked.resolvedValuesSide))) := by
  simp [CheckedStarEnumerationValueListSource.evaluatePartial, unfiltered, resolved]
  rfl

/-- A checked fields-side `Having` skips partial validation before topology or Enumeration reads. -/
theorem checkedStarEnumerationValueList_partialHaving_skips
    (checked : CheckedStarEnumerationValueListSource model)
    (filter : CheckedStarHaving model checked.fields.source
      checked.fields.declaringGroup)
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (read : Env → FieldId → RawCell)
    (owned : checked.fields.filter = some filter) :
    checked.evaluatePartial document outer scope read = .ok .skippedHaving := by
  simp [CheckedStarEnumerationValueListSource.evaluatePartial, owned]
  rfl

end A12Kernel
