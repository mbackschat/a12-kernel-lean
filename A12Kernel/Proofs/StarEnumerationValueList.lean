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

/-- The direct Enumeration projection is re-admitted against the exact model before it can be paired with starred values. -/
theorem checkedEnumerationValueListStarValues_field_admitted
    (checked : CheckedEnumerationValueListStarValuesSource model) :
    model.checkedEnumerationOperand? checked.fieldCore = some checked.field :=
  checked.fieldAdmitted

/-- Once the starred values side resolves, full evaluation delegates exactly to the common token-list dispatcher. -/
theorem checkedEnumerationValueListStarValues_evaluateFull_of_resolved
    (checked : CheckedEnumerationValueListStarValuesSource model)
    (document : Document) (outer : Env) (context : FlatContext)
    (filterRead : Env → FieldId → CheckedCell)
    (read : Env → FieldId → RawCell) (values : ResolvedValueListSide .token)
    (resolved : checked.values.resolvedValueSide document outer filterRead read =
      .ok values) :
    checked.evaluateFull document outer context filterRead read =
      .ok (checked.quantifier.eval (checked.resolvedFieldsSide context) values) := by
  simp [CheckedEnumerationValueListStarValuesSource.evaluateFull, resolved]
  rfl

/-- Once partial star resolution succeeds, both classified sides enter the sole asymmetric dispatcher unchanged. -/
theorem checkedEnumerationValueListStarValues_evaluatePartial_of_resolved
    (checked : CheckedEnumerationValueListStarValuesSource model)
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (context : FlatContext) (read : Env → FieldId → RawCell)
    (values : ResolvedValueListQuantifierSide .token)
    (unfiltered : checked.values.filter.isNone = true)
    (resolved : checked.values.resolvedPartialValueSide document outer scope read
      unfiltered = .ok values) :
    checked.evaluatePartial document outer scope context read =
      .ok (.evaluated (checked.quantifier.evalClassified
        (checked.resolvedPartialFieldsSide scope context) values)) := by
  simp [CheckedEnumerationValueListStarValuesSource.evaluatePartial, unfiltered,
    resolved]
  rfl

/-- A checked values-side `Having` skips partial validation before direct-field, topology, or Enumeration reads. -/
theorem checkedEnumerationValueListStarValues_partialHaving_skips
    (checked : CheckedEnumerationValueListStarValuesSource model)
    (filter : CheckedStarHaving model checked.values.source
      checked.values.declaringGroup)
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (context : FlatContext) (read : Env → FieldId → RawCell)
    (owned : checked.values.filter = some filter) :
    checked.evaluatePartial document outer scope context read = .ok .skippedHaving := by
  simp [CheckedEnumerationValueListStarValuesSource.evaluatePartial, owned]
  rfl

end A12Kernel
