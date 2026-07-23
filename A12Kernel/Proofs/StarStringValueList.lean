import A12Kernel.Elaboration.StarStringValueList
import A12Kernel.Proofs.Correlation

/-! # Checked nested String-star literal value-list laws -/

namespace A12Kernel

/-- The checked star-specific String field is the terminal declaration's exact identifier, not a caller-selected lookalike. -/
theorem checkedStarStringSource_fieldId_exact
    (checked : CheckedStarStringSource model) :
    checked.field.id = checked.source.declaration.id := by
  have fieldOwned := checked.fieldOwned
  cases kindEq : checked.source.declaration.policy.kind <;>
    cases modeEq : checked.source.declaration.stringValueMode
  all_goals try simp_all [FlatFieldDecl.toStringValueField?]
  exact (congrArg FlatStringField.id fieldOwned.2).symm

/-- Any retained String-star filter is checked against the exact candidate and captured repetition environments of its typed source. -/
theorem checkedStarStringSource_filter_wellFormed
    (checked : CheckedStarStringSource model)
    (filter : CheckedStarHaving model checked.source checked.declaringGroup) :
    filter.condition.wellFormedForEnvironments model
      (checked.source.path.axes.map (·.level))
      (model.repeatableScopeForGroupPath checked.declaringGroup) = true :=
  filter.wellFormed

/-- A filtered String star delegates selection and classification to the shared kind-neutral checked-star route. -/
theorem checkedStarStringSource_filtered_delegates
    (checked : CheckedStarStringSource model)
    (filter : CheckedStarHaving model checked.source checked.declaringGroup)
    (document : Document) (outer : Env)
    (filterRead : Env → FieldId → CheckedCell)
    (read : Env → FieldId → CheckedCell) (owned : checked.filter = some filter) :
    checked.resolvedValueSide document outer filterRead read =
      checked.source.resolvedValidationHavingValueListSide document outer
        filter.condition filterRead (checked.valueListCell read) := by
  simp [CheckedStarStringSource.resolvedValueSide,
    CheckedStarFieldPath.resolvedOptionalValidationHavingValueListSide, owned]

/-- Checked authoring always retains a nonempty literal token side. -/
theorem checkedStarStringValueList_values_nonempty
    (checked : CheckedStarStringValueListSource model) :
    checked.values ≠ [] := by
  simp [CheckedStarStringValueListSource.values]

/-- The literal side preserves authored order and introduces neither an omitted tail nor filter metadata. -/
theorem checkedStarStringValueList_valuesSide_shape
    (checked : CheckedStarStringValueListSource model) :
    checked.resolvedValuesSide.cells = checked.values.map
        (fun value => (ValueListCell.present value : ValueListCell .token)) ∧
      checked.resolvedValuesSide.hasUninstantiatedTail = false ∧
      checked.resolvedValuesSide.hasHaving = false := by
  exact ⟨rfl, rfl, rfl⟩

/-- Partial star selection preserves canonical order and hierarchical tail state, invokes String classification only for relevant leaves, and separately records whether wildcard/ancestor coverage establishes the star's complete extent. -/
theorem checkedStarStringValueList_partialFields_shape
    (source : CheckedStarStringSource model) (resolved : ResolvedStarTopology)
    (scope : ValidationRelevanceScope) (read : Env → FieldId → CheckedCell) :
    let relevant := resolved.environments.filter fun environment =>
      source.source.cellRelevant scope environment
    (source.source.selectedPartialValueListSide resolved scope
        (source.valueListCell read)).side.cells =
        relevant.map (source.valueListCell read) ∧
      (source.source.selectedPartialValueListSide resolved scope
        (source.valueListCell read)).side.hasUninstantiatedTail =
          resolved.domain.hasOpenTail ∧
      (source.source.selectedPartialValueListSide resolved scope
        (source.valueListCell read)).hasNonRelevant =
          !source.source.allRowsRelevant scope := by
  exact ⟨rfl, rfl, rfl⟩

/-- Masked topology cells are never String-checked: agreement on retained environments is sufficient for equal partial sides. -/
theorem checkedStarStringValueList_partialFields_agreeOnRelevant
    (source : CheckedStarStringSource model) (resolved : ResolvedStarTopology)
    (scope : ValidationRelevanceScope) (left right : Env → FieldId → CheckedCell)
    (agree : ∀ environment,
      environment ∈ resolved.environments.filter (fun candidate =>
        source.source.cellRelevant scope candidate) →
      source.valueListCell left environment = source.valueListCell right environment) :
    source.source.selectedPartialValueListSide resolved scope
        (source.valueListCell left) =
      source.source.selectedPartialValueListSide resolved scope
        (source.valueListCell right) := by
  have cellsEqual :
      (resolved.environments.filter fun candidate =>
          source.source.cellRelevant scope candidate).map
          (source.valueListCell left) =
        (resolved.environments.filter fun candidate =>
          source.source.cellRelevant scope candidate).map
          (source.valueListCell right) := by
    apply List.map_congr_left
    intro environment selected
    exact agree environment selected
  simp only [CheckedStarFieldPath.selectedPartialValueListSide]
  rw [cellsEqual]

/-- Once topology resolution succeeds, full evaluation is exactly the common token-list dispatcher over the checked String side and literal side. -/
theorem checkedStarStringValueList_evaluateFull_of_resolved
    (checked : CheckedStarStringValueListSource model)
    (document : Document) (outer : Env)
    (filterRead : Env → FieldId → CheckedCell)
    (read : Env → FieldId → CheckedCell)
    (fields : ResolvedValueListSide .token)
    (resolved : checked.fields.resolvedValueSide document outer filterRead read = .ok fields) :
    checked.evaluateFull document outer filterRead read =
      .ok (checked.quantifier.eval fields checked.resolvedValuesSide) := by
  simp [CheckedStarStringValueListSource.evaluateFull, resolved]
  rfl

/-- Once topology resolution succeeds, partial evaluation delegates the classified fields side and always-relevant literal side to the sole shared quantifier dispatcher. -/
theorem checkedStarStringValueList_evaluatePartial_of_resolved
    (checked : CheckedStarStringValueListSource model)
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (read : Env → FieldId → CheckedCell)
    (fields : ResolvedValueListQuantifierSide .token)
    (unfiltered : checked.fields.filter.isNone = true)
    (resolved : checked.fields.resolvedPartialValueSide document outer scope read
      unfiltered = .ok fields) :
    checked.evaluatePartial document outer scope read =
      .ok (.evaluated (checked.quantifier.evalClassified fields
        (.ofResolved checked.resolvedValuesSide))) := by
  simp [CheckedStarStringValueListSource.evaluatePartial, unfiltered, resolved]
  rfl

/-- A checked fields-side `Having` skips partial validation before topology or String reads. -/
theorem checkedStarStringValueList_partialHaving_skips
    (checked : CheckedStarStringValueListSource model)
    (filter : CheckedStarHaving model checked.fields.source checked.fields.declaringGroup)
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (read : Env → FieldId → CheckedCell)
    (owned : checked.fields.filter = some filter) :
    checked.evaluatePartial document outer scope read = .ok .skippedHaving := by
  simp [CheckedStarStringValueListSource.evaluatePartial, owned]
  rfl

/-- The direct fields-side operand is re-admitted against the exact model before it can be paired with a starred values side. -/
theorem checkedStringValueListStarValues_field_admitted
    (checked : CheckedStringValueListStarValuesSource model) :
    model.admitsField (.string checked.field) = true :=
  checked.admitted

/-- The direct fields side contains exactly one model-checked String cell and no star metadata. -/
theorem checkedStringValueListStarValues_fieldsSide_shape
    (checked : CheckedStringValueListStarValuesSource model)
    (context : FlatContext) :
    checked.resolvedFieldsSide context = {
      cells := [
        (FlatTextFieldOperand.string checked.field).valueListCell
          context]
      hasUninstantiatedTail := false
      hasHaving := false } := by
  rfl

/-- Once the starred values side resolves, full evaluation delegates exactly to the common token-list dispatcher. -/
theorem checkedStringValueListStarValues_evaluateFull_of_resolved
    (checked : CheckedStringValueListStarValuesSource model)
    (document : Document) (outer : Env) (context : FlatContext)
    (filterRead : Env → FieldId → CheckedCell)
    (read : Env → FieldId → CheckedCell)
    (values : ResolvedValueListSide .token)
    (resolved : checked.values.resolvedValueSide document outer filterRead read =
      .ok values) :
    checked.evaluateFull document outer context filterRead read =
      .ok (checked.quantifier.eval (checked.resolvedFieldsSide context) values) := by
  simp [CheckedStringValueListStarValuesSource.evaluateFull, resolved]
  rfl

/-- Once partial star resolution succeeds, both classified sides enter the sole asymmetric dispatcher unchanged. -/
theorem checkedStringValueListStarValues_evaluatePartial_of_resolved
    (checked : CheckedStringValueListStarValuesSource model)
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (context : FlatContext) (read : Env → FieldId → CheckedCell)
    (values : ResolvedValueListQuantifierSide .token)
    (unfiltered : checked.values.filter.isNone = true)
    (resolved : checked.values.resolvedPartialValueSide document outer scope read
      unfiltered = .ok values) :
    checked.evaluatePartial document outer scope context read =
      .ok (.evaluated (checked.quantifier.evalClassified
        (checked.resolvedPartialFieldsSide scope context) values)) := by
  simp [CheckedStringValueListStarValuesSource.evaluatePartial, unfiltered, resolved]
  rfl

/-- A checked values-side `Having` skips partial validation before direct-field, topology, or String reads. -/
theorem checkedStringValueListStarValues_partialHaving_skips
    (checked : CheckedStringValueListStarValuesSource model)
    (filter : CheckedStarHaving model checked.values.source checked.values.declaringGroup)
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (context : FlatContext) (read : Env → FieldId → CheckedCell)
    (owned : checked.values.filter = some filter) :
    checked.evaluatePartial document outer scope context read = .ok .skippedHaving := by
  simp [CheckedStringValueListStarValuesSource.evaluatePartial, owned]
  rfl

end A12Kernel
