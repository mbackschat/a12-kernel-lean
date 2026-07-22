import A12Kernel.Elaboration.StarStringValueList

/-! # Checked nested String-star literal value-list laws -/

namespace A12Kernel

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
    (scope : ValidationRelevanceScope) (read : Env → FieldId → RawCell) :
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
    (scope : ValidationRelevanceScope) (left right : Env → FieldId → RawCell)
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
    (document : Document) (outer : Env) (read : Env → FieldId → RawCell)
    (fields : ResolvedValueListSide .token)
    (resolved : checked.fields.resolvedValueSide document outer read = .ok fields) :
    checked.evaluateFull document outer read =
      .ok (checked.quantifier.eval fields checked.resolvedValuesSide) := by
  simp [CheckedStarStringValueListSource.evaluateFull, resolved]
  rfl

/-- Once topology resolution succeeds, partial evaluation delegates the classified fields side and always-relevant literal side to the sole shared quantifier dispatcher. -/
theorem checkedStarStringValueList_evaluatePartial_of_resolved
    (checked : CheckedStarStringValueListSource model)
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (read : Env → FieldId → RawCell)
    (fields : ResolvedValueListQuantifierSide .token)
    (resolved : checked.fields.resolvedPartialValueSide document outer scope read =
      .ok fields) :
    checked.evaluatePartial document outer scope read =
      .ok (checked.quantifier.evalClassified fields
        (.ofResolved checked.resolvedValuesSide)) := by
  simp [CheckedStarStringValueListSource.evaluatePartial, resolved]
  rfl

end A12Kernel
