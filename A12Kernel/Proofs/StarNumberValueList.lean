import A12Kernel.Elaboration.StarNumberValueList

/-! # Checked nested Number-star value-list laws

These laws pin the checked composition boundary. The general star topology, checked filtering, Number classification, and asymmetric quantifier laws remain with their existing owners.
-/

namespace A12Kernel

/-- Checked authoring contains no repeated direct value field. -/
theorem checkedStarNumberValueList_uniqueValueFields
    (checked : CheckedStarNumberValueListSource model) :
    FieldId.firstDuplicate?
      (checked.values.map (·.field.id)) = none :=
  checked.uniqueValueFields

/-- The checked direct values side preserves authored order and introduces neither an uninstantiated tail nor filter metadata. -/
theorem checkedStarNumberValueList_valuesSide_shape
    (checked : CheckedStarNumberValueListSource model) (raw : RawFlatContext) :
    (checked.resolvedValuesSide raw).cells =
        (checked.values.map fun value =>
          value.field.valueListCell (model.checkContext raw)) ∧
      (checked.resolvedValuesSide raw).hasUninstantiatedTail = false ∧
      (checked.resolvedValuesSide raw).hasHaving = false := by
  exact ⟨rfl, rfl, rfl⟩

/-- A plain checked fields side delegates to the established topology-derived Number side without consulting the unused filter reader. -/
theorem checkedStarNumberValueList_plainFields_delegates
    (source : CheckedStarNumberSource model) (document : Document)
    (outer : Env) (filterRead : Env → FieldId → CheckedCell)
    (read : Env → FieldId → RawCell) :
    (CheckedStarNumberValueListFields.star source).resolvedValueSide
        document outer filterRead read =
      source.resolvedValueSide document outer read := by
  rfl

/-- A filtered checked fields side delegates to the existing checked `Having` route. -/
theorem checkedStarNumberValueList_havingFields_delegates
    (source : CheckedStarNumberHavingSource model) (document : Document)
    (outer : Env) (filterRead : Env → FieldId → CheckedCell)
    (read : Env → FieldId → RawCell) :
    (CheckedStarNumberValueListFields.starHaving source).resolvedValueSide
        document outer filterRead read =
      source.resolvedValueSide document outer filterRead read := by
  rfl

/-- Partial star selection preserves canonical order and hierarchical tail state, filters before every target classification, and records whether any topology-produced cell was masked. -/
theorem checkedStarNumberValueList_partialFields_shape
    (source : CheckedStarNumberSource model) (resolved : ResolvedStarTopology)
    (scope : ValidationRelevanceScope) (read : Env → FieldId → RawCell) :
    let relevant := resolved.environments.filter fun environment =>
      source.source.cellRelevant scope environment
    (source.selectedPartialValueListSide resolved scope read).side.cells =
        relevant.map (source.valueListCell read) ∧
      (source.selectedPartialValueListSide resolved scope read).side.hasUninstantiatedTail =
        resolved.domain.hasOpenTail ∧
      (source.selectedPartialValueListSide resolved scope read).hasNonRelevant =
        (resolved.environments.any fun environment =>
          !source.source.cellRelevant scope environment) := by
  exact ⟨rfl, rfl, rfl⟩

/-- Masked topology cells are not read: two readers that classify every retained environment identically produce the same partial side. -/
theorem checkedStarNumberValueList_partialFields_agreeOnRelevant
    (source : CheckedStarNumberSource model) (resolved : ResolvedStarTopology)
    (scope : ValidationRelevanceScope) (left right : Env → FieldId → RawCell)
    (agree : ∀ environment,
      environment ∈ resolved.environments.filter (fun candidate =>
        source.source.cellRelevant scope candidate) →
      source.valueListCell left environment = source.valueListCell right environment) :
    source.selectedPartialValueListSide resolved scope left =
      source.selectedPartialValueListSide resolved scope right := by
  simp only [CheckedStarNumberSource.selectedPartialValueListSide]
  congr 1
  congr 1
  apply List.map_congr_left
  intro environment selected
  exact agree environment selected

/-- Partial direct values preserve authored order among relevant fields and record values-side masking independently of formal cell causes. -/
theorem checkedStarNumberValueList_partialValues_shape
    (checked : CheckedStarNumberValueListSource model)
    (scope : ValidationRelevanceScope) (raw : RawFlatContext) :
    let relevant := checked.values.filter fun value =>
      scope.coversCell model value.declaration.path []
    (checked.resolvedPartialValuesSide scope raw).side.cells =
        relevant.map (fun value =>
          value.field.valueListCell (model.checkContext raw)) ∧
      (checked.resolvedPartialValuesSide scope raw).hasNonRelevant =
        (checked.values.any fun value =>
          !scope.coversCell model value.declaration.path []) := by
  exact ⟨rfl, rfl⟩

/-- Once topology resolution succeeds, the checked route is exactly the existing asymmetric value-list dispatcher over the two resolved sides. -/
theorem checkedStarNumberValueList_evaluateFull_of_resolved
    (checked : CheckedStarNumberValueListSource model)
    (document : Document) (outer : Env) (raw : RawFlatContext)
    (filterRead : Env → FieldId → CheckedCell)
    (starRead : Env → FieldId → RawCell)
    (fields : ResolvedValueListSide .number)
    (resolved : checked.fields.resolvedValueSide document outer filterRead starRead =
      .ok fields) :
    checked.evaluateFull document outer raw filterRead starRead =
      .ok (checked.quantifier.eval fields (checked.resolvedValuesSide raw)) := by
  simp [CheckedStarNumberValueListSource.evaluateFull, resolved]
  rfl

/-- Once partial topology resolution succeeds, an unfiltered checked star delegates both classified sides to the sole shared quantifier dispatcher. -/
theorem checkedStarNumberValueList_evaluatePartial_of_resolved
    (checked : CheckedStarNumberValueListSource model)
    (source : CheckedStarNumberSource model)
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (raw : RawFlatContext) (starRead : Env → FieldId → RawCell)
    (fieldsOwner : checked.fields = .star source)
    (fields : ResolvedValueListQuantifierSide .number)
    (resolved : source.resolvedPartialValueListSide document outer scope starRead =
      .ok fields) :
    checked.evaluatePartial document outer scope raw starRead =
      .ok (.evaluated (checked.quantifier.evalClassified fields
        (checked.resolvedPartialValuesSide scope raw))) := by
  simp [CheckedStarNumberValueListSource.evaluatePartial, fieldsOwner, resolved]
  rfl

/-- A locally visible `Having` skips partial evaluation before topology and either reader, independently of malformed document state. -/
theorem checkedStarNumberValueList_partialHaving_skips
    (checked : CheckedStarNumberValueListSource model)
    (source : CheckedStarNumberHavingSource model)
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (raw : RawFlatContext) (starRead : Env → FieldId → RawCell)
    (fieldsOwner : checked.fields = .starHaving source) :
    checked.evaluatePartial document outer scope raw starRead =
      .ok .skippedHaving := by
  simp [CheckedStarNumberValueListSource.evaluatePartial, fieldsOwner]
  rfl

end A12Kernel
