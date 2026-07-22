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

end A12Kernel
