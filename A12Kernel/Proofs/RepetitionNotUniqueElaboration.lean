import A12Kernel.Elaboration.RepetitionNotUnique

/-! # Checked nested Number `RepetitionNotUnique` laws -/

namespace A12Kernel

@[simp]
theorem repetitionKey_numberValueList_present (value : Rat) :
    RepetitionKeyComponent.ofNumberValueListCell (.present value) =
      .present (.number value) := by
  rfl

@[simp]
theorem repetitionKey_numberValueList_empty :
    RepetitionKeyComponent.ofNumberValueListCell .empty = .empty := by
  rfl

@[simp]
theorem repetitionKey_numberValueList_unknown (cause : FormalCause) :
    RepetitionKeyComponent.ofNumberValueListCell (.unknown cause) =
      .unknown cause := by
  rfl

/-- Checked composite keys contain no repeated direct field identifier. -/
theorem checkedNumberRepetitionNotUnique_uniqueKeyFields
    (checked : CheckedNumberRepetitionNotUniqueSource model) :
    FieldId.firstDuplicate? (checked.keys.map (·.field.id)) = none :=
  checked.uniqueKeyFields

/-- Every checked key uses the same exact group path as the first key. -/
theorem checkedNumberRepetitionNotUnique_commonKeyPath
    (checked : CheckedNumberRepetitionNotUniqueSource model) :
    checked.restKeys.all (fun key =>
      key.source.declaration.groupPath ==
        checked.firstKey.source.declaration.groupPath) = true :=
  checked.commonKeyPath

/-- Every checked key uses the same topology plan as the first key. -/
theorem checkedNumberRepetitionNotUnique_commonStarPath
    (checked : CheckedNumberRepetitionNotUniqueSource model) :
    checked.restKeys.all (fun key =>
      key.source.path == checked.firstKey.source.path) = true :=
  checked.commonStarPath

/-- The first reopened level is exactly the selected default or explicit reference group. -/
theorem checkedNumberRepetitionNotUnique_referenceLevel
    (checked : CheckedNumberRepetitionNotUniqueSource model) :
    ((checked.firstKey.source.path.axes.drop
      checked.firstKey.source.path.firstStar).head?.map (·.level)) =
        some checked.referenceGroup.level :=
  checked.referenceLevelOwned

/-- Resolved checked rows preserve their complete topology environment and authored composite-key order. -/
theorem checkedNumberRepetitionNotUnique_resolvedRow_shape
    (checked : CheckedNumberRepetitionNotUniqueSource model)
    (read : Env → FieldId → RawCell) (environment : Env) :
    (checked.resolvedRow read environment).row = environment ∧
      (checked.resolvedRow read environment).key =
        checked.keys.map fun key =>
          RepetitionKeyComponent.ofNumberValueListCell
            (key.valueListCell read environment) := by
  exact ⟨rfl, rfl⟩

/-- Successful topology resolution is followed only by all-component relevance filtering and checked key classification. -/
theorem checkedNumberRepetitionNotUnique_resolvedRows_of_topology
    (checked : CheckedNumberRepetitionNotUniqueSource model)
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (read : Env → FieldId → RawCell) (topology : ResolvedStarTopology)
    (resolved : checked.firstKey.source.path.resolve document outer = .ok topology) :
    checked.resolvedRows document outer scope read =
      .ok ((topology.environments.filter (checked.rowRelevant scope)).map
        (checked.resolvedRow read)) := by
  simp [CheckedNumberRepetitionNotUniqueSource.resolvedRows, resolved]
  rfl

/-- Once checked row construction succeeds, evaluation delegates exactly to the established branch-independent RNU relation. -/
theorem checkedNumberRepetitionNotUnique_evaluate_of_rows
    (checked : CheckedNumberRepetitionNotUniqueSource model)
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (read : Env → FieldId → RawCell) (rows : List ResolvedRepetitionKeyRow)
    (resolved : checked.resolvedRows document outer scope read = .ok rows) :
    checked.evaluate document outer scope read =
      .ok (evalRepetitionNotUnique rows) := by
  simp [CheckedNumberRepetitionNotUniqueSource.evaluate, resolved]
  rfl

end A12Kernel
