import A12Kernel.Elaboration.RepetitionNotUnique

/-! # Checked nested heterogeneous `RepetitionNotUnique` laws -/

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

@[simp]
theorem repetitionKey_tokenValueList_present (value : String) :
    RepetitionKeyComponent.ofTokenValueListCell (.present value) =
      .present (.token value) := by
  rfl

@[simp]
theorem repetitionKey_tokenValueList_empty :
    RepetitionKeyComponent.ofTokenValueListCell .empty = .empty := by
  rfl

@[simp]
theorem repetitionKey_tokenValueList_unknown (cause : FormalCause) :
    RepetitionKeyComponent.ofTokenValueListCell (.unknown cause) =
      .unknown cause := by
  rfl

/-- Checked composite keys contain no repeated direct field identifier. -/
theorem checkedRepetitionNotUnique_uniqueKeyFields
    (checked : CheckedRepetitionNotUniqueSource model) :
    FieldId.firstDuplicate? (checked.keys.map (·.fieldId)) = none :=
  checked.uniqueKeyFields

/-- Every checked key uses the same exact group path as the first key. -/
theorem checkedRepetitionNotUnique_commonKeyPath
    (checked : CheckedRepetitionNotUniqueSource model) :
    checked.restKeys.all (fun key =>
      key.source.declaration.groupPath ==
        checked.firstKey.source.declaration.groupPath) = true :=
  checked.commonKeyPath

/-- Every checked key uses the same topology plan as the first key. -/
theorem checkedRepetitionNotUnique_commonStarPath
    (checked : CheckedRepetitionNotUniqueSource model) :
    checked.restKeys.all (fun key =>
      key.source.path == checked.firstKey.source.path) = true :=
  checked.commonStarPath

/-- The first reopened level is exactly the selected default or explicit reference group. -/
theorem checkedRepetitionNotUnique_referenceLevel
    (checked : CheckedRepetitionNotUniqueSource model) :
    ((checked.firstKey.source.path.axes.drop
      checked.firstKey.source.path.firstStar).head?.map (·.level)) =
        some checked.referenceGroup.level :=
  checked.referenceLevelOwned

/-- Resolved checked rows preserve their complete topology environment and authored composite-key order. -/
theorem checkedRepetitionNotUnique_resolvedRow_shape
    (checked : CheckedRepetitionNotUniqueSource model)
    (read : Env → FieldId → RawCell) (environment : Env) :
    (checked.resolvedRow read environment).row = environment ∧
      (checked.resolvedRow read environment).key =
        checked.keys.map fun key => key.classify read environment := by
  exact ⟨rfl, rfl⟩

/-- Successful topology resolution is followed only by all-component relevance filtering and checked key classification. -/
theorem checkedRepetitionNotUnique_resolvedRows_of_topology
    (checked : CheckedRepetitionNotUniqueSource model)
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (read : Env → FieldId → RawCell) (topology : ResolvedStarTopology)
    (resolved : checked.firstKey.source.path.resolve document outer = .ok topology) :
    checked.resolvedRows document outer scope read =
      .ok ((topology.environments.filter (checked.rowRelevant scope)).map
        (checked.resolvedRow read)) := by
  simp [CheckedRepetitionNotUniqueSource.resolvedRows, resolved]
  rfl

/-- Once checked row construction succeeds, evaluation delegates exactly to the established branch-independent RNU relation. -/
theorem checkedRepetitionNotUnique_evaluate_of_rows
    (checked : CheckedRepetitionNotUniqueSource model)
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (read : Env → FieldId → RawCell) (rows : List ResolvedRepetitionKeyRow)
    (resolved : checked.resolvedRows document outer scope read = .ok rows) :
    checked.evaluate document outer scope read =
      .ok (evalRepetitionNotUnique rows) := by
  simp [CheckedRepetitionNotUniqueSource.evaluate, resolved]
  rfl

end A12Kernel
