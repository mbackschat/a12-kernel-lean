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

/-- An authored Enumeration key projects the deepest row to its own declared ancestry, then delegates unchanged to the established checked stored-token classifier. -/
theorem checkedRepetitionEnumerationKey_classify
    (key : CheckedRepetitionEnumerationKey model)
    (read : Env → FieldId → CheckedCell) (environment : Env) :
    (CheckedRepetitionKey.enumeration key).classify read environment =
      key.projection.classifyCheckedKeyAt .validation
        (key.source.contextualizeCell
          (environment.take key.source.path.axes.length)
          (read (environment.take key.source.path.axes.length)
            key.source.declaration.id)) := by
  rfl

/-- Checked composite keys contain no repeated direct field identifier. -/
theorem checkedRepetitionNotUnique_uniqueKeyFields
    (checked : CheckedRepetitionNotUniqueSource model) :
    FieldId.firstDuplicate? (checked.keys.map (·.fieldId)) = none :=
  checked.uniqueKeyFields

/-- Every checked key group is an ancestor-or-equal prefix of the selected terminal group. -/
theorem checkedRepetitionNotUnique_keyGroupsOnBranch
    (checked : CheckedRepetitionNotUniqueSource model) :
    checked.keys.all (fun key =>
      key.source.declaration.groupPath.isPrefixOf checked.terminalGroup) = true :=
  checked.keyGroupsOnBranch

/-- At least one checked key owns the selected terminal group. -/
theorem checkedRepetitionNotUnique_terminalGroupOwned
    (checked : CheckedRepetitionNotUniqueSource model) :
    checked.keys.any (fun key =>
      key.source.declaration.groupPath == checked.terminalGroup) = true :=
  checked.terminalGroupOwned

/-- Every component path is an exact repeatable-axis prefix of the deepest-row topology. -/
theorem checkedRepetitionNotUnique_keyPathsWithinTopology
    (checked : CheckedRepetitionNotUniqueSource model) :
    checked.keys.all (fun key =>
      key.source.path.axes ==
        checked.topology.path.axes.take key.source.path.axes.length) = true :=
  checked.keyPathsWithinTopology

/-- The deepest-row topology carries exactly the terminal key group's model-owned repeatable ancestry. -/
theorem checkedRepetitionNotUnique_topologyLevels
    (checked : CheckedRepetitionNotUniqueSource model) :
    checked.topology.path.axes.map (·.level) =
      model.repeatableScopeForGroupPath checked.terminalGroup :=
  checked.topologyLevelsOwned

/-- The first reopened level is exactly the selected default or explicit reference group. -/
theorem checkedRepetitionNotUnique_referenceLevel
    (checked : CheckedRepetitionNotUniqueSource model) :
    ((checked.topology.path.axes.drop
      checked.topology.path.firstStar).head?.map (·.level)) =
        some checked.referenceGroup.level :=
  checked.referenceLevelOwned

/-- The indexed-key refusal certificate preserves the exact RNU target, semantic-index selection,
error field, and authored text key that justified its carrier-specific diagnostic. -/
theorem checkedRepetitionNotUniqueSemanticIndexRefusal_identity
    (checked : CheckedRepetitionNotUniqueSemanticIndexRefusal model) :
    (checked.source.ruleGroup == checked.declaringGroup) = true ∧
      (checked.source.referenceGroup == checked.selection.group) = true ∧
      (checked.source.firstKey.source.declaration ==
        checked.selection.targetDeclaration) = true ∧
      (checked.selection.targetDeclaration.id == checked.errorField) = true ∧
      (checked.selection.key == .literal (.text checked.token)) = true := by
  exact ⟨checked.ruleGroupRetained, checked.referenceGroupSelected,
    checked.targetSelected, checked.errorFieldSelected, checked.keyRetained⟩

/-- Every checked instance projects the exact measured carrier diagnostic; invalid or wider shapes
cannot construct this certificate. -/
@[simp]
theorem checkedRepetitionNotUniqueSemanticIndexRefusal_diagnostic
    (checked : CheckedRepetitionNotUniqueSemanticIndexRefusal model) :
    checked.diagnostic = .semanticIndexNotAllowed := by
  rfl

/-- An inferred default reference group contributes no field references beyond the authored key fields, even though the checked source retains that resolved group for evaluation. -/
theorem checkedRepetitionNotUnique_referencesField_inferred
    (checked : CheckedRepetitionNotUniqueSource model)
    (field : FieldId)
    (origin : checked.referenceOrigin = .inferredDefault) :
    checked.referencesField field =
      checked.keys.any (fun key => key.fieldId == field) := by
  simp [CheckedRepetitionNotUniqueSource.referencesField, origin]

/-- An authored `@From` contributes every declaration in its resolved group subtree to field-reference detection. -/
theorem checkedRepetitionNotUnique_referencesField_authored_subtree
    (checked : CheckedRepetitionNotUniqueSource model)
    (field : FieldId) (declaration : FlatFieldDecl)
    (origin : checked.referenceOrigin = .authoredFrom)
    (lookup : model.lookupUniqueId field = .ok declaration)
    (within :
      checked.referenceGroup.path.isPrefixOf declaration.groupPath = true) :
    checked.referencesField field = true := by
  simp [CheckedRepetitionNotUniqueSource.referencesField,
    ResolvedGroupReference.referencesField, origin, lookup, within]

/-- Even an authored `@From` does not reference a non-key declaration outside the resolved group subtree. -/
theorem checkedRepetitionNotUnique_referencesField_authored_outside
    (checked : CheckedRepetitionNotUniqueSource model)
    (field : FieldId) (declaration : FlatFieldDecl)
    (origin : checked.referenceOrigin = .authoredFrom)
    (notKey :
      checked.keys.any (fun key => key.fieldId == field) = false)
    (lookup : model.lookupUniqueId field = .ok declaration)
    (outside :
      checked.referenceGroup.path.isPrefixOf declaration.groupPath = false) :
    checked.referencesField field = false := by
  simp [CheckedRepetitionNotUniqueSource.referencesField,
    ResolvedGroupReference.referencesField, origin, notKey, lookup, outside]

/-- Resolved checked rows preserve their complete topology environment and authored composite-key order. -/
theorem checkedRepetitionNotUnique_resolvedRow_shape
    (checked : CheckedRepetitionNotUniqueSource model)
    (read : Env → FieldId → CheckedCell) (environment : Env) :
    (checked.resolvedRow read environment).row = environment ∧
      (checked.resolvedRow read environment).key =
        checked.keys.map fun key => key.classify read environment := by
  exact ⟨rfl, rfl⟩

/-- Successful topology resolution is followed only by all-component relevance filtering and checked key classification. -/
theorem checkedRepetitionNotUnique_resolvedRows_of_topology
    (checked : CheckedRepetitionNotUniqueSource model)
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (read : Env → FieldId → CheckedCell) (topology : ResolvedStarTopology)
    (resolved : checked.topology.path.resolve document outer = .ok topology) :
    checked.resolvedRows document outer scope read =
      .ok ((topology.environments.filter (checked.rowRelevant scope)).map
        (checked.resolvedRow read)) := by
  simp [CheckedRepetitionNotUniqueSource.resolvedRows, resolved]
  rfl

/-- Once checked row construction succeeds, evaluation delegates exactly to the established branch-independent RNU relation. -/
theorem checkedRepetitionNotUnique_evaluate_of_rows
    (checked : CheckedRepetitionNotUniqueSource model)
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (read : Env → FieldId → CheckedCell)
    (rows : List ResolvedRepetitionKeyRow)
    (resolved : checked.resolvedRows document outer scope read = .ok rows) :
    checked.evaluate document outer scope read =
      .ok (evalRepetitionNotUnique rows) := by
  simp [CheckedRepetitionNotUniqueSource.evaluate, resolved]
  rfl

/-- Once immutable checked-document row construction succeeds, evaluation changes no key, order, cluster, or verdict; it delegates to the same branch-independent relation. -/
theorem checkedRepetitionNotUnique_evaluateChecked_of_rows
    (checked : CheckedRepetitionNotUniqueSource model)
    (document : CheckedDocument model) (outer : Env)
    (scope : ValidationRelevanceScope)
    (rows : List ResolvedRepetitionKeyRow)
    (resolved :
      checked.resolvedRowsChecked document outer scope = .ok rows) :
    checked.evaluateChecked document outer scope =
      .ok (evalRepetitionNotUnique rows) := by
  simp [CheckedRepetitionNotUniqueSource.evaluateChecked, resolved]
  rfl

end A12Kernel
