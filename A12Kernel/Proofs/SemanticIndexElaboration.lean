import A12Kernel.Elaboration.SemanticIndex
import A12Kernel.Proofs.SemanticIndex

/-! # Checked semantic-index construction laws -/

namespace A12Kernel

/-- The checked literal suffix cannot drift from `RuleGroup` to a child or sibling group: its
certificate identifies the exact containing group supplied to elaboration. -/
theorem checkedRuleGroupSemanticIndex_selectsRuleGroup
    (checked : CheckedRuleGroupSemanticIndexSource model) :
    checked.selection.group.path = checked.ruleGroup := by
  simpa using checked.groupSelected

/-- The exact missing-index code is carrier-specific: the general semantic-index error remains
unmapped until a checked carrier supplies its own measured projection. -/
theorem semanticIndex_missingIndex_requiresCarrierProjection
    (group : GroupPath) :
    SemanticIndexElabError.diagnostic? (.missingIndexField group) = none := by
  rfl

/-- The checked filled-field pair has one semantic-index selection identity while retaining two
distinct target declarations in authored order. -/
theorem checkedFilledFieldCountSemanticIndexPair_identity
    (checked : CheckedFilledFieldCountSemanticIndexPair model) :
    checked.first.group = checked.second.group ∧
      checked.first.indexDeclaration = checked.second.indexDeclaration ∧
      checked.first.key = .literal (.text checked.token) ∧
      checked.second.key = .literal (.text checked.token) ∧
      checked.first.targetDeclaration.id ≠ checked.second.targetDeclaration.id := by
  constructor
  · simpa using checked.sharedGroup
  constructor
  · simpa using checked.sharedIndex
  constructor
  · simpa using checked.firstKeyRetained
  constructor
  · simpa using checked.secondKeyRetained
  · simpa using checked.distinctTargets

/-- The indexed-group field-fill surface is closed to the two Kernel-locked carriers. -/
theorem indexedGroupFieldFillOperator_exhaustive
    (operator : IndexedGroupFieldFillOperator) :
    operator = .allFieldsFilled ∨ operator = .noFieldFilled := by
  cases operator <;> simp

/-- A checked indexed-group/direct-field pair retains one exact text selection and one independently
owned nonrepeatable direct field outside that selected group. -/
theorem checkedIndexedGroupFieldFillPair_identity
    (checked : CheckedIndexedGroupFieldFillPair model) :
    checked.selection.group.path = checked.groupPath ∧
      checked.selection.key = .literal (.text checked.token) ∧
      model.fields.contains checked.field = true ∧
      checked.field.repeatableScope.isEmpty = true ∧
      (!checked.selection.group.path.isPrefixOf checked.field.groupPath) = true := by
  constructor
  · simpa using checked.groupSelected
  constructor
  · simpa using checked.keyRetained
  exact ⟨checked.fieldOwned, checked.fieldNonrepeatable,
    checked.fieldOutsideSelection⟩

/-- The document-backed route delegates key policy to the same semantic-index evaluator after the
shared checked column has been projected, at every index kind. -/
theorem checkedSemanticIndex_preliminary_delegates
    (checked : CheckedSemanticIndexSource model)
    (preliminary : CheckedIndexPreliminary model)
    (keyRaw : RawFlatContext) (phase : Phase) (outer : Env)
    (column : ResolvedSemanticIndexColumn)
    (resolved : checked.resolvePreliminaryColumn preliminary outer =
      .ok column) :
    checked.lookupPreliminaryValue preliminary keyRaw phase outer =
      .ok (column.lookupObservationForIndex phase checked.numericIndex
        (checked.key.observe model keyRaw phase)) := by
  unfold CheckedSemanticIndexSource.lookupPreliminaryValue
  rw [resolved]
  rfl

/-- A Number-indexed source's shared dispatch is the numeric lookup, so the reduced route's own
delegation law and the general one agree rather than describing two policies. -/
theorem checkedNumberSemanticIndex_preliminary_is_numeric
    (checked : CheckedNumberSemanticIndexSource model)
    (column : ResolvedSemanticIndexColumn) (phase : Phase)
    (key : CellObservation) :
    column.lookupObservationForIndex phase
        checked.toCheckedSemanticIndexSource.numericIndex key =
      column.lookupNumberObservation phase key := by
  have witness := checked.indexNumber
  unfold FlatFieldDecl.toNumberField? at witness
  simp only [ResolvedSemanticIndexColumn.lookupObservationForIndex,
    CheckedSemanticIndexSource.numericIndex]
  split at witness <;> simp_all

/-- A successfully resolved checked source delegates phase behavior and numeric-key comparison to the existing resolved semantic-index evaluator. -/
theorem checkedNumberSemanticIndex_lookupValue_delegates
    (checked : CheckedNumberSemanticIndexSource model)
    (raw : RawSingleGroupContext) (keyRaw : RawFlatContext) (phase : Phase)
    (column : ResolvedSemanticIndexColumn)
    (resolved : checked.resolveColumn raw = .ok column) :
    checked.lookupValue raw keyRaw phase =
      .ok (column.lookupNumberObservation phase
        (checked.key.observe model keyRaw phase)) := by
  unfold CheckedNumberSemanticIndexSource.lookupValue
  rw [resolved]
  rfl

/-- The checked validation Number consumer reuses the target declaration's signedness/scale and the sole resolved numeric-key projection. -/
theorem checkedNumberSemanticIndex_validationNumberOperand_delegates
    (checked : CheckedNumberSemanticIndexSource model)
    (raw : RawSingleGroupContext) (keyRaw : RawFlatContext)
    (column : ResolvedSemanticIndexColumn)
    (resolved : checked.resolveColumn raw = .ok column) :
    checked.validationNumberOperand raw keyRaw =
      .ok (column.validationNumberObservedKeyOperand checked.targetField.info
        (checked.key.observe model keyRaw .validation)) := by
  unfold CheckedNumberSemanticIndexSource.validationNumberOperand
  rw [resolved]
  rfl

/-- Malformed one-group topology is rejected before any semantic-index column is exposed. -/
theorem checkedNumberSemanticIndex_invalidTopology
    (checked : CheckedNumberSemanticIndexSource model)
    (raw : RawSingleGroupContext) (error : SingleGroupContextError)
    (invalid : raw.validate = .error error) :
    checked.resolveColumn raw = .error (.topology error) := by
  unfold CheckedNumberSemanticIndexSource.resolveColumn
  rw [invalid]
  rfl

/-- Numeric and exact-text key domains remain disjoint; decimal value normalization cannot accidentally match a non-Number stored token with the same characters. -/
theorem semanticIndex_numberKey_does_not_match_text
    (value : Rat) (text : String) (target : CheckedCell)
    (phase : Phase) :
    ({ entries := [{ token := .text text, target }], unavailableKey := none } :
      ResolvedSemanticIndexColumn).lookupNumberValue phase value = .empty := by
  cases phase <;>
    simp [ResolvedSemanticIndexColumn.lookupNumberValue,
      ResolvedSemanticIndexColumn.lookupKey,
      ResolvedSemanticIndexColumn.targetFor?]

/-- A clean numeric head match reached through either a literal or field-valued Number observation is observed through the requested phase, irrespective of alternate decimal spellings erased by preceding Number admission. -/
theorem semanticIndex_numberKey_cleanMatch
    (value : Rat) (target : CheckedCell)
    (remaining : List ResolvedSemanticIndexEntry) (phase : Phase) :
    ({ entries := { token := .number value, target } :: remaining
       unavailableKey := none } :
      ResolvedSemanticIndexColumn).lookupNumberObservation phase
        (.value (.num value)) =
        observeCell phase target := by
  cases phase <;>
    simp [ResolvedSemanticIndexColumn.lookupNumberObservation,
      ResolvedSemanticIndexColumn.lookupNumberValue,
      ResolvedSemanticIndexColumn.lookupKey,
      ResolvedSemanticIndexColumn.targetFor?]

end A12Kernel
