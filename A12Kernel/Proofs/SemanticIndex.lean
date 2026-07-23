import A12Kernel.Proofs.NumericComparison
import A12Kernel.Semantics.SemanticIndex

/-! # Resolved semantic-index consumer laws -/

namespace A12Kernel

private def resolvedIndexEntry (token : String) (target : CheckedCell) :
    ResolvedSemanticIndexEntry :=
  { token, target }

/-- Computation rejects an unavailable index column before consulting either the requested token or a clean entry. -/
theorem semanticIndex_computation_unavailableKey
    (entries : List ResolvedSemanticIndexEntry) (cause : FormalCause)
    (token : String) :
    ({ entries, unavailableKey := some cause } :
      ResolvedSemanticIndexColumn).lookupValue .computation token =
        .poison cause := by
  rfl

/-- Validation delegates a clean head match to ordinary target observation even when another index key made the column unavailable. -/
theorem semanticIndex_validation_cleanMatch_ignores_unavailableKey
    (token : String) (target : CheckedCell)
    (remaining : List ResolvedSemanticIndexEntry)
    (cause : FormalCause) :
    ({ entries := resolvedIndexEntry token target :: remaining
       unavailableKey := some cause } :
      ResolvedSemanticIndexColumn).lookupValue .validation token =
        observeCell .validation target := by
  simp [ResolvedSemanticIndexColumn.lookupValue,
    ResolvedSemanticIndexColumn.lookupKey,
    ResolvedSemanticIndexColumn.targetFor?, resolvedIndexEntry]

/-- On a clean column, a selected target is observed by the requested phase without an index-specific reinterpretation. -/
theorem semanticIndex_cleanMatch_observes_target
    (phase : Phase) (token : String) (target : CheckedCell)
    (remaining : List ResolvedSemanticIndexEntry) :
    ({ entries := resolvedIndexEntry token target :: remaining
       unavailableKey := none } :
      ResolvedSemanticIndexColumn).lookupValue phase token =
        observeCell phase target := by
  cases phase <;> simp [ResolvedSemanticIndexColumn.lookupValue,
    ResolvedSemanticIndexColumn.lookupKey,
    ResolvedSemanticIndexColumn.targetFor?, resolvedIndexEntry]

/-- A nonmatching entry cannot affect an indexed value read, irrespective of its target state. -/
theorem semanticIndex_nonmatchingEntry_irrelevant
    (phase : Phase) (requested other : String) (target : CheckedCell)
    (remaining : List ResolvedSemanticIndexEntry)
    (unavailableKey : Option FormalCause)
    (notMatch : (other == requested) = false) :
    ({ entries := resolvedIndexEntry other target :: remaining
       unavailableKey } :
      ResolvedSemanticIndexColumn).lookupValue phase requested =
    ({ entries := remaining, unavailableKey } :
      ResolvedSemanticIndexColumn).lookupValue phase requested := by
  cases phase <;> cases unavailableKey <;>
    simp [ResolvedSemanticIndexColumn.lookupValue,
      ResolvedSemanticIndexColumn.lookupKey,
      ResolvedSemanticIndexColumn.targetFor?, resolvedIndexEntry, notMatch]

/-- A clean column with no entry returns the empty observation in either phase. -/
theorem semanticIndex_cleanNoMatch_is_empty
    (phase : Phase) (token : String) :
    ({ entries := [], unavailableKey := none } :
      ResolvedSemanticIndexColumn).lookupValue phase token = .empty := by
  cases phase <;> rfl

/-- The same unresolved no-match is validation-unknown but computation-poisoned. -/
theorem semanticIndex_unavailableNoMatch_phaseSplit
    (cause : FormalCause) (token : String) :
    ({ entries := [], unavailableKey := some cause } :
      ResolvedSemanticIndexColumn).lookupValue .validation token =
        .unknown cause ∧
    ({ entries := [], unavailableKey := some cause } :
      ResolvedSemanticIndexColumn).lookupValue .computation token =
        .poison cause := by
  constructor <;> rfl

/-- A clean no-match becomes the existing signedness-aware empty Number operand rather than unknown. -/
theorem semanticIndex_cleanNoMatch_numberOperand
    (field : NumField) (token : String) :
    ({ entries := [], unavailableKey := none } :
      ResolvedSemanticIndexColumn).validationNumberOperand field token =
        .value 0 (.emptyNumber field.signed) := by
  rfl

/-- The indexed no-match consumer inherits the established direct-Number `>=` polarity law. -/
theorem semanticIndex_cleanNoMatch_greaterEqual_polarity
    (field : NumField) (token : String) (expected : Rat)
    (holds : NumericComparisonOp.greaterEqual.holds 0 expected = true) :
    NumericComparisonOp.greaterEqual.evalFixedRight
        (({ entries := [], unavailableKey := none } :
          ResolvedSemanticIndexColumn).validationNumberOperand field token)
        expected =
      .fired (if field.signed then .omission else .value) := by
  simpa [semanticIndex_cleanNoMatch_numberOperand] using
    emptyNumberGreaterEqualFiring_polarity field.signed expected holds

/-- Presence makes the clean indexed no-match boundary explicit in both phases: the absent row behaves exactly like an empty target cell. -/
theorem semanticIndex_cleanNoMatch_presence (token : String) :
    let column : ResolvedSemanticIndexColumn :=
      { entries := [], unavailableKey := none }
    column.validationFilled token = .notFired ∧
      column.validationNotFilled token = .fired .omission ∧
      column.computationFilled token = .notTrue ∧
      column.computationNotFilled token = .holds := by
  simp [ResolvedSemanticIndexColumn.validationFilled,
    ResolvedSemanticIndexColumn.validationNotFilled,
    ResolvedSemanticIndexColumn.computationFilled,
    ResolvedSemanticIndexColumn.computationNotFilled,
    ResolvedSemanticIndexColumn.lookupValue,
    ResolvedSemanticIndexColumn.lookupKey,
    ResolvedSemanticIndexColumn.targetFor?]

/-- Validation presence preserves match-first lookup: both predicates consume the selected target even when another key made the column unavailable. -/
theorem semanticIndex_validation_cleanMatch_presence_ignores_unavailableKey
    (token : String) (target : CheckedCell)
    (remaining : List ResolvedSemanticIndexEntry)
    (cause : FormalCause) :
    let column : ResolvedSemanticIndexColumn :=
      { entries := resolvedIndexEntry token target :: remaining
        unavailableKey := some cause }
    column.validationFilled token =
        (observeCell .validation target).evalValidationFilled ∧
      column.validationNotFilled token =
        (observeCell .validation target).evalValidationNotFilled := by
  simp [ResolvedSemanticIndexColumn.validationFilled,
    ResolvedSemanticIndexColumn.validationNotFilled,
    ResolvedSemanticIndexColumn.lookupValue,
    ResolvedSemanticIndexColumn.lookupKey,
    ResolvedSemanticIndexColumn.targetFor?, resolvedIndexEntry]

/-- Computation presence preserves column-first lookup: either predicate returns the unavailable-key poison before a clean matching target can contribute. -/
theorem semanticIndex_computation_unavailableKey_presence
    (entries : List ResolvedSemanticIndexEntry) (cause : FormalCause)
    (token : String) :
    let column : ResolvedSemanticIndexColumn :=
      { entries, unavailableKey := some cause }
    column.computationFilled token = .poison cause ∧
      column.computationNotFilled token = .poison cause := by
  constructor <;> rfl

/-- A clean indexed no-match contributes one instantiated empty classification in validation and one empty slot in computation. -/
theorem semanticIndex_cleanNoMatch_fillOperand (token : String) :
    let column : ResolvedSemanticIndexColumn :=
      { entries := [], unavailableKey := none }
    column.validationFillTally token =
        { filled := 0, empty := 1, unknown := 0, uninstantiated := 0 } ∧
      column.computationFillSlot token = .empty := by
  constructor <;> rfl

/-- Validation's match-first gate remains intact when an indexed read is classified for a field-fill tally. -/
theorem semanticIndex_validation_cleanMatch_fillTally_ignores_unavailableKey
    (token : String) (target : CheckedCell)
    (remaining : List ResolvedSemanticIndexEntry)
    (cause : FormalCause) :
    ({ entries := resolvedIndexEntry token target :: remaining
       unavailableKey := some cause } :
      ResolvedSemanticIndexColumn).validationFillTally token =
        (observeCell .validation target).asValidationFillTally := by
  simp [ResolvedSemanticIndexColumn.validationFillTally,
    ResolvedSemanticIndexColumn.lookupValue,
    ResolvedSemanticIndexColumn.lookupKey,
    ResolvedSemanticIndexColumn.targetFor?, resolvedIndexEntry]

/-- Computation's column-first gate likewise becomes an exact poison slot before any quantifier scan consumes the indexed operand. -/
theorem semanticIndex_computation_unavailableKey_fillSlot
    (entries : List ResolvedSemanticIndexEntry) (cause : FormalCause)
    (token : String) :
    ({ entries, unavailableKey := some cause } :
      ResolvedSemanticIndexColumn).computationFillSlot token = .poison cause := by
  rfl

/-- Authored operand order remains observable after indexed-slot projection: a prior filled witness decides `AtLeastOne`, but reaching the unavailable indexed column first poisons. -/
theorem semanticIndex_computationFillSlot_orderObservable
    (entries : List ResolvedSemanticIndexEntry) (cause : FormalCause)
    (token : String) :
    let indexed :=
      ({ entries, unavailableKey := some cause } :
        ResolvedSemanticIndexColumn).computationFillSlot token
    FieldFillQuantifier.atLeastOneFieldFilled.evalComputation
        [.filled, indexed] = .holds ∧
      FieldFillQuantifier.atLeastOneFieldFilled.evalComputation
        [indexed, .filled] = .poison cause := by
  constructor <;> rfl

end A12Kernel
