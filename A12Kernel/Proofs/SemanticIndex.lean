import A12Kernel.Proofs.NumericComparison
import A12Kernel.Semantics.SemanticIndex

/-! # Resolved semantic-index value-read laws -/

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

end A12Kernel
