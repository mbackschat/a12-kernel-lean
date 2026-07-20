import A12Kernel.Semantics.NumericComparison
import A12Kernel.Semantics.Observation

/-! # Resolved literal-key semantic-index lookup

This capsule starts after path resolution, literal-token nonemptiness, key normalization, and generated index-field checks. Each entry therefore carries one uniquely resolvable canonical token and its target cell. Empty, duplicate, or malformed key rows are excluded from `entries`; `unavailableKey` retains one formal cause establishing that the column is not fully resolvable. Selecting that retained cause is an internal refinement, not an externally observed priority claim.

Validation and computation deliberately consume that same resolved column differently. Validation accepts a clean unique match despite an unrelated unavailable key and consults column invalidity only after no match. Computation checks column invalidity before lookup, so any unavailable key poisons every indexed read. No match over a clean column and a matched empty target both return `CellObservation.empty`.
-/

namespace A12Kernel

/-- One uniquely addressable row after canonical index-key normalization and index-field checking. -/
structure ResolvedSemanticIndexEntry where
  token : String
  target : CheckedCell
  deriving Repr, DecidableEq

/-- A resolved index column. `entries` omits every unavailable key row and every participant in a duplicate key; `unavailableKey` records one such cause when one exists. -/
structure ResolvedSemanticIndexColumn where
  entries : List ResolvedSemanticIndexEntry
  unavailableKey : Option FormalCause
  deriving Repr, DecidableEq

namespace ResolvedSemanticIndexColumn

/-- Deterministic reference lookup over the preceding unique-entry contract. The first-match totality behavior is outside the claimed fragment when callers violate uniqueness. -/
def targetFor? (token : String) :
    List ResolvedSemanticIndexEntry → Option CheckedCell
  | [] => none
  | entry :: remaining =>
      if entry.token == token then some entry.target
      else targetFor? token remaining

/-- Read one literal-key semantic-index value under the phase-specific lookup policy. Inputs that violate the preceding unique-key contract are outside the claimed fragment; this total function chooses the first supplied clean match. Presence and field-fill consumers remain separate projections of the resulting observation. -/
def lookupValue (column : ResolvedSemanticIndexColumn)
    (phase : Phase) (token : String) : CellObservation :=
  match phase with
  | .validation =>
      match targetFor? token column.entries with
      | some target => observeCell .validation target
      | none =>
          match column.unavailableKey with
          | some cause => .unknown cause
          | none => .empty
  | .computation =>
      match column.unavailableKey with
      | some cause => .poison cause
      | none =>
          match targetFor? token column.entries with
          | some target => observeCell .computation target
          | none => .empty

/-- Feed one resolved validation-side Number lookup into the shared direct-comparison empty and polarity rule. -/
def validationNumberOperand (column : ResolvedSemanticIndexColumn)
    (field : NumField) (token : String) : NumericOperand :=
  (column.lookupValue .validation token).asValidationNumericOperand field

end ResolvedSemanticIndexColumn

end A12Kernel
