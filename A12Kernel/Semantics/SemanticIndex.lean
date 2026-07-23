import A12Kernel.Semantics.ComputationCondition
import A12Kernel.Semantics.ComputationFillQuantifier
import A12Kernel.Semantics.FlatValidation
import A12Kernel.Semantics.NumericComparison
import A12Kernel.Semantics.Observation
import A12Kernel.Semantics.ValidationFillQuantifier

/-! # Resolved semantic-index lookup

This capsule starts after path resolution, key admission and normalization, and generated index-field checks. Each entry therefore carries one uniquely resolvable canonical token and its target cell. Empty, duplicate, or malformed key rows are excluded from `entries`; `unavailableKey` retains one formal cause establishing that the column is not fully resolvable. Selecting that retained cause is an internal refinement, not an externally observed priority claim.

Validation and computation deliberately consume that same resolved column differently. Validation accepts a clean unique match despite an unrelated unavailable key and consults column invalidity only after no match. Computation checks column invalidity before lookup, so any unavailable key poisons every indexed read. No match over a clean column and a matched empty target both return `CellObservation.empty`.

A field-valued Number key reaches this boundary as its phase-indexed observation. A present Number delegates to the same normalized lookup as a literal; an empty key performs a no-match while retaining the column policy; formal unavailability remains validation-unknown or computation-poison.
-/

namespace A12Kernel

/-- A canonical semantic-index key after declaration-owned admission and normalization. Number keys compare by numeric value; every other admitted kind remains represented by its exact stored token. -/
inductive SemanticIndexKey where
  | text (token : String)
  | number (value : Rat)
  deriving Repr, BEq, DecidableEq

instance : Coe String SemanticIndexKey := ⟨SemanticIndexKey.text⟩

@[simp] theorem SemanticIndexKey.text_beq (left right : String) :
    ((SemanticIndexKey.text left == SemanticIndexKey.text right) : Bool) =
      (left == right) := by
  rfl

@[simp] theorem SemanticIndexKey.number_beq (left right : Rat) :
    ((SemanticIndexKey.number left == SemanticIndexKey.number right) : Bool) =
      (left == right) := by
  rfl

@[simp] theorem SemanticIndexKey.text_number_beq (text : String) (value : Rat) :
    ((SemanticIndexKey.text text == SemanticIndexKey.number value) : Bool) = false := by
  rfl

@[simp] theorem SemanticIndexKey.number_text_beq (value : Rat) (text : String) :
    ((SemanticIndexKey.number value == SemanticIndexKey.text text) : Bool) = false := by
  rfl

/-- One uniquely addressable row after canonical index-key normalization and index-field checking. -/
structure ResolvedSemanticIndexEntry where
  token : SemanticIndexKey
  target : CheckedCell
  deriving Repr, DecidableEq

/-- A resolved index column. `entries` omits every unavailable key row and every participant in a duplicate key; `unavailableKey` records one such cause when one exists. -/
structure ResolvedSemanticIndexColumn where
  entries : List ResolvedSemanticIndexEntry
  unavailableKey : Option FormalCause
  deriving Repr, DecidableEq

namespace ResolvedSemanticIndexColumn

/-- Deterministic reference lookup over the preceding unique-entry contract. The first-match totality behavior is outside the claimed fragment when callers violate uniqueness. -/
def targetFor? (token : SemanticIndexKey) :
    List ResolvedSemanticIndexEntry → Option CheckedCell
  | [] => none
  | entry :: remaining =>
      if entry.token == token then some entry.target
      else targetFor? token remaining

@[simp] private def noMatch (column : ResolvedSemanticIndexColumn)
    (phase : Phase) : CellObservation :=
  match phase, column.unavailableKey with
  | .validation, some cause => .unknown cause
  | .computation, some cause => .poison cause
  | _, none => .empty

/-- Read one already-normalized semantic-index key under the phase-specific lookup policy. Inputs that violate the preceding unique-key contract are outside the claimed fragment; this total function chooses the first supplied clean match. Presence and field-fill consumers remain separate projections of the resulting observation. -/
def lookupKey (column : ResolvedSemanticIndexColumn)
    (phase : Phase) (token : SemanticIndexKey) : CellObservation :=
  match phase with
  | .validation =>
      match targetFor? token column.entries with
      | some target => observeCell .validation target
      | none => column.noMatch .validation
  | .computation =>
      match column.unavailableKey with
      | some cause => .poison cause
      | none =>
          match targetFor? token column.entries with
          | some target => observeCell .computation target
          | none => column.noMatch .computation

/-- Preserve the original exact-text literal-key surface as a thin projection into the common canonical-key lookup. -/
def lookupValue (column : ResolvedSemanticIndexColumn)
    (phase : Phase) (token : String) : CellObservation :=
  column.lookupKey phase (.text token)

/-- Read one admitted Number key by numeric value, independent of its authored or stored decimal spelling. -/
def lookupNumberValue (column : ResolvedSemanticIndexColumn)
    (phase : Phase) (value : Rat) : CellObservation :=
  column.lookupKey phase (.number value)

private def unavailableNumberKey (phase : Phase)
    (cause : FormalCause) : CellObservation :=
  match phase with
  | .validation => .unknown cause
  | .computation => .poison cause

/-- Resolve one phase-indexed Number key observation through the same canonical column. Empty means a genuine no-match, not an unavailable key; the column's match/no-match phase policy still applies. -/
def lookupNumberObservation (column : ResolvedSemanticIndexColumn)
    (phase : Phase) (key : CellObservation) : CellObservation :=
  match key with
  | .empty => column.noMatch phase
  | .value (.num value) => column.lookupNumberValue phase value
  | .unknown cause | .poison cause => unavailableNumberKey phase cause
  | .value _ => unavailableNumberKey phase .malformed

/-- Feed one resolved numeric-key validation lookup into the same direct-comparison empty and polarity rule as the exact-text entry point. -/
def validationNumberKeyOperand (column : ResolvedSemanticIndexColumn)
    (field : NumField) (value : Rat) : NumericOperand :=
  (column.lookupNumberObservation .validation
    (.value (.num value))).asValidationNumericOperand field

/-- Feed one resolved field-valued Number key observation into the same direct-comparison empty and polarity rule as the literal-key entry point. -/
def validationNumberObservedKeyOperand (column : ResolvedSemanticIndexColumn)
    (field : NumField) (key : CellObservation) : NumericOperand :=
  (column.lookupNumberObservation .validation key).asValidationNumericOperand field

/-- Feed one resolved validation-side Number lookup into the shared direct-comparison empty and polarity rule. -/
def validationNumberOperand (column : ResolvedSemanticIndexColumn)
    (field : NumField) (token : String) : NumericOperand :=
  (column.lookupValue .validation token).asValidationNumericOperand field

/-- Consume one resolved indexed read as validation `FieldFilled`. A clean no-match is therefore not fired rather than skipped or unknown. -/
def validationFilled (column : ResolvedSemanticIndexColumn)
    (token : String) : Verdict :=
  (column.lookupValue .validation token).evalValidationFilled

/-- Consume one resolved indexed read as validation `FieldNotFilled`. A clean no-match fires with omission polarity exactly like an empty target cell. -/
def validationNotFilled (column : ResolvedSemanticIndexColumn)
    (token : String) : Verdict :=
  (column.lookupValue .validation token).evalValidationNotFilled

/-- Consume one resolved indexed read as computation `FieldFilled`, preserving the lookup's column-first poison policy. -/
def computationFilled (column : ResolvedSemanticIndexColumn)
    (token : String) : ComputationConditionResult :=
  (column.lookupValue .computation token).evalComputationFilled

/-- Consume one resolved indexed read as computation `FieldNotFilled`, reversing only clean presence and preserving poison. -/
def computationNotFilled (column : ResolvedSemanticIndexColumn)
    (token : String) : ComputationConditionResult :=
  (column.lookupValue .computation token).evalComputationNotFilled

/-- Classify one resolved indexed validation operand for composition with the existing extensional field-fill tally. -/
def validationFillTally (column : ResolvedSemanticIndexColumn)
    (token : String) : ValidationFillTally :=
  (column.lookupValue .validation token).asValidationFillTally

/-- Classify one resolved indexed computation operand for insertion at its authored position in the existing ordered scan. -/
def computationFillSlot (column : ResolvedSemanticIndexColumn)
    (token : String) : ComputationFillSlot :=
  (column.lookupValue .computation token).asComputationFillSlot

end ResolvedSemanticIndexColumn

end A12Kernel
