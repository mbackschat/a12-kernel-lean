import A12Kernel.Document
import A12Kernel.Semantics.Observation

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
  /-- Checked columns preserve the physical row; scalar-only legacy columns have no address. -/
  environment : Option Env := none
  deriving Repr, DecidableEq

/-- A resolved index column. `entries` omits every unavailable key row and every participant in a duplicate key; `unavailableKey` records one such cause when one exists. -/
structure ResolvedSemanticIndexColumn where
  entries : List ResolvedSemanticIndexEntry
  unavailableKey : Option FormalCause
  deriving Repr, DecidableEq

end A12Kernel
