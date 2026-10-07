import A12Kernel.Semantics.SemanticIndexColumn
import A12Kernel.Semantics.MessagePointer

/-! # Message-pointer semantic-index cache

This is the message-coordinate boundary for [§10 paths and references](../../spec/08-paths-and-references.md). The input is the admitted cache insertion sequence, rather than physical document row order. The selected-reference checkpoint in [message and pointer sources](../../docs/sources/message-and-pointer-probes.md#src-selected-message-reference-resolution) establishes overwrite lookup independently of duplicate-excluding value selection. Cache population order, cell admission, payload reading, and phase policy belong outside this boundary.
-/

namespace A12Kernel

/-- One insertion after index-field admission and key normalization. Invalid and empty index cells do not enter this sequence. -/
structure MessageIndexInsertion where
  group : RepeatableLevel
  parentPath : List Nat
  key : SemanticIndexKey
  row : Nat
  deriving Repr, DecidableEq

/-- The actual admitted cache insertion sequence; its order must not be inferred from document rows. -/
structure MessageIndexCache where
  insertions : List MessageIndexInsertion
  deriving Repr, DecidableEq

namespace MessageIndexCache

/-- Resolve the last matching insertion in this parent and group. An absent query key or absent association yields an unknown coordinate. -/
def lookup (cache : MessageIndexCache) (group : RepeatableLevel)
    (parentPath : List Nat) (key : Option SemanticIndexKey) :
    MessageRepetitionCoordinate :=
  match key with
  | none => .unknown
  | some key =>
      if key = .text "" then .unknown
      else cache.insertions.foldl (fun selected insertion =>
        if insertion.group = group ∧ insertion.parentPath = parentPath ∧
            insertion.key = key then .concrete insertion.row
        else selected) .unknown

end MessageIndexCache

end A12Kernel
