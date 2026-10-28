import A12Kernel.Document
import A12Kernel.Semantics.GroupReference

/-! # Shared formal-message pointers

A12 uses one partially-known pointer domain for validation, computation, registered-field, and custom-condition message channels. This normalized semantic owner retains resolved field identity plus the repetition coordinates those channels observe. It deliberately defines no textual codec: exact document addresses remain `CellAddr`, while raw kernel pointer-factory syntax and malformed name/index arity are outside the resolved field-instance boundary.
-/

namespace A12Kernel

/-- One repetition coordinate in a partially-known message pointer. Wildcard, unknown and the
parallel-iteration placeholder are values, not matching operators. The placeholder is the Kernel's
`-6`, which a reference keeps at a keyed error group's own level beside a join
([checkpoint](../../docs/sources/key-join-and-parallel-probes.md#src-keyed-group-beside-join),
`runtime-keyed`). -/
inductive MessageRepetitionCoordinate where
  | concrete (index : Nat)
  | wildcard
  | unknown
  | parallelIteration
  deriving Repr, DecidableEq

/-- One resolved field identity with its possibly-partial repetition coordinates. Every formal-message channel shares this type. -/
structure MessagePointer where
  field : FieldId
  coordinates : List MessageRepetitionCoordinate
  /-- The root or fixed group whose one instance a key failed to select. The Kernel names that
  group's level `-5`, as it names an unresolved repeatable row
  ([runtime open cells](../../docs/sources/model-structure-and-declaration-probes.md#src-runtime-open-cells),
  `ixroot-other`, `ixfix-other`). -/
  unresolvedInstance : Option GroupPath := none
  deriving Repr, DecidableEq

namespace MessagePointer

/-- Embed one exact document address into the wider formal-message pointer domain. -/
def ofCellAddr (address : CellAddr) : MessagePointer := {
  field := address.field
  coordinates := address.path.map .concrete
}

/-- Recover a concrete path only when every coordinate is concrete. -/
def toConcretePath? : List MessageRepetitionCoordinate → Option (List Nat)
  | [] => some []
  | .concrete index :: remaining =>
      (toConcretePath? remaining).map (index :: ·)
  | .wildcard :: _ | .unknown :: _ | .parallelIteration :: _ => none

/-- Recover an exact document address only when every repetition coordinate is concrete and every
instance is resolved. -/
def toCellAddr? (pointer : MessagePointer) : Option CellAddr := do
  if pointer.unresolvedInstance.isSome then none
  let path ← toConcretePath? pointer.coordinates
  pure { field := pointer.field, path }

end MessagePointer

end A12Kernel
