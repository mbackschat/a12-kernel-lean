import A12Kernel.Document

/-! # Shared formal-message pointers

A12 uses one partially-known pointer domain for validation, computation, registered-field, and custom-condition message channels. This normalized semantic owner retains resolved field identity plus the repetition coordinates those channels observe. It deliberately defines no textual codec: exact document addresses remain `CellAddr`, while raw kernel pointer-factory syntax and malformed name/index arity are outside the resolved field-instance boundary.
-/

namespace A12Kernel

/-- One repetition coordinate in a partially-known message pointer. Wildcard and unknown are values, not matching operators. -/
inductive MessageRepetitionCoordinate where
  | concrete (index : Nat)
  | wildcard
  | unknown
  deriving Repr, DecidableEq

/-- One resolved field identity with its possibly-partial repetition coordinates. Every formal-message channel shares this type. -/
structure MessagePointer where
  field : FieldId
  coordinates : List MessageRepetitionCoordinate
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
  | .wildcard :: _ | .unknown :: _ => none

/-- Recover an exact document address only when every repetition coordinate is concrete. -/
def toCellAddr? (pointer : MessagePointer) : Option CellAddr := do
  let path ← toConcretePath? pointer.coordinates
  pure { field := pointer.field, path }

end MessagePointer

end A12Kernel
