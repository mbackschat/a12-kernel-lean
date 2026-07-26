import A12Kernel.Document

/-! # Computation-phase formal-message pointers

The kernel partitions one computation message stream by exact pointer identity. This owner represents that wider pointer and the partition while keeping localized payload bytes opaque. It performs no template parsing, rendering, validation, or message production.
-/

namespace A12Kernel

/-- One repetition coordinate in a possibly partial computation-error pointer. The tagged cases keep the kernel's wildcard and unknown sentinels distinct from concrete row numbers. -/
inductive RepetitionCoordinate where
  | concrete (index : Nat)
  | wildcard
  | unknown
  deriving Repr, DecidableEq

/-- A computation-error pointer. Equality compares the complete field and coordinate list; wildcard and unknown are values, not matching operators. -/
structure ComputationErrorPointer where
  field : FieldId
  coordinates : List RepetitionCoordinate
  deriving Repr, DecidableEq

namespace ComputationErrorPointer

/-- Embed one exact document address into the wider formal-message pointer domain. -/
def ofCellAddr (address : CellAddr) : ComputationErrorPointer := {
  field := address.field
  coordinates := address.path.map .concrete
}

/-- Recover a concrete path only when every coordinate is concrete. -/
def toConcretePath? : List RepetitionCoordinate → Option (List Nat)
  | [] => some []
  | .concrete index :: remaining =>
      (toConcretePath? remaining).map (index :: ·)
  | .wildcard :: _ | .unknown :: _ => none

/-- Recover an exact document address only when every repetition coordinate is concrete. -/
def toCellAddr? (pointer : ComputationErrorPointer) : Option CellAddr := do
  let path ← toConcretePath? pointer.coordinates
  pure { field := pointer.field, path }

end ComputationErrorPointer

/-- One already-rendered computation-phase formal message. Severity is always ERROR at this boundary; payload bytes remain parametric and uninspected. -/
structure ComputationFormalMessage (Payload : Type) where
  pointer : ComputationErrorPointer
  errorCode : String
  messageType : Polarity
  payload : Payload
  deriving Repr, DecidableEq

/-- Stable kernel error code for a value-less computed Number failure. -/
def berechnungsWertFehler : String := "berechnungsWertFehler"

/-- Exact-pointer partition of the single computation message stream. Input order is preserved in both projections. -/
structure ComputationMessagePartition (Payload : Type) where
  atComputedInstances : List (ComputationFormalMessage Payload)
  residual : List (ComputationFormalMessage Payload)
  deriving Repr, DecidableEq

/-- Partition messages by exact membership in the computed-instance pointer set. Wildcard and unknown coordinates are compared structurally, never expanded. -/
def partitionComputationMessages (computedInstances : List ComputationErrorPointer)
    (messages : List (ComputationFormalMessage Payload)) :
    ComputationMessagePartition Payload := {
  atComputedInstances :=
    messages.filter fun message => computedInstances.contains message.pointer
  residual :=
    messages.filter fun message => !computedInstances.contains message.pointer
}

end A12Kernel
