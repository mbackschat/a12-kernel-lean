import A12Kernel.Semantics.MessagePointer

/-! # Computation-phase formal-message partition

The kernel partitions one computation message stream by exact shared message-pointer identity. This owner represents the computation payload and partition while keeping localized payload bytes opaque. It performs no template parsing, rendering, validation, or message production.
-/

namespace A12Kernel

/-- One already-rendered computation-phase formal message. Severity is always ERROR at this boundary; payload bytes remain parametric and uninspected. -/
structure ComputationFormalMessage (Payload : Type) where
  pointer : MessagePointer
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
def partitionComputationMessages (computedInstances : List MessagePointer)
    (messages : List (ComputationFormalMessage Payload)) :
    ComputationMessagePartition Payload := {
  atComputedInstances :=
    messages.filter fun message => computedInstances.contains message.pointer
  residual :=
    messages.filter fun message => !computedInstances.contains message.pointer
}

end A12Kernel
