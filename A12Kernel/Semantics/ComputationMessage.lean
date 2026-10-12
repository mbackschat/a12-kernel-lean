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

/-- Stable Kernel error code for a computed-target failure with no computed instance, measured on
Number invalidity and a DateTime gap constant. -/
def berechnungsWertFehler : String := "berechnungsWertFehler"

/-- Exact-pointer partition of the single computation message stream. Input order is preserved in both projections. -/
structure ComputationMessagePartition (Payload : Type) where
  atComputedInstances : List (ComputationFormalMessage Payload)
  residual : List (ComputationFormalMessage Payload)
  deriving Repr, DecidableEq

/-- Pure partition projection; callers must establish assembly success before exposing a result. Partition messages by exact membership in the computed-instance pointer set. Wildcard and unknown coordinates are compared structurally, never expanded. -/
def partitionComputationMessages (computedInstances : List MessagePointer)
    (messages : List (ComputationFormalMessage Payload)) :
    ComputationMessagePartition Payload := {
  atComputedInstances :=
    messages.filter fun message => computedInstances.contains message.pointer
  residual :=
    messages.filter fun message => !computedInstances.contains message.pointer
}

/-- Result construction fails when two messages share a full error pointer, regardless of payload or code (`spec/09` §3.3). -/
inductive ComputationReportAssemblyFault where
  | duplicatePointer (pointer : MessagePointer)
  deriving Repr, DecidableEq

/-- Check the complete diagnostic stream after execution and before partitioning or application. Pointer coordinates are compared structurally, including wildcard and unknown. -/
def checkComputationReportPointers : List MessagePointer → Except ComputationReportAssemblyFault Unit
  | [] => .ok ()
  | pointer :: remaining =>
      if remaining.contains pointer then .error (.duplicatePointer pointer)
      else checkComputationReportPointers remaining

/-- Assemble the public message partition only when every complete error pointer is unique. -/
def assembleComputationMessages (computedInstances : List MessagePointer)
    (messages : List (ComputationFormalMessage Payload)) :
    Except ComputationReportAssemblyFault (ComputationMessagePartition Payload) := do
  checkComputationReportPointers (messages.map (·.pointer))
  pure (partitionComputationMessages computedInstances messages)

end A12Kernel
