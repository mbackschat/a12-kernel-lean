import A12Kernel.Semantics.ComputationMessage

/-! # Computation-message pointer and Number-result locks -/

namespace A12Kernel.Conformance.ComputationMessage

open A12Kernel

private def address : CellAddr := { field := 7, path := [1] }

private def message (pointer : MessagePointer)
    (payload : String) : ComputationFormalMessage String := {
  pointer
  errorCode := berechnungsWertFehler
  messageType := .value
  payload
}

/- Exact addresses embed into the wider error-pointer domain, while wildcard and unknown coordinates never masquerade as concrete cells. -/
example :
    MessagePointer.toCellAddr?
        (MessagePointer.ofCellAddr address) = some address ∧
      MessagePointer.toCellAddr?
        { field := 7, coordinates := [.wildcard] } = none ∧
      MessagePointer.toCellAddr?
        { field := 7, coordinates := [.unknown] } = none := by
  native_decide

/- Partition membership follows exact pointer identity only. Payload bytes are opaque, and an unknown coordinate does not match its concrete sibling. -/
example :
    let exact := MessagePointer.ofCellAddr address
    let unknown : MessagePointer :=
      { field := 7, coordinates := [.unknown] }
    let partition := partitionComputationMessages [exact] [
      message unknown "$Field$ $$ $<fieldName>$",
      message exact "first",
      message exact "second"
    ]
    partition.atComputedInstances = [
      message exact "first", message exact "second"
    ] ∧
      partition.residual = [
        message unknown "$Field$ $$ $<fieldName>$"
      ] := by
  native_decide

end A12Kernel.Conformance.ComputationMessage
