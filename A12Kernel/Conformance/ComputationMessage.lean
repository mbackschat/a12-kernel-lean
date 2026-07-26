import A12Kernel.Semantics.ComputationMessage

/-! # Computation-message pointer and Number-result locks -/

namespace A12Kernel.Conformance.ComputationMessage

open A12Kernel

private def address : CellAddr := { field := 7, path := [1] }

private def message (pointer : ComputationErrorPointer)
    (payload : String) : ComputationFormalMessage String := {
  pointer
  errorCode := berechnungsWertFehler
  messageType := .value
  payload
}

/- Exact addresses embed into the wider error-pointer domain, while wildcard and unknown coordinates never masquerade as concrete cells. -/
example :
    ComputationErrorPointer.toCellAddr?
        (ComputationErrorPointer.ofCellAddr address) = some address ∧
      ComputationErrorPointer.toCellAddr?
        { field := 7, coordinates := [.wildcard] } = none ∧
      ComputationErrorPointer.toCellAddr?
        { field := 7, coordinates := [.unknown] } = none := by
  native_decide

/- Partition membership follows exact pointer identity only. Payload bytes are opaque, and an unknown coordinate does not match its concrete sibling. -/
example :
    let exact := ComputationErrorPointer.ofCellAddr address
    let unknown : ComputationErrorPointer :=
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
