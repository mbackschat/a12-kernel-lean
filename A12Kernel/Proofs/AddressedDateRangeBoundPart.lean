import A12Kernel.Elaboration.AddressedDateRangeBoundPart

/-! # Addressed DateRange endpoint-component laws -/

namespace A12Kernel

/-- Immutable endpoint-component execution is exactly the caller-read route at the document's checked view. -/
theorem checkedAddressedDateRangeBoundPart_executeWithRead_base
    (operation : CheckedAddressedDateRangeBoundPart model)
    (input : CheckedDocument model) :
    operation.executeWithRead input input.read = operation.execute input := by
  rfl

/-- Immutable result construction is exactly the caller-read route at the document's checked view. -/
theorem checkedAddressedDateRangeBoundPart_executeResultWithRead_base
    (operation : CheckedAddressedDateRangeBoundPart model)
    (input : CheckedDocument model)
    (payloadAt : CellAddr → Payload)
    (supplied : List (ComputationFormalMessage Payload)) :
    operation.executeResultWithRead input input.read payloadAt supplied =
      operation.executeResult input payloadAt supplied := by
  rfl

end A12Kernel
