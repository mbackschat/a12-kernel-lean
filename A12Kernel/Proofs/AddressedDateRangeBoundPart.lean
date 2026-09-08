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

/-- Suppression is an admission fact: checked copies of the same endpoint operation execute alike.
    Both copies must already be certified, so this does not permit deleting a required warning
    waiver when a Translate consumer emits the computation again. -/
theorem checkedAddressedDateRangeBoundPart_executeWithRead_eq_of_same_operation
    (left right : CheckedAddressedDateRangeBoundPart model)
    (samePlacement : left.placement = right.placement)
    (sameBound : left.bound = right.bound)
    (samePart : left.part = right.part)
    (input : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell) :
    left.executeWithRead input read = right.executeWithRead input read := by
  cases left
  cases right
  cases samePlacement
  cases sameBound
  cases samePart
  rfl

end A12Kernel
