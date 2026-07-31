import A12Kernel.Proofs.AddressedNumberField
import A12Kernel.Elaboration.AddressedNumberExtremum

/-! # Same-scope repeatable direct-Number extrema certificate -/

namespace A12Kernel

/-- Every checked extremum retains every ordered Number-kind witness, one target, and the maximum operand scale as its exact target scale. -/
theorem checkedAddressedNumberExtremum_sound
    (operation : CheckedAddressedNumberExtremum model) :
    operation.first.placement.sourceDeclaration.toNumberField? =
        some operation.first.source ∧
      (∀ source ∈ operation.rest,
        source.placement.sourceDeclaration.toNumberField? =
          some source.source) ∧
      (∀ source ∈ operation.rest,
        operation.first.placement.targetField =
          source.placement.targetField) ∧
      operation.first.placement.targetPolicy.info.scale =
        addressedNumberExtremumResultScale operation.first
          operation.rest := by
  refine ⟨operation.first.sourceCertified, ?_, operation.restSameTarget,
    operation.sameScale⟩
  intro source _
  exact source.sourceCertified

end A12Kernel
