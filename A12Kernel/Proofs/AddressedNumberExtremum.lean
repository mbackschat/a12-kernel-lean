import A12Kernel.Proofs.AddressedNumberField
import A12Kernel.Elaboration.AddressedNumberExtremum

/-! # Same-scope repeatable direct-Number extrema certificate -/

namespace A12Kernel

/-- Every checked extremum retains every ordered Number-kind witness, one target, and the maximum operand scale as its exact target scale. -/
theorem checkedAddressedNumberExtremum_sound
    (operation : CheckedAddressedNumberExtremum model) :
    operation.pair.left.placement.sourceDeclaration.toNumberField? =
        some operation.pair.left.source ∧
      operation.pair.right.placement.sourceDeclaration.toNumberField? =
        some operation.pair.right.source ∧
      (∀ source ∈ operation.additional,
        source.placement.sourceDeclaration.toNumberField? =
          some source.source) ∧
      operation.pair.left.placement.targetField =
        operation.pair.right.placement.targetField ∧
      (∀ source ∈ operation.additional,
        operation.pair.left.placement.targetField =
          source.placement.targetField) ∧
      operation.pair.left.placement.targetPolicy.info.scale =
        addressedNumberExtremumResultScale operation.pair
          operation.additional := by
  refine ⟨operation.pair.left.sourceCertified,
    operation.pair.right.sourceCertified, ?_, operation.pair.sameTarget,
    operation.additionalSameTarget, operation.sameScale⟩
  intro source _
  exact source.sourceCertified

end A12Kernel
