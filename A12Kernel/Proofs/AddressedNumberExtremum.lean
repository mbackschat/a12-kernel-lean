import A12Kernel.Proofs.AddressedNumberField
import A12Kernel.Elaboration.AddressedNumberExtremum

/-! # Same-scope repeatable direct-Number extrema certificate -/

namespace A12Kernel

/-- Every checked extremum retains two Number-kind witnesses, one target, and the maximum operand scale as its exact target scale. -/
theorem checkedAddressedNumberExtremum_sound
    (operation : CheckedAddressedNumberExtremum model) :
    operation.left.placement.sourceDeclaration.toNumberField? =
        some operation.left.source ∧
      operation.right.placement.sourceDeclaration.toNumberField? =
        some operation.right.source ∧
      operation.left.placement.targetField =
        operation.right.placement.targetField ∧
      operation.left.placement.targetPolicy.info.scale =
        max operation.left.source.info.scale operation.right.source.info.scale := by
  exact ⟨operation.left.sourceCertified, operation.right.sourceCertified,
    operation.sameTarget, operation.sameScale⟩

end A12Kernel
