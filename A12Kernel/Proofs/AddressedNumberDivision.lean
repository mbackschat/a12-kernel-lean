import A12Kernel.Proofs.AddressedNumberField
import A12Kernel.Elaboration.AddressedNumberDivision

/-! # Same-scope repeatable direct-Number division certificate -/

namespace A12Kernel

/-- Every checked division retains two Number-kind witnesses, one target, and the explicit warning suppression required by its unknown static result scale. -/
theorem checkedAddressedNumberDivision_sound
    (operation : CheckedAddressedNumberDivision model) :
    operation.pair.left.placement.sourceDeclaration.toNumberField? =
        some operation.pair.left.source ∧
      operation.pair.right.placement.sourceDeclaration.toNumberField? =
        some operation.pair.right.source ∧
      operation.pair.left.placement.targetField =
        operation.pair.right.placement.targetField ∧
      operation.suppressExactScaleWarning = true := by
  exact ⟨operation.pair.left.sourceCertified,
    operation.pair.right.sourceCertified, operation.pair.sameTarget,
    operation.suppressionCertified⟩

end A12Kernel
