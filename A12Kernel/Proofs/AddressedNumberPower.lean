import A12Kernel.Proofs.AddressedNumberField
import A12Kernel.Elaboration.AddressedNumberPower

/-! # Same-scope repeatable direct-Number power certificate -/

namespace A12Kernel

/-- Every checked power retains two ordered direct Number witnesses, one target, a scale-0 exponent, and the explicit warning suppression required by its field-derived unknown result scale. -/
theorem checkedAddressedNumberPower_sound
    (operation : CheckedAddressedNumberPower model) :
    operation.pair.left.placement.sourceDeclaration.toNumberField? =
        some operation.pair.left.source ∧
      operation.pair.right.placement.sourceDeclaration.toNumberField? =
        some operation.pair.right.source ∧
      operation.pair.left.placement.targetField =
        operation.pair.right.placement.targetField ∧
      operation.pair.right.source.info.scale = 0 ∧
      operation.suppressExactScaleWarning = true := by
  exact ⟨operation.pair.left.sourceCertified,
    operation.pair.right.sourceCertified, operation.pair.sameTarget,
    operation.exponentScaleZero, operation.suppressionCertified⟩

end A12Kernel
