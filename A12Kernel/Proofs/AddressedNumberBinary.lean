import A12Kernel.Proofs.AddressedNumberField
import A12Kernel.Elaboration.AddressedNumberBinary

/-! # Same-scope repeatable direct-Number binary arithmetic certificate -/

namespace A12Kernel

/-- Every checked binary operation retains two Number-kind witnesses, one target, its authored operation, and that operation's exact derived scale. -/
theorem checkedAddressedNumberBinary_sound
    (operation : CheckedAddressedNumberBinary model) :
    operation.pair.left.placement.sourceDeclaration.toNumberField? =
        some operation.pair.left.source ∧
      operation.pair.right.placement.sourceDeclaration.toNumberField? =
        some operation.pair.right.source ∧
      operation.pair.left.placement.targetField =
        operation.pair.right.placement.targetField ∧
      operation.pair.left.placement.targetPolicy.info.scale =
        operation.op.directFieldResultScale
          operation.pair.left.source.info.scale
          operation.pair.right.source.info.scale := by
  exact ⟨operation.pair.left.sourceCertified,
    operation.pair.right.sourceCertified, operation.pair.sameTarget,
    operation.sameScale⟩

end A12Kernel
