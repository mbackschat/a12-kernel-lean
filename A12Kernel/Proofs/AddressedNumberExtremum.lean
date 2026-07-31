import A12Kernel.Proofs.AddressedNumberField
import A12Kernel.Elaboration.AddressedNumberExtremum

/-! # Same-scope repeatable bounded Number extrema certificate -/

namespace A12Kernel

/-- Every checked extremum retains every ordered Number-kind witness behind its operand-local tag, one target, and the maximum transformed-source/literal operand scale as its exact target scale. -/
theorem checkedAddressedNumberExtremum_sound
    (operation : CheckedAddressedNumberExtremum model) :
    operation.first.numberSource.placement.sourceDeclaration.toNumberField? =
        some operation.first.numberSource.source ∧
      (∀ source ∈ operation.rest,
        source.numberSource.placement.sourceDeclaration.toNumberField? =
          some source.numberSource.source) ∧
      (∀ source ∈ operation.rest,
        operation.first.numberSource.placement.targetField =
          source.numberSource.placement.targetField) ∧
      operation.first.numberSource.placement.targetPolicy.info.scale =
        addressedNumberExtremumOperandResultScale operation.first
          operation.rest operation.literal := by
  refine ⟨operation.first.numberSource.sourceCertified, ?_,
    operation.restSameTarget, operation.sameScale⟩
  intro source _
  exact source.numberSource.sourceCertified

/-- A retained literal insertion point is always within the complete field-backed list, so ordered reconstruction cannot skip a source or create an unowned placement. -/
theorem checkedAddressedNumberExtremum_literalPosition
    (operation : CheckedAddressedNumberExtremum model)
    (positioned : AddressedNumberExtremumLiteral)
    (retained : operation.literal = some positioned) :
    positioned.position ≤ operation.rest.length + 1 := by
  have within := operation.literalWithinSources
  change (match operation.literal with
    | none => True
    | some literal => literal.position ≤ operation.rest.length + 1) at within
  simpa [retained] using within

end A12Kernel
