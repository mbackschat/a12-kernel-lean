import A12Kernel.Proofs.AddressedNumberField
import A12Kernel.Elaboration.AddressedNumberExtremum

/-! # Same-scope repeatable bounded Number extrema certificate -/

namespace A12Kernel

namespace CheckedAddressedNumberExtremumFieldOperand

/-- Every field dependency behind one bounded outer operand retains its direct Number witness. -/
theorem sourceCertified
    (operand : CheckedAddressedNumberExtremumFieldOperand model) :
    ∀ source ∈ operand.sources,
      source.placement.sourceDeclaration.toNumberField? = some source.source := by
  cases operand with
  | unary _ source =>
      simp [sources, source.sourceCertified]
  | addition pair =>
      simp [sources, pair.left.sourceCertified, pair.right.sourceCertified]

/-- Both children of an addition operand and the sole child of a unary operand are certified against the operand's one outer target. -/
theorem sourceTargetField
    (operand : CheckedAddressedNumberExtremumFieldOperand model) :
    ∀ source ∈ operand.sources,
      source.placement.targetField = operand.targetField := by
  cases operand with
  | unary _ source =>
      simp [sources, targetField, primarySource]
  | addition pair =>
      simp [sources, targetField, primarySource, pair.sameTarget]

/-- No dependency nested inside one bounded outer operand can name that operand's target. -/
theorem sourceField_ne_targetField
    (operand : CheckedAddressedNumberExtremumFieldOperand model) :
    ∀ field ∈ operand.sourceFields, field ≠ operand.targetField := by
  intro field member
  simp only [sourceFields, List.mem_map] at member
  rcases member with ⟨source, sourceMember, rfl⟩
  intro sourceIsTarget
  apply source.placement.sourceNotTarget
  exact sourceIsTarget.trans
    (operand.sourceTargetField source sourceMember).symm

end CheckedAddressedNumberExtremumFieldOperand

/-- Addition contributes exactly the maximum scale of its two direct Number children. -/
theorem checkedAddressedNumberExtremum_additionResultScale
    (pair : CheckedAddressedNumberPair model) :
    CheckedAddressedNumberExtremumFieldOperand.resultScale (.addition pair) =
      max pair.left.source.info.scale pair.right.source.info.scale := by
  rfl

/-- The outer addition operand delegates row-local ordered reads to the shared Number-pair evaluator and supplies only the existing scalar addition node. -/
theorem checkedAddressedNumberExtremum_additionEvaluation
    (pair : CheckedAddressedNumberPair model)
    (input : CheckedDocument model) (path : List Nat) :
    (CheckedAddressedNumberExtremumOperand.addition pair).evaluateAtPath
        input path =
      pair.evaluateAtPath input
        (NumericComputationResult.combineReached fun left right =>
          .value (NumericArithmeticOp.add.eval left right)) path := by
  rfl

/-- Every checked extremum retains every ordered Number-kind witness behind its operand-local tag, one target, and the maximum transformed-source/literal operand scale as its exact target scale. -/
theorem checkedAddressedNumberExtremum_sound
    (operation : CheckedAddressedNumberExtremum model) :
    (∀ source ∈ operation.first.sources,
        source.placement.sourceDeclaration.toNumberField? = some source.source) ∧
      (∀ operand ∈ operation.rest, ∀ source ∈ operand.sources,
        source.placement.sourceDeclaration.toNumberField? = some source.source) ∧
      (∀ operand ∈ operation.rest,
        operation.first.targetField = operand.targetField) ∧
      operation.first.primarySource.placement.targetPolicy.info.scale =
        addressedNumberExtremumOperandResultScale operation.first
          operation.rest operation.literal := by
  refine ⟨operation.first.sourceCertified, ?_, operation.restSameTarget,
    operation.sameScale⟩
  intro operand _
  exact operand.sourceCertified

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
