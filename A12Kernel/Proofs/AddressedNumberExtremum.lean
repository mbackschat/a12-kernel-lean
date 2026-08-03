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
  | additive _ pair =>
      simp [sources, pair.left.sourceCertified, pair.right.sourceCertified]

/-- Both children of an additive operand and the sole child of a unary operand are certified against the operand's one outer target. -/
theorem sourceTargetField
    (operand : CheckedAddressedNumberExtremumFieldOperand model) :
    ∀ source ∈ operand.sources,
      source.placement.targetField = operand.targetField := by
  cases operand with
  | unary _ source =>
      simp [sources, targetField, primarySource]
  | additive _ pair =>
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

/-- Every bounded additive node contributes exactly the maximum scale of its two direct Number children. -/
theorem checkedAddressedNumberExtremum_additiveResultScale
    (operation : AddressedNumberExtremumAdditiveOperation)
    (pair : CheckedAddressedNumberPair model) :
    CheckedAddressedNumberExtremumFieldOperand.resultScale
        (.additive operation pair) =
      max pair.left.source.info.scale pair.right.source.info.scale := by
  rfl

/-- Every bounded additive node delegates row-local ordered reads to the shared Number-pair evaluator and supplies only its existing scalar node. -/
theorem checkedAddressedNumberExtremum_additiveEvaluation
    (operation : AddressedNumberExtremumAdditiveOperation)
    (pair : CheckedAddressedNumberPair model)
    (input : CheckedDocument model) (path : List Nat) :
    (CheckedAddressedNumberExtremumOperand.additive operation pair).evaluateAtPath
        input path =
      pair.evaluateAtPath input
        (NumericComputationResult.combineReached fun left right =>
          .value (operation.arithmetic.eval left right)) path := by
  rfl

/-- Addition is the additive scale law specialized to the addition tag. -/
theorem checkedAddressedNumberExtremum_additionResultScale
    (pair : CheckedAddressedNumberPair model) :
    CheckedAddressedNumberExtremumFieldOperand.resultScale
        (.additive .add pair) =
      max pair.left.source.info.scale pair.right.source.info.scale := by
  exact checkedAddressedNumberExtremum_additiveResultScale .add pair

/-- Subtraction is the additive scale law specialized to the subtraction tag. -/
theorem checkedAddressedNumberExtremum_subtractionResultScale
    (pair : CheckedAddressedNumberPair model) :
    CheckedAddressedNumberExtremumFieldOperand.resultScale
        (.additive .subtract pair) =
      max pair.left.source.info.scale pair.right.source.info.scale := by
  exact checkedAddressedNumberExtremum_additiveResultScale .subtract pair

/-- Addition is the shared ordered-pair delegation law specialized to the scalar addition node. -/
theorem checkedAddressedNumberExtremum_additionEvaluation
    (pair : CheckedAddressedNumberPair model)
    (input : CheckedDocument model) (path : List Nat) :
    (CheckedAddressedNumberExtremumOperand.additive .add pair).evaluateAtPath
        input path =
      pair.evaluateAtPath input
        (NumericComputationResult.combineReached fun left right =>
          .value (NumericArithmeticOp.add.eval left right)) path := by
  exact checkedAddressedNumberExtremum_additiveEvaluation .add pair input path

/-- Subtraction is the shared ordered-pair delegation law specialized to the scalar subtraction node. -/
theorem checkedAddressedNumberExtremum_subtractionEvaluation
    (pair : CheckedAddressedNumberPair model)
    (input : CheckedDocument model) (path : List Nat) :
    (CheckedAddressedNumberExtremumOperand.additive .subtract pair).evaluateAtPath
        input path =
      pair.evaluateAtPath input
        (NumericComputationResult.combineReached fun left right =>
          .value (NumericArithmeticOp.subtract.eval left right)) path := by
  exact checkedAddressedNumberExtremum_additiveEvaluation .subtract pair input path

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
