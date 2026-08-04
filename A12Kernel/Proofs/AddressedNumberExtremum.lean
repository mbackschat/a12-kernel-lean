import A12Kernel.Proofs.AddressedNumberField
import A12Kernel.Elaboration.AddressedNumberExtremum

/-! # Same-scope repeatable bounded Number extrema certificate -/

namespace A12Kernel

/-- Every dependency an arithmetic child actually reads retains its direct Number witness, whichever inner position a literal occupies. -/
theorem checkedAddressedNumberArithmeticChild_sourceCertified
    (child : CheckedAddressedNumberArithmeticChild model) :
    ∀ source ∈ child.sources,
      source.placement.sourceDeclaration.toNumberField? = some source.source := by
  cases child with
  | fields pair =>
      simp [CheckedAddressedNumberArithmeticChild.sources,
        pair.left.sourceCertified, pair.right.sourceCertified]
  | fieldLiteral source _ =>
      simp [CheckedAddressedNumberArithmeticChild.sources, source.sourceCertified]
  | literalField _ source =>
      simp [CheckedAddressedNumberArithmeticChild.sources, source.sourceCertified]

/-- Every retained dependency is certified against the one primary source's target, so a literal side cannot introduce a second target. -/
theorem checkedAddressedNumberArithmeticChild_sourceTargetField
    (child : CheckedAddressedNumberArithmeticChild model) :
    ∀ source ∈ child.sources,
      source.placement.targetField =
        child.primarySource.placement.targetField := by
  cases child with
  | fields pair =>
      simp [CheckedAddressedNumberArithmeticChild.sources,
        CheckedAddressedNumberArithmeticChild.primarySource, pair.sameTarget]
  | fieldLiteral source _ =>
      simp [CheckedAddressedNumberArithmeticChild.sources,
        CheckedAddressedNumberArithmeticChild.primarySource]
  | literalField _ source =>
      simp [CheckedAddressedNumberArithmeticChild.sources,
        CheckedAddressedNumberArithmeticChild.primarySource]

namespace CheckedAddressedNumberExtremumFieldOperand

/-- Every field dependency behind one bounded outer operand retains its direct Number witness. -/
theorem sourceCertified
    (operand : CheckedAddressedNumberExtremumFieldOperand model) :
    ∀ source ∈ operand.sources,
      source.placement.sourceDeclaration.toNumberField? = some source.source := by
  cases operand with
  | unary _ source =>
      simp [sources, source.sourceCertified]
  | arithmetic _ child =>
      simpa [sources] using
        checkedAddressedNumberArithmeticChild_sourceCertified child

/-- Both children of an arithmetic operand and the sole child of a unary operand are certified against the operand's one outer target. -/
theorem sourceTargetField
    (operand : CheckedAddressedNumberExtremumFieldOperand model) :
    ∀ source ∈ operand.sources,
      source.placement.targetField = operand.targetField := by
  cases operand with
  | unary _ source =>
      simp [sources, targetField, primarySource]
  | arithmetic _ child =>
      simpa [sources, targetField, primarySource] using
        checkedAddressedNumberArithmeticChild_sourceTargetField child

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

/-- Every bounded arithmetic node contributes exactly the shared direct-field result scale of its operation over its two Number children. The operation, not the extremum, owns whether that is the maximum or the sum. -/
theorem checkedAddressedNumberExtremum_arithmeticResultScale
    (operation : NumericArithmeticOp)
    (child : CheckedAddressedNumberArithmeticChild model) :
    CheckedAddressedNumberExtremumFieldOperand.resultScale
        (.arithmetic operation child) =
      operation.directFieldResultScale child.operandScales.1
        child.operandScales.2 := by
  rfl

/-- Every bounded arithmetic node delegates row-local ordered reads to the shared Number-pair evaluator and supplies only its existing scalar node. -/
theorem checkedAddressedNumberExtremum_arithmeticEvaluation
    (operation : NumericArithmeticOp)
    (child : CheckedAddressedNumberArithmeticChild model)
    (input : CheckedDocument model) (path : List Nat) :
    (CheckedAddressedNumberExtremumOperand.arithmetic operation
        child).evaluateAtPath input path =
      child.evaluateAtPath operation input path := by
  rfl

/-- Addition contributes the maximum child scale: the shared law specialized to the addition node. -/
theorem checkedAddressedNumberExtremum_additionResultScale
    (pair : CheckedAddressedNumberPair model) :
    CheckedAddressedNumberExtremumFieldOperand.resultScale
        (.arithmetic .add (.fields pair)) =
      max pair.left.source.info.scale pair.right.source.info.scale :=
  checkedAddressedNumberExtremum_arithmeticResultScale .add (.fields pair)

/-- Subtraction contributes the maximum child scale: the shared law specialized to the subtraction node. -/
theorem checkedAddressedNumberExtremum_subtractionResultScale
    (pair : CheckedAddressedNumberPair model) :
    CheckedAddressedNumberExtremumFieldOperand.resultScale
        (.arithmetic .subtract (.fields pair)) =
      max pair.left.source.info.scale pair.right.source.info.scale :=
  checkedAddressedNumberExtremum_arithmeticResultScale .subtract (.fields pair)

/-- Multiplication instead contributes the SUM of its child scales, which is why it cannot ride the additive nodes' maximum contract. -/
theorem checkedAddressedNumberExtremum_multiplicationResultScale
    (pair : CheckedAddressedNumberPair model) :
    CheckedAddressedNumberExtremumFieldOperand.resultScale
        (.arithmetic .multiply (.fields pair)) =
      pair.left.source.info.scale + pair.right.source.info.scale :=
  checkedAddressedNumberExtremum_arithmeticResultScale .multiply (.fields pair)

/-- Addition is the shared ordered-pair delegation law specialized to the scalar addition node. -/
theorem checkedAddressedNumberExtremum_additionEvaluation
    (pair : CheckedAddressedNumberPair model)
    (input : CheckedDocument model) (path : List Nat) :
    (CheckedAddressedNumberExtremumOperand.arithmetic .add (.fields pair)).evaluateAtPath
        input path =
      (CheckedAddressedNumberArithmeticChild.fields pair).evaluateAtPath
        .add input path :=
  checkedAddressedNumberExtremum_arithmeticEvaluation .add (.fields pair) input path

/-- Subtraction is the shared ordered-pair delegation law specialized to the scalar subtraction node. -/
theorem checkedAddressedNumberExtremum_subtractionEvaluation
    (pair : CheckedAddressedNumberPair model)
    (input : CheckedDocument model) (path : List Nat) :
    (CheckedAddressedNumberExtremumOperand.arithmetic .subtract
        (.fields pair)).evaluateAtPath input path =
      (CheckedAddressedNumberArithmeticChild.fields pair).evaluateAtPath
        .subtract input path :=
  checkedAddressedNumberExtremum_arithmeticEvaluation .subtract (.fields pair) input path

/-- Multiplication is the same delegation law specialized to the scalar multiplication node; only the derived scale above distinguishes it. -/
theorem checkedAddressedNumberExtremum_multiplicationEvaluation
    (pair : CheckedAddressedNumberPair model)
    (input : CheckedDocument model) (path : List Nat) :
    (CheckedAddressedNumberExtremumOperand.arithmetic .multiply
        (.fields pair)).evaluateAtPath input path =
      (CheckedAddressedNumberArithmeticChild.fields pair).evaluateAtPath
        .multiply input path :=
  checkedAddressedNumberExtremum_arithmeticEvaluation .multiply (.fields pair) input path

/-- A child literal contributes its AUTHORED scale at its authored position, so the same value written with a trailing zero legally changes the target scale. -/
theorem checkedAddressedNumberExtremum_fieldLiteralResultScale
    (operation : NumericArithmeticOp)
    (source : CheckedAddressedNumberSource model)
    (decoded : DecodedNumericLiteral) :
    CheckedAddressedNumberExtremumFieldOperand.resultScale
        (.arithmetic operation (.fieldLiteral source decoded)) =
      operation.directFieldResultScale source.source.info.scale
        decoded.authoredScale.toNat :=
  checkedAddressedNumberExtremum_arithmeticResultScale operation
    (.fieldLiteral source decoded)

/-- The mirrored inner position keeps the operand scales in authored order. -/
theorem checkedAddressedNumberExtremum_literalFieldResultScale
    (operation : NumericArithmeticOp)
    (decoded : DecodedNumericLiteral)
    (source : CheckedAddressedNumberSource model) :
    CheckedAddressedNumberExtremumFieldOperand.resultScale
        (.arithmetic operation (.literalField decoded source)) =
      operation.directFieldResultScale decoded.authoredScale.toNat
        source.source.info.scale :=
  checkedAddressedNumberExtremum_arithmeticResultScale operation
    (.literalField decoded source)

/-- A literal-bearing product adds the literal's authored scale to its field's scale; this is the exact contract the real kernel gate measures. -/
theorem checkedAddressedNumberExtremum_multiplicationLiteralResultScale
    (source : CheckedAddressedNumberSource model)
    (decoded : DecodedNumericLiteral) :
    CheckedAddressedNumberExtremumFieldOperand.resultScale
        (.arithmetic .multiply (.fieldLiteral source decoded)) =
      source.source.info.scale + decoded.authoredScale.toNat :=
  checkedAddressedNumberExtremum_fieldLiteralResultScale .multiply source decoded

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
