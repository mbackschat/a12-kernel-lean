import A12Kernel.Proofs.AddressedNumberField
import A12Kernel.Elaboration.AddressedNumberExtremum

/-! # Repeatable bounded Number extrema certificate -/

namespace A12Kernel

/-- Every dependency an arithmetic child actually reads retains its direct Number witness, whichever inner positions its literals occupy. A constant-only child reads nothing, so the claim is vacuous there. -/
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
  | literals _ _ => simp [CheckedAddressedNumberArithmeticChild.sources]

/-- Every field-backed nested leaf retains its direct Number witness; literal leaves contribute no dependency. -/
theorem checkedAddressedNumberExtremumLeaf_sourceCertified
    (leaf : CheckedAddressedNumberExtremumLeaf model) :
    ∀ source ∈ leaf.sources,
      source.placement.sourceDeclaration.toNumberField? = some source.source := by
  cases leaf with
  | field source =>
      simp [CheckedAddressedNumberExtremumLeaf.sources, source.sourceCertified]
  | literal _ => simp [CheckedAddressedNumberExtremumLeaf.sources]

/-- Every dependency retained by a nested extremum keeps its direct Number witness. -/
theorem checkedAddressedNumberNestedExtremum_sourceCertified
    (operation : CheckedAddressedNumberNestedExtremum model) :
    ∀ source ∈ operation.sources,
      source.placement.sourceDeclaration.toNumberField? = some source.source := by
  intro source member
  simp only [CheckedAddressedNumberNestedExtremum.sources,
    CheckedAddressedNumberNestedExtremum.orderedOperands,
    List.mem_flatMap] at member
  rcases member with ⟨leaf, _, sourceMember⟩
  exact checkedAddressedNumberExtremumLeaf_sourceCertified leaf source sourceMember

/-- Every dependency behind one retained operand keeps its direct Number witness. Literal and constant-only operands contribute none. -/
theorem checkedAddressedNumberExtremumOperand_sourceCertified
    (operand : CheckedAddressedNumberExtremumOperand model) :
    ∀ source ∈ operand.sources,
      source.placement.sourceDeclaration.toNumberField? = some source.source := by
  cases operand with
  | field source | abs source =>
      simp [CheckedAddressedNumberExtremumOperand.sources, source.sourceCertified]
  | round source _ _ =>
      simp [CheckedAddressedNumberExtremumOperand.sources, source.sourceCertified]
  | arithmetic _ child =>
      simpa [CheckedAddressedNumberExtremumOperand.sources] using
        checkedAddressedNumberArithmeticChild_sourceCertified child
  | extremum operation =>
      simpa [CheckedAddressedNumberExtremumOperand.sources] using
        checkedAddressedNumberNestedExtremum_sourceCertified operation
  | literal _ => simp [CheckedAddressedNumberExtremumOperand.sources]

/-- A nested extremum contributes its own ordered leaf-scale union without flattening those leaves into the parent call. -/
theorem checkedAddressedNumberExtremum_nestedScaleSummary
    (operation : CheckedAddressedNumberNestedExtremum model) :
    CheckedAddressedNumberExtremumOperand.scaleSummary
        (.extremum operation) = operation.scaleSummary := by
  rfl

/-- A nested extremum operand delegates row-local selection to the nested call while preserving its selector and authored leaf order. -/
theorem checkedAddressedNumberExtremum_nestedEvaluation
    (operation : CheckedAddressedNumberNestedExtremum model)
    (input : CheckedDocument model) (environment : Env) :
    (CheckedAddressedNumberExtremumOperand.extremum
        operation).evaluateAtEnvironment input environment =
      operation.evaluateAtEnvironment input environment := by
  rfl

/-- Every bounded arithmetic node contributes exactly its child's shared scale summary. The operation, not the extremum, owns whether the scale is the maximum or the sum and whether multiplicative-constant capability survives. -/
theorem checkedAddressedNumberExtremum_arithmeticScaleSummary
    (operation : NumericArithmeticOp)
    (child : CheckedAddressedNumberArithmeticChild model) :
    CheckedAddressedNumberExtremumOperand.scaleSummary
        (.arithmetic operation child) =
      child.scaleSummary operation := by
  rfl

/-- Every bounded arithmetic node delegates row-local ordered reads to its child and supplies only its existing scalar node. -/
theorem checkedAddressedNumberExtremum_arithmeticEvaluation
    (operation : NumericArithmeticOp)
    (child : CheckedAddressedNumberArithmeticChild model)
    (input : CheckedDocument model) (environment : Env) :
    (CheckedAddressedNumberExtremumOperand.arithmetic operation
        child).evaluateAtEnvironment input environment =
      child.evaluateAtEnvironment operation input environment := by
  rfl

/-- Addition over two fields contributes the maximum child scale. -/
theorem checkedAddressedNumberExtremum_additionScaleSummary
    (pair : CheckedAddressedNumberPair model) :
    CheckedAddressedNumberExtremumOperand.scaleSummary
        (.arithmetic .add (.fields pair)) =
      NumericScaleSummary.binary .add (.field pair.left.source.info.scale)
        (.field pair.right.source.info.scale) :=
  checkedAddressedNumberExtremum_arithmeticScaleSummary .add (.fields pair)

/-- Subtraction over two fields contributes the maximum child scale. -/
theorem checkedAddressedNumberExtremum_subtractionScaleSummary
    (pair : CheckedAddressedNumberPair model) :
    CheckedAddressedNumberExtremumOperand.scaleSummary
        (.arithmetic .subtract (.fields pair)) =
      NumericScaleSummary.binary .subtract (.field pair.left.source.info.scale)
        (.field pair.right.source.info.scale) :=
  checkedAddressedNumberExtremum_arithmeticScaleSummary .subtract (.fields pair)

/-- Multiplication over two fields instead SUMS their scales, and with no capable operand the product stays incapable of expansion. -/
theorem checkedAddressedNumberExtremum_multiplicationScaleSummary
    (pair : CheckedAddressedNumberPair model) :
    CheckedAddressedNumberExtremumOperand.scaleSummary
        (.arithmetic .multiply (.fields pair)) =
      { scale := .exact (pair.left.source.info.scale +
          pair.right.source.info.scale), canExpandScale := false } :=
  checkedAddressedNumberExtremum_arithmeticScaleSummary .multiply (.fields pair)

/-- A child literal contributes its AUTHORED scale at its authored position, so the same value written with a trailing zero legally changes the admitted target scale. -/
theorem checkedAddressedNumberExtremum_fieldLiteralScaleSummary
    (operation : NumericArithmeticOp)
    (source : CheckedAddressedNumberSource model)
    (decoded : DecodedNumericLiteral) :
    CheckedAddressedNumberExtremumOperand.scaleSummary
        (.arithmetic operation (.fieldLiteral source decoded)) =
      NumericScaleSummary.binary operation.scaleBinaryOp
        (.field source.source.info.scale)
        (NumericScaleSummary.constant decoded.authoredScale) :=
  checkedAddressedNumberExtremum_arithmeticScaleSummary operation
    (.fieldLiteral source decoded)

/-- The mirrored inner position keeps the operand summaries in authored order. -/
theorem checkedAddressedNumberExtremum_literalFieldScaleSummary
    (operation : NumericArithmeticOp)
    (decoded : DecodedNumericLiteral)
    (source : CheckedAddressedNumberSource model) :
    CheckedAddressedNumberExtremumOperand.scaleSummary
        (.arithmetic operation (.literalField decoded source)) =
      NumericScaleSummary.binary operation.scaleBinaryOp
        (NumericScaleSummary.constant decoded.authoredScale)
        (.field source.source.info.scale) :=
  checkedAddressedNumberExtremum_arithmeticScaleSummary operation
    (.literalField decoded source)

/-- A literal-bearing product adds the literal's authored signed scale to its field's scale and RETAINS multiplicative-constant capability, which is what lets an all-capable list be padded up to a larger declared target scale. -/
theorem checkedAddressedNumberExtremum_multiplicationLiteralScaleSummary
    (source : CheckedAddressedNumberSource model)
    (decoded : DecodedNumericLiteral) :
    CheckedAddressedNumberExtremumOperand.scaleSummary
        (.arithmetic .multiply (.fieldLiteral source decoded)) =
      { scale := .exact (source.source.info.scale + decoded.authoredScale)
        canExpandScale := true } :=
  checkedAddressedNumberExtremum_fieldLiteralScaleSummary .multiply source decoded

/-- A constant-only child reads no field and stays capability-carrying under every admitted operation, which is why a list built only from such operands is admitted at any declared scale at or above its derived one. -/
theorem checkedAddressedNumberExtremum_constantOnlyCapable
    (operation : NumericArithmeticOp)
    (left right : DecodedNumericLiteral) :
    (CheckedAddressedNumberExtremumOperand.scaleSummary (model := model)
        (.arithmetic operation (.literals left right))).canExpandScale = true := by
  cases operation <;> rfl

/-- No field dependency anywhere in a checked call names that call's own written target. -/
theorem checkedAddressedNumberExtremum_sourceField_ne_targetField
    (operation : CheckedAddressedNumberExtremum model) :
    ∀ field ∈ operation.sourceFields, field ≠ operation.target.targetField := by
  intro field member
  simp only [CheckedAddressedNumberExtremum.sourceFields,
    CheckedAddressedNumberExtremum.orderedOperands, List.mem_flatMap,
    CheckedAddressedNumberExtremumOperand.sourceFields, List.mem_map] at member
  rcases member with ⟨operand, operandMember, source, sourceMember, rfl⟩
  intro sourceIsTarget
  apply source.placement.sourceNotTarget
  have shared := operation.sourcesShareTarget source (by
    simp only [List.mem_flatMap]
    exact ⟨operand, operandMember, sourceMember⟩)
  exact sourceIsTarget.trans shared.symm

/-- Every checked extremum retains every ordered Number-kind witness, certifies every dependency against its one target, and declares a target scale admitted by the shared comparison predicate over its derived summary. -/
theorem checkedAddressedNumberExtremum_sound
    (operation : CheckedAddressedNumberExtremum model) :
    (∀ operand ∈ operation.orderedOperands, ∀ source ∈ operand.sources,
        source.placement.sourceDeclaration.toNumberField? = some source.source) ∧
      (∀ source ∈ operation.orderedOperands.flatMap
          CheckedAddressedNumberExtremumOperand.sources,
        source.placement.targetField = operation.target.targetField) ∧
      exactNumericScaleComparisonAllowedWithSuppression false
        (NumericScaleSummary.field operation.target.targetPolicy.info.scale)
        operation.scaleSummary = true := by
  refine ⟨?_, operation.sourcesShareTarget, operation.targetAdmitted⟩
  intro operand _
  exact checkedAddressedNumberExtremumOperand_sourceCertified operand

end A12Kernel
