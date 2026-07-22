import A12Kernel.Semantics.CheckedEnumeration

/-! # A12Kernel.Proofs.CheckedEnumeration — checked observation laws -/

namespace A12Kernel

@[simp]
theorem checkedEnumeration_empty_is_empty
    (checked : CheckedEnumerationDeclaration) :
    checked.classifyValue (.enum "") = .ok none := by
  simp [CheckedEnumerationDeclaration.classifyValue]

theorem checkedEnumeration_stored_admitted
    (checked : CheckedEnumerationDeclaration) (stored : String)
    (nonempty : stored.isEmpty = false)
    (member : checked.declaration.storedTokens.contains stored = true) :
    checked.classifyValue (.enum stored) = .ok (some (.enum stored)) := by
  have member' : stored ∈ checked.declaration.storedTokens := by simpa using member
  simp [CheckedEnumerationDeclaration.classifyValue, nonempty, member']

theorem checkedEnumeration_stored_rejected
    (checked : CheckedEnumerationDeclaration) (stored : String)
    (nonempty : stored.isEmpty = false)
    (absent : checked.declaration.storedTokens.contains stored = false) :
    checked.classifyValue (.enum stored) = .error .declaredConstraint := by
  have absent' : stored ∉ checked.declaration.storedTokens := by simpa using absent
  simp [CheckedEnumerationDeclaration.classifyValue, nonempty, absent']

/-- A present admitted token reaches the existing resolved evaluator unchanged. -/
theorem checkedEnumeration_evalRaw_present
    (comparison : CheckedEnumerationLiteralComparison) (stored : String)
    (nonempty : stored.isEmpty = false)
    (member : comparison.operand.declaration.declaration.storedTokens.contains stored = true) :
    comparison.evalRaw (.parsed (.enum stored)) =
      comparison.operand.projection.evalLiteral comparison.op
        (.value (.enum stored)) comparison.expected := by
  have member' : stored ∈ comparison.operand.declaration.declaration.storedTokens := by
    simpa using member
  simp [CheckedEnumerationLiteralComparison.evalRaw,
    CheckedEnumerationLiteralComparison.evalCheckedCell,
    CheckedEnumerationDeclaration.checkRaw,
    CheckedEnumerationDeclaration.classifyValue,
    nonempty, member', observeCell]

/-- An out-of-domain stored token stays formal UNKNOWN rather than becoming an ordinary literal mismatch. -/
theorem checkedEnumeration_evalRaw_outOfDomain
    (comparison : CheckedEnumerationLiteralComparison) (stored : String)
    (nonempty : stored.isEmpty = false)
    (absent : comparison.operand.declaration.declaration.storedTokens.contains stored = false) :
    comparison.evalRaw (.parsed (.enum stored)) = .unknown := by
  have absent' : stored ∉ comparison.operand.declaration.declaration.storedTokens := by
    simpa using absent
  simp [CheckedEnumerationLiteralComparison.evalRaw,
    CheckedEnumerationLiteralComparison.evalCheckedCell,
    CheckedEnumerationDeclaration.checkRaw,
    CheckedEnumerationDeclaration.classifyValue,
    nonempty, absent', observeCell,
    ResolvedEnumerationProjection.evalLiteral,
    ResolvedEnumerationProjection.resolveOperand,
    EqualityOp.evalSimple, BaseFormalCause.toFormalCause]

end A12Kernel
