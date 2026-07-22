import A12Kernel.Semantics.EnumerationValueList

/-! # A12Kernel.Proofs.EnumerationValueList — checked token-side laws -/

namespace A12Kernel

@[simp]
theorem enumerationValueList_empty
    (projection : ResolvedEnumerationProjection) :
    projection.asValueListCell .empty = .empty := by
  rfl

@[simp]
theorem enumerationValueList_unknown
    (projection : ResolvedEnumerationProjection) (cause : FormalCause) :
    projection.asValueListCell (.unknown cause) = .unknown cause := by
  rfl

theorem enumerationValueList_present
    (projection : ResolvedEnumerationProjection)
    (stored projected : String)
    (resolved : projection.tokenFor? stored = some projected) :
    projection.asValueListCell (.value (.enum stored)) = .present projected := by
  simp [ResolvedEnumerationProjection.asValueListCell,
    ResolvedEnumerationProjection.resolveOperand,
    resolved]

/-- An invalid stored token retains the declaration failure cause in the value-list cell. -/
theorem checkedEnumerationValueList_outOfDomain
    (operand : CheckedEnumerationValueListOperand) (stored : String)
    (nonempty : stored.isEmpty = false)
    (absent : operand.declaration.declaration.storedTokens.contains stored = false) :
    operand.classifyRaw (.parsed (.enum stored)) = .unknown .declaredConstraint := by
  have absent' : stored ∉ operand.declaration.declaration.storedTokens := by
    simpa using absent
  simp [CheckedEnumerationValueListOperand.classifyRaw,
    CheckedEnumerationDeclaration.checkRaw,
    CheckedEnumerationDeclaration.classifyValue,
    ResolvedEnumerationProjection.asValueListCell,
    ResolvedEnumerationProjection.resolveOperand,
    nonempty, absent', observeCell, BaseFormalCause.toFormalCause]

@[simp]
theorem checkedEnumerationValueList_sideCells
    (operand : CheckedEnumerationValueListOperand) (rawCells : List RawCell)
    (hasUninstantiatedTail hasHaving : Bool) :
    (operand.classifyRawSide rawCells hasUninstantiatedTail hasHaving).cells =
      rawCells.map operand.classifyRaw := by
  rfl

end A12Kernel
