import A12Kernel.Semantics.EnumerationRepetitionNotUnique

/-! # A12Kernel.Proofs.EnumerationRepetitionNotUnique — checked key laws -/

namespace A12Kernel

@[simp]
theorem enumerationRepetitionKey_empty
    (projection : ResolvedEnumerationProjection) :
    projection.asRepetitionKeyComponent .empty = .empty := by
  rfl

@[simp]
theorem enumerationRepetitionKey_unknown
    (projection : ResolvedEnumerationProjection) (cause : FormalCause) :
    projection.asRepetitionKeyComponent (.unknown cause) = .unknown cause := by
  rfl

theorem enumerationRepetitionKey_present
    (projection : ResolvedEnumerationProjection)
    (stored projected : String)
    (resolved : projection.tokenFor? stored = some projected) :
    projection.asRepetitionKeyComponent (.value (.enum stored)) =
      .present (.token projected) := by
  simp [ResolvedEnumerationProjection.asRepetitionKeyComponent,
    ResolvedEnumerationProjection.resolveOperand, resolved]

/-- Any two stored tokens with the same resolved category token become the same RNU component. -/
theorem enumerationRepetitionKey_sameProjectedToken
    (projection : ResolvedEnumerationProjection)
    (left right projected : String)
    (leftResolved : projection.tokenFor? left = some projected)
    (rightResolved : projection.tokenFor? right = some projected) :
    projection.asRepetitionKeyComponent (.value (.enum left)) =
      projection.asRepetitionKeyComponent (.value (.enum right)) := by
  rw [enumerationRepetitionKey_present projection left projected leftResolved,
    enumerationRepetitionKey_present projection right projected rightResolved]

/-- An invalid stored token retains the declaration failure cause and therefore cannot enter a duplicate cluster. -/
theorem checkedEnumerationRepetitionKey_outOfDomain
    (operand : CheckedEnumerationProjection) (stored : String)
    (nonempty : stored.isEmpty = false)
    (absent : operand.declaration.declaration.storedTokens.contains stored = false) :
    operand.classifyRawKey (.parsed (.enum stored)) = .unknown .declaredConstraint := by
  have absent' : stored ∉ operand.declaration.declaration.storedTokens := by
    simpa using absent
  simp [CheckedEnumerationProjection.classifyRawKey,
    CheckedEnumerationProjection.classifyCheckedKeyAt,
    CheckedEnumerationDeclaration.checkRaw,
    CheckedEnumerationDeclaration.classifyValue,
    ResolvedEnumerationProjection.asRepetitionKeyComponent,
    ResolvedEnumerationProjection.resolveOperand,
    nonempty, absent', observeCell, BaseFormalCause.toFormalCause]

end A12Kernel
