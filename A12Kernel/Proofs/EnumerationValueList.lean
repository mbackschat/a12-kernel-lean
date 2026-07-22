import A12Kernel.Semantics.FlatValidation

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

@[simp]
theorem flatEnumerationValueList_canFireOnEmpty
    (quantifier : ValueListQuantifier) (operand : FlatEnumerationOperand)
    (values : List String) :
    (FlatCondition.enumerationValueList quantifier operand values).canFireOnEmpty =
      quantifier.canFireOnEmpty := by
  rfl

/-- The single flat Enumeration leaf remains relevance-gated before either value-list side is consumed. -/
@[simp]
theorem flatEnumerationValueList_irrelevant_unknown
    (quantifier : ValueListQuantifier) (operand : FlatEnumerationOperand)
    (values : List String) (context : FlatContext) :
    (FlatCondition.enumerationValueList quantifier operand values).evalSelected
      context (fun _ => false) = .unknown := by
  simp [FlatCondition.evalSelected]

/-- `No` is the one value-list quantifier structurally eligible on a blank row; the clean empty field makes that fire omission-typed. -/
theorem flatEnumerationValueList_no_empty
    (operand : FlatEnumerationOperand) (values : List String)
    (context : FlatContext)
    (empty : context.observeValidationAt operand.field.id = .empty) :
    (FlatCondition.enumerationValueList .no operand values).evalFull context false =
      .fired .omission := by
  simp [FlatCondition.evalFull, FlatCondition.evalSelected,
    FlatEnumerationOperand.valueListSide, literalTokenValueListSide,
    ValueListQuantifier.eval, evalValueListNo,
    ResolvedValueListSide.hasUnknown, ResolvedValueListSide.anyMatches,
    ResolvedValueListSide.hasMissingPotential, ResolvedValueListSide.hasEmpty,
    ResolvedValueListSide.contains, ValueListQuantifier.canFireOnEmpty,
    ValueListCell.isUnknown, ValueListCell.isEmpty, empty]

end A12Kernel
