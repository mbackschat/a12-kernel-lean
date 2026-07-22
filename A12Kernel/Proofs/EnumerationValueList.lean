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
theorem flatTokenValueList_canFireOnEmpty
    (quantifier : ValueListQuantifier) (operands : List FlatTextFieldOperand)
    (values : FlatTokenValueSide) :
    (FlatCondition.tokenValueList quantifier operands values).canFireOnEmpty =
      quantifier.canFireOnEmpty := by
  rfl

@[simp]
theorem flatTokenValueListSide_cells
    (operands : List FlatTextFieldOperand) (context : FlatContext) :
    (flatTokenValueListSide operands context).cells =
      operands.map (·.valueListCell context) := by
  rfl

@[simp]
theorem flatTokenValueSide_fields
    (operands : List FlatTextFieldOperand) (context : FlatContext) :
    (FlatTokenValueSide.fields operands).resolve context =
      flatTokenValueListSide operands context := by
  rfl

/-- The single flat Enumeration leaf remains relevance-gated before either value-list side is consumed. -/
@[simp]
theorem flatTokenValueList_irrelevant_unknown
    (quantifier : ValueListQuantifier) (operand : FlatTextFieldOperand)
    (remaining : List FlatTextFieldOperand)
    (values : FlatTokenValueSide) (context : FlatContext) :
    (FlatCondition.tokenValueList quantifier (operand :: remaining) values).evalSelected
      context (fun _ => false) = .unknown := by
  simp [FlatCondition.evalSelected, FlatTokenValueSide.allOperands]

/-- Scalar membership is a one-field `AtLeastOne`/`NotAll` specialization: an empty subject makes either surface operator non-firing. -/
theorem flatTokenValueMembership_empty
    (op : ValueListMembershipOp) (operand : FlatTextFieldOperand)
    (values : List String) (context : FlatContext)
    (empty : operand.valueListCell context = .empty) :
    (FlatCondition.tokenValueList op.quantifier [operand] (.literals values)).evalFull
      context true = .notFired := by
  cases op <;>
    simp [ValueListMembershipOp.quantifier, FlatCondition.evalFull,
      FlatCondition.evalSelected, FlatTokenValueSide.allOperands,
      FlatTokenValueSide.operands, FlatTokenValueSide.resolve,
      flatTokenValueListSide, literalTokenValueListSide,
      ValueListQuantifier.eval, evalValueListAtLeastOne,
      evalValueListNotAll, ResolvedValueListSide.anyMatches,
      ResolvedValueListSide.hasPresent, empty]

/-- `No` is the one value-list quantifier structurally eligible on a blank row; the clean empty field makes that fire omission-typed. -/
theorem flatEnumerationValueList_no_empty
    (operand : FlatEnumerationOperand) (values : List String)
    (context : FlatContext)
    (empty : context.observeValidationAt operand.field.id = .empty) :
    (FlatCondition.tokenValueList .no [.enumeration operand] (.literals values)).evalFull context false =
      .fired .omission := by
  simp [FlatCondition.evalFull, FlatCondition.evalSelected,
    FlatTokenValueSide.allOperands, FlatTokenValueSide.operands,
    FlatTokenValueSide.resolve, flatTokenValueListSide,
    FlatTextFieldOperand.valueListCell, FlatTextFieldOperand.resolve,
    FlatEnumerationOperand.resolve, SimpleComparisonOperand.asTokenValueListCell,
    ResolvedEnumerationProjection.resolveOperand,
    literalTokenValueListSide,
    ValueListQuantifier.eval, evalValueListNo,
    ResolvedValueListSide.hasUnknown, ResolvedValueListSide.anyMatches,
    ResolvedValueListSide.hasMissingPotential, ResolvedValueListSide.hasEmpty,
    ResolvedValueListSide.contains, ValueListQuantifier.canFireOnEmpty,
    ValueListCell.isUnknown, ValueListCell.isEmpty, empty]

/-- Both scalar membership operators remain ineligible on an empty subject; NotIncluded deliberately specializes `NotAll`, not empty-firing `No`. -/
theorem flatEnumerationValueMembership_empty
    (op : ValueListMembershipOp) (operand : FlatEnumerationOperand)
    (values : List String) (context : FlatContext)
    (empty : context.observeValidationAt operand.field.id = .empty) :
    (FlatCondition.tokenValueList op.quantifier [.enumeration operand] (.literals values)).evalFull
      context true = .notFired := by
  apply flatTokenValueMembership_empty
  simp [FlatTextFieldOperand.valueListCell, FlatTextFieldOperand.resolve,
    FlatEnumerationOperand.resolve, SimpleComparisonOperand.asTokenValueListCell,
    ResolvedEnumerationProjection.resolveOperand, empty]

end A12Kernel
