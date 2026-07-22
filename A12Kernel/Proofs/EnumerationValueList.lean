import A12Kernel.Semantics.FlatValidation

/-! # A12Kernel.Proofs.EnumerationValueList — checked token-side laws -/

namespace A12Kernel

private theorem filter_const_true (items : List α) :
    items.filter (fun _ => true) = items := by
  apply List.filter_eq_self.mpr
  simp

private theorem filter_const_false (items : List α) :
    items.filter (fun _ => false) = [] := by
  induction items <;> simp [*]

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

/-- Full relevance constructs exactly the ordinary resolved token side. -/
@[simp]
theorem selectedFlatTokenValueListSide_full
    (operands : List FlatTextFieldOperand) (context : FlatContext) :
    selectedFlatTokenValueListSide operands context (fun _ => true) =
      .ofResolved (flatTokenValueListSide operands context) := by
  simp [selectedFlatTokenValueListSide,
    ResolvedValueListQuantifierSide.ofResolved, filter_const_true]

/-- Full relevance constructs exactly the ordinary resolved token values side. -/
@[simp]
theorem flatTokenValueSide_resolveSelected_full
    (values : FlatTokenValueSide) (context : FlatContext) :
    values.resolveSelected context (fun _ => true) =
      .ofResolved (values.resolve context) := by
  cases values with
  | literals values => rfl
  | fields operands => exact selectedFlatTokenValueListSide_full operands context

/-- With every token operand masked, the quantifiers retain their distinct per-cell relevance rules: only `No` becomes UNKNOWN. -/
@[simp]
theorem flatTokenValueList_allIrrelevant
    (quantifier : ValueListQuantifier) (operand : FlatTextFieldOperand)
    (remaining : List FlatTextFieldOperand)
    (values : FlatTokenValueSide) (context : FlatContext) :
    (FlatCondition.tokenValueList quantifier (operand :: remaining) values).evalSelected
      context (fun _ => false) =
        match quantifier with
        | .atLeastOne => .notFired
        | .no => .unknown
        | .notAll => .notFired := by
  cases quantifier <;> cases values <;>
    simp [FlatCondition.evalSelected, selectedFlatTokenValueListSide,
      FlatTokenValueSide.resolveSelected, ValueListQuantifier.evalClassified,
      evalClassifiedValueListAtLeastOne, evalClassifiedValueListNo,
      evalClassifiedValueListNotAll, ResolvedValueListQuantifierSide.hasUnknown,
      ResolvedValueListQuantifierSide.hasPresent,
      ResolvedValueListQuantifierSide.anyMatches, flatTokenValueListSide,
      literalTokenValueListSide, ResolvedValueListSide.hasUnknown,
      ResolvedValueListSide.hasPresent, ResolvedValueListSide.anyMatches,
      ResolvedValueListSide.contains, filter_const_false]

/-- Scalar membership is a one-field `AtLeastOne`/`NotAll` specialization: an empty subject makes either surface operator non-firing. -/
theorem flatTokenValueMembership_empty
    (op : ValueListMembershipOp) (operand : FlatTextFieldOperand)
    (values : List String) (context : FlatContext)
    (empty : operand.valueListCell context = .empty) :
    (FlatCondition.tokenValueList op.quantifier [operand] (.literals values)).evalFull
      context true = .notFired := by
  simp only [FlatCondition.evalFull, Bool.true_or, ↓reduceIte,
    FlatCondition.evalSelected, ConditionTree.evalVerdict,
    FlatConditionLeaf.evalSelected]
  rw [selectedFlatTokenValueListSide_full,
    flatTokenValueSide_resolveSelected_full]
  cases op <;>
    simp [ValueListMembershipOp.quantifier,
      ValueListQuantifier.evalClassified, evalClassifiedValueListAtLeastOne,
      evalClassifiedValueListNotAll,
      ResolvedValueListQuantifierSide.hasPresent,
      ResolvedValueListQuantifierSide.anyMatches,
      FlatTokenValueSide.resolve, flatTokenValueListSide,
      literalTokenValueListSide, ResolvedValueListSide.anyMatches,
      ResolvedValueListSide.hasPresent, ResolvedValueListSide.contains, empty]

/-- `No` is the one value-list quantifier structurally eligible on a blank row; the clean empty field makes that fire omission-typed. -/
theorem flatEnumerationValueList_no_empty
    (operand : FlatEnumerationOperand) (values : List String)
    (context : FlatContext)
    (empty : context.observeValidationAt operand.field.id = .empty) :
    (FlatCondition.tokenValueList .no [.enumeration operand] (.literals values)).evalFull context false =
      .fired .omission := by
  simp only [FlatCondition.evalFull, FlatCondition.canFireOnEmpty,
    ConditionTree.evalBool, FlatConditionLeaf.canFireOnEmpty,
    ValueListQuantifier.canFireOnEmpty, Bool.false_or, ↓reduceIte,
    FlatCondition.evalSelected, ConditionTree.evalVerdict,
    FlatConditionLeaf.evalSelected]
  rw [selectedFlatTokenValueListSide_full,
    flatTokenValueSide_resolveSelected_full]
  simp [ValueListQuantifier.evalClassified, evalClassifiedValueListNo,
    ResolvedValueListQuantifierSide.hasUnknown,
    ResolvedValueListQuantifierSide.anyMatches,
    FlatTokenValueSide.resolve, flatTokenValueListSide,
    FlatTextFieldOperand.valueListCell, FlatTextFieldOperand.resolve,
    FlatEnumerationOperand.resolve, SimpleComparisonOperand.asTokenValueListCell,
    ResolvedEnumerationProjection.resolveOperand, literalTokenValueListSide,
    ResolvedValueListSide.hasUnknown, ResolvedValueListSide.anyMatches,
    ResolvedValueListSide.hasMissingPotential, ResolvedValueListSide.hasEmpty,
    ResolvedValueListSide.contains, ValueListCell.isUnknown,
    ValueListCell.isEmpty, empty]

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
