import A12Kernel.Semantics.FlatValidation

/-! # A12Kernel.Proofs.FlatNumberValueList — checked Number list laws -/

namespace A12Kernel

private theorem filter_const_true (items : List α) :
    items.filter (fun _ => true) = items := by
  apply List.filter_eq_self.mpr
  simp

private theorem filter_const_false (items : List α) :
    items.filter (fun _ => false) = [] := by
  induction items <;> simp [*]

@[simp]
theorem flatNumberValueListCell_empty
    (field : FlatNumberField) (context : FlatContext)
    (empty : context.observeValidationAt field.id = .empty) :
    field.valueListCell context = .empty := by
  simp [FlatNumberField.valueListCell, CellObservation.asNumberValueListCell, empty]

@[simp]
theorem flatNumberValueListCell_present
    (field : FlatNumberField) (context : FlatContext) (value : Rat)
    (present : context.observeValidationAt field.id = .value (.num value)) :
    field.valueListCell context = .present value := by
  simp [FlatNumberField.valueListCell, CellObservation.asNumberValueListCell, present]

@[simp]
theorem flatNumberValueListCell_unknown
    (field : FlatNumberField) (context : FlatContext) (cause : FormalCause)
    (unknown : context.observeValidationAt field.id = .unknown cause) :
    field.valueListCell context = .unknown cause := by
  simp [FlatNumberField.valueListCell, CellObservation.asNumberValueListCell, unknown]

@[simp]
theorem flatNumberValueList_canFireOnEmpty
    (quantifier : ValueListQuantifier) (operands : List FlatNumberField)
    (values : FlatNumberValueSide) :
    (FlatCondition.numberValueList quantifier operands values).canFireOnEmpty =
      quantifier.canFireOnEmpty := by
  rfl

/-- Full relevance constructs exactly the ordinary resolved Number side. -/
@[simp]
theorem selectedFlatNumberValueListSide_full
    (operands : List FlatNumberField) (context : FlatContext) :
    selectedFlatNumberValueListSide operands context (fun _ => true) =
      .ofResolved (flatNumberValueListSide operands context) := by
  simp [selectedFlatNumberValueListSide,
    ResolvedValueListQuantifierSide.ofResolved, filter_const_true]

/-- Full relevance constructs exactly the ordinary resolved Number values side. -/
@[simp]
theorem flatNumberValueSide_resolveSelected_full
    (values : FlatNumberValueSide) (context : FlatContext) :
    values.resolveSelected context (fun _ => true) =
      .ofResolved (values.resolve context) := by
  cases values with
  | literals values => rfl
  | fields operands => exact selectedFlatNumberValueListSide_full operands context

/-- With every Number operand masked, the quantifiers retain their distinct per-cell relevance rules: only `No` becomes UNKNOWN. -/
@[simp]
theorem flatNumberValueList_allIrrelevant
    (quantifier : ValueListQuantifier) (operand : FlatNumberField)
    (remaining : List FlatNumberField) (values : FlatNumberValueSide)
    (context : FlatContext) :
    (FlatCondition.numberValueList quantifier (operand :: remaining) values).evalSelected
      context (fun _ => false) =
        match quantifier with
        | .atLeastOne => .notFired
        | .no => .unknown
        | .notAll => .notFired := by
  cases quantifier <;> cases values <;>
    simp [FlatCondition.evalSelected, selectedFlatNumberValueListSide,
      FlatNumberValueSide.resolveSelected, ValueListQuantifier.evalClassified,
      evalClassifiedValueListAtLeastOne, evalClassifiedValueListNo,
      evalClassifiedValueListNotAll, ResolvedValueListQuantifierSide.hasUnknown,
      ResolvedValueListQuantifierSide.hasPresent,
      ResolvedValueListQuantifierSide.anyMatches,
      flatNumberValueListSide,
      literalNumberValueListSide, ResolvedValueListSide.hasUnknown,
      ResolvedValueListSide.hasPresent, ResolvedValueListSide.anyMatches,
      ResolvedValueListSide.contains, filter_const_false]

/-- Included and NotIncluded share the kernel's empty-subject suppression; neither imports direct comparison's Number empty substitution. -/
theorem flatNumberValueMembership_empty
    (op : ValueListMembershipOp) (operand : FlatNumberField)
    (values : List Rat) (context : FlatContext)
    (empty : operand.valueListCell context = .empty) :
    (FlatCondition.numberValueList op.quantifier [operand] (.literals values)).evalFull
      context true = .notFired := by
  simp only [FlatCondition.evalFull, Bool.true_or, ↓reduceIte,
    FlatCondition.evalSelected, ConditionTree.evalVerdict,
    FlatConditionLeaf.evalSelected]
  rw [selectedFlatNumberValueListSide_full,
    flatNumberValueSide_resolveSelected_full]
  cases op <;>
    simp [ValueListMembershipOp.quantifier,
      ValueListQuantifier.evalClassified, evalClassifiedValueListAtLeastOne,
      evalClassifiedValueListNotAll,
      ResolvedValueListQuantifierSide.hasPresent,
      ResolvedValueListQuantifierSide.anyMatches,
      FlatNumberValueSide.resolve, flatNumberValueListSide,
      literalNumberValueListSide,
      ResolvedValueListSide.anyMatches, ResolvedValueListSide.hasPresent,
      ResolvedValueListSide.contains, empty]

/-- `No` remains the sole Number-list quantifier eligible on a blank row, and its missing field makes the firing omission-typed. -/
theorem flatNumberValueList_no_empty
    (operand : FlatNumberField) (values : List Rat)
    (context : FlatContext)
    (empty : operand.valueListCell context = .empty) :
    (FlatCondition.numberValueList .no [operand] (.literals values)).evalFull
      context false = .fired .omission := by
  simp only [FlatCondition.evalFull, ValueListQuantifier.canFireOnEmpty,
    FlatCondition.canFireOnEmpty, ConditionTree.evalBool,
    FlatConditionLeaf.canFireOnEmpty, Bool.false_or, ↓reduceIte,
    FlatCondition.evalSelected,
    ConditionTree.evalVerdict, FlatConditionLeaf.evalSelected]
  rw [selectedFlatNumberValueListSide_full,
    flatNumberValueSide_resolveSelected_full]
  simp [ValueListQuantifier.evalClassified,
    evalClassifiedValueListNo,
    ResolvedValueListQuantifierSide.hasUnknown,
    ResolvedValueListQuantifierSide.anyMatches,
    FlatNumberValueSide.resolve, flatNumberValueListSide,
    literalNumberValueListSide,
    ResolvedValueListSide.hasUnknown,
    ResolvedValueListSide.anyMatches, ResolvedValueListSide.hasMissingPotential,
    ResolvedValueListSide.hasEmpty, ResolvedValueListSide.contains,
    ValueListCell.isUnknown, ValueListCell.isEmpty, empty]

end A12Kernel
