import A12Kernel.Semantics.FlatValidation

/-! # A12Kernel.Proofs.FlatNumberValueList — checked Number list laws -/

namespace A12Kernel

@[simp]
theorem flatNumberValueListCell_empty
    (field : FlatNumberField) (context : FlatContext)
    (empty : context.observeValidationAt field.id = .empty) :
    field.valueListCell context = .empty := by
  simp [FlatNumberField.valueListCell, empty]

@[simp]
theorem flatNumberValueListCell_present
    (field : FlatNumberField) (context : FlatContext) (value : Rat)
    (present : context.observeValidationAt field.id = .value (.num value)) :
    field.valueListCell context = .present value := by
  simp [FlatNumberField.valueListCell, present]

@[simp]
theorem flatNumberValueListCell_unknown
    (field : FlatNumberField) (context : FlatContext) (cause : FormalCause)
    (unknown : context.observeValidationAt field.id = .unknown cause) :
    field.valueListCell context = .unknown cause := by
  simp [FlatNumberField.valueListCell, unknown]

@[simp]
theorem flatNumberValueList_canFireOnEmpty
    (quantifier : ValueListQuantifier) (operands : List FlatNumberField)
    (values : FlatNumberValueSide) :
    (FlatCondition.numberValueList quantifier operands values).canFireOnEmpty =
      quantifier.canFireOnEmpty := by
  rfl

/-- Every Number operand on either side remains relevance-gated before the shared quantifier consumes a cell. -/
@[simp]
theorem flatNumberValueList_irrelevant_unknown
    (quantifier : ValueListQuantifier) (operand : FlatNumberField)
    (remaining : List FlatNumberField) (values : FlatNumberValueSide)
    (context : FlatContext) :
    (FlatCondition.numberValueList quantifier (operand :: remaining) values).evalSelected
      context (fun _ => false) = .unknown := by
  simp [FlatCondition.evalSelected, FlatNumberValueSide.allOperands]

/-- Included and NotIncluded share the kernel's empty-subject suppression; neither imports direct comparison's Number empty substitution. -/
theorem flatNumberValueMembership_empty
    (op : ValueListMembershipOp) (operand : FlatNumberField)
    (values : List Rat) (context : FlatContext)
    (empty : operand.valueListCell context = .empty) :
    (FlatCondition.numberValueList op.quantifier [operand] (.literals values)).evalFull
      context true = .notFired := by
  cases op <;>
    simp [ValueListMembershipOp.quantifier, FlatCondition.evalFull,
      FlatCondition.evalSelected, FlatNumberValueSide.allOperands,
      FlatNumberValueSide.operands, FlatNumberValueSide.resolve,
      flatNumberValueListSide, literalNumberValueListSide,
      ValueListQuantifier.eval, evalValueListAtLeastOne,
      evalValueListNotAll, ResolvedValueListSide.anyMatches,
      ResolvedValueListSide.hasPresent, empty]

/-- `No` remains the sole Number-list quantifier eligible on a blank row, and its missing field makes the firing omission-typed. -/
theorem flatNumberValueList_no_empty
    (operand : FlatNumberField) (values : List Rat)
    (context : FlatContext)
    (empty : operand.valueListCell context = .empty) :
    (FlatCondition.numberValueList .no [operand] (.literals values)).evalFull
      context false = .fired .omission := by
  simp [FlatCondition.evalFull, FlatCondition.evalSelected,
    FlatNumberValueSide.allOperands, FlatNumberValueSide.operands,
    FlatNumberValueSide.resolve, flatNumberValueListSide,
    literalNumberValueListSide, ValueListQuantifier.eval,
    evalValueListNo, ResolvedValueListSide.hasUnknown,
    ResolvedValueListSide.anyMatches, ResolvedValueListSide.hasMissingPotential,
    ResolvedValueListSide.hasEmpty, ResolvedValueListSide.contains,
    ValueListQuantifier.canFireOnEmpty, ValueListCell.isUnknown,
    ValueListCell.isEmpty, empty]

end A12Kernel
