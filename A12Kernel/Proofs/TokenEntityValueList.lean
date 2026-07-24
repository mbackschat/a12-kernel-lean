import A12Kernel.Elaboration.TokenEntityValueList

/-! # Checked mixed token entity-list value-list laws -/

namespace A12Kernel

/-- The combined checked source excludes a repeated exact direct String or Enumeration/category reference across either authored side. -/
theorem checkedTokenEntityValueList_uniqueDirectOperands
    (checked : CheckedTokenEntityValueListSource model) :
    firstDuplicateDirectTokenField?
      (checked.fields.operands ++ checked.values.operands) = none :=
  checked.uniqueDirectOperands

/-- Both checked sides retain the same statically admitted String or Enumeration base family. -/
theorem checkedTokenEntityValueList_commonFamily
    (checked : CheckedTokenEntityValueListSource model) :
    checked.fields.valueListFamily? = some checked.family ∧
      checked.values.valueListFamily? = some checked.family :=
  ⟨checked.fieldsFamily, checked.valuesFamily⟩

/-- The shared addressed core is projected through the exact checked String/Enumeration operand retained by this authored slot. -/
theorem resolvedCheckedTokenEntityOperand_valueListSideAt_cells
    (resolved : ResolvedCheckedTokenEntityOperand model) (phase : Phase) :
    (resolved.valueListSideAt phase).cells =
      resolved.core.addressedCells.map fun addressed =>
        resolved.source.tokenOperand.checkedValueListCellAt phase addressed.cell := by
  rfl

/-- Rich two-sided execution is exactly the existing ordered evaluator over the typed addressed projections. -/
theorem resolvedCheckedTokenEntityValueList_evaluate_delegates
    (resolved : ResolvedCheckedTokenEntityValueList model) :
    resolved.evaluate =
      resolved.quantifier.evalOrdered
        (resolved.fields.map (·.valueListSideAt .validation))
        (resolved.values.map (·.valueListSideAt .validation)) := by
  rfl

end A12Kernel
