import A12Kernel.Elaboration.NumberEntityValueList

/-! # Checked mixed Number entity-list value-list laws -/

namespace A12Kernel

/-- The combined checked source excludes a repeated direct field across either authored side. -/
theorem checkedNumberEntityValueList_uniqueDirectOperands
    (checked : CheckedNumberEntityValueListSource model) :
    firstDuplicateDirectNumberEntityField?
      (checked.fields.operands ++ checked.values.operands) = none :=
  checked.uniqueDirectOperands

/-- Rich two-sided execution is exactly the existing ordered evaluator over the resolved operand projections. -/
theorem resolvedCheckedNumberEntityValueList_evaluate_delegates
    (resolved : ResolvedCheckedNumberEntityValueList model) :
    resolved.evaluate =
      resolved.quantifier.evalOrdered
        (resolved.fields.map (·.valueListSideAt .validation))
        (resolved.values.map (·.valueListSideAt .validation)) := by
  rfl

/-- A fields-side match decides `No` before a later operand-local partial nonrelevance. -/
theorem valueListNo_match_before_nonRelevantOperand
    : ValueListQuantifier.no.evalOrdered (kind := .token)
      [{ cells := [.present "A"]
         hasUninstantiatedTail := false
         hasHaving := false },
       { cells := []
         hasUninstantiatedTail := false
         hasHaving := false
         hasNonRelevant := true }]
      [{ cells := [.present "A"]
         hasUninstantiatedTail := false
         hasHaving := false }] =
      .notFired := by
  rfl

/-- Reversing the same two operands exposes partial nonrelevance before the later match. -/
theorem valueListNo_nonRelevantOperand_before_match
    (value : ValueListAtom kind) :
    ValueListQuantifier.no.evalOrdered
      [{ cells := []
         hasUninstantiatedTail := false
         hasHaving := false
         hasNonRelevant := true },
       { cells := [.present value]
         hasUninstantiatedTail := false
         hasHaving := false }]
      [{ cells := [.present value]
         hasUninstantiatedTail := false
         hasHaving := false }] =
      .unknown := by
  rfl

end A12Kernel
