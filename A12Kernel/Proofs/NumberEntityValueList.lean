import A12Kernel.Elaboration.NumberEntityValueList

/-! # Checked mixed Number entity-list value-list laws -/

namespace A12Kernel

/-- The combined checked source excludes a repeated direct field across either authored side. -/
theorem checkedNumberEntityValueList_uniqueDirectOperands
    (checked : CheckedNumberEntityValueListSource model) :
    firstDuplicateDirectNumberEntityField?
      (checked.fields.operands ++ checked.values.operands) = none :=
  checked.uniqueDirectOperands

/-- The semantic projection reads each already-addressed checked cell exactly once and preserves encounter order. -/
theorem resolvedCheckedNumberEntityOperand_valueListSideAt_cells
    (resolved : ResolvedCheckedNumberEntityOperand model)
    (phase : Phase) :
    (resolved.valueListSideAt phase).cells =
      resolved.addressedCells.map fun addressed =>
        (observeCell phase addressed.cell).asNumberValueListCell := by
  rfl

/-- Hierarchical tail, filter, and positional nonrelevance metadata cross the rich addressed boundary unchanged. -/
theorem resolvedCheckedNumberEntityOperand_valueListSideAt_metadata
    (resolved : ResolvedCheckedNumberEntityOperand model)
    (phase : Phase) :
    (resolved.valueListSideAt phase).hasUninstantiatedTail =
        resolved.hasUninstantiatedTail ∧
      (resolved.valueListSideAt phase).hasHaving =
        resolved.hasHaving ∧
      (resolved.valueListSideAt phase).hasNonRelevant =
        resolved.hasNonRelevant := by
  simp [ResolvedCheckedNumberEntityOperand.valueListSideAt]

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

/-- A failed starred topology remains an addressed construction error before any semantic side exists. -/
theorem checkedNumberEntityStarValueList_addressing_error
    (source : CheckedStarNumberSource model)
    (document : CheckedDocument model) (outer : Env)
    (cause : StarAddressingError)
    (failed :
      source.source.path.resolve document.source.toDocument outer =
        .error cause) :
    (CheckedNumberEntityOperand.star source).resolveCheckedValueListOperand
        document outer =
      .error (.addressing cause) := by
  simp [CheckedNumberEntityOperand.resolveCheckedValueListOperand,
    failed, Except.mapError, bind, Except.bind]

end A12Kernel
