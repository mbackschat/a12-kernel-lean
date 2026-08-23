import A12Kernel.Elaboration.SemanticIndexDateRange

/-! # Keyed DateRange operand laws

The keyed read is deliberately not a second component account. These laws pin the two properties that
make that true: it factors through the same shared component clause the direct read uses, and its two
failure classes stay separated — an unresolvable lookup propagates while a wrong-kind selected cell
collapses the way a direct malformed read does.
-/

namespace A12Kernel

/-- The keyed read factors into the range projection followed by the shared component clause, so
emptiness, unavailability, and fillability follow from that clause's own laws rather than being
restated for this route. Together with `resolveDateRangeBoundNumericOperand_factors` this is what
makes the keyed and direct reads structurally unable to disagree about a reached observation. -/
theorem semanticIndexDateRangeBoundPart_resolve_factors
    (operation : CheckedSemanticIndexDateRangeBoundPart model)
    (preliminary : CheckedIndexPreliminary model) (keyRaw : RawFlatContext)
    (outer : Env) (observed : CellObservation DateRangeCellValue)
    (reached : operation.source.observePreliminaryRange preliminary keyRaw
      .validation outer = .ok observed) :
    operation.resolvePreliminaryNumericOperand preliminary keyRaw outer =
      .ok (operation.part.fromDateRangeBoundObservation operation.bound
        observed) := by
  simp [CheckedSemanticIndexDateRangeBoundPart.resolvePreliminaryNumericOperand,
    reached]

/-- A lookup that could not be resolved at all keeps its own error, because a consumer must be able
to tell an unresolvable column from a resolved one that selected nothing. -/
theorem semanticIndexDateRangeBoundPart_resolve_context
    (operation : CheckedSemanticIndexDateRangeBoundPart model)
    (preliminary : CheckedIndexPreliminary model) (keyRaw : RawFlatContext)
    (outer : Env) (error : SemanticIndexContextError)
    (failed : operation.source.observePreliminaryRange preliminary keyRaw
      .validation outer = .error (.context error)) :
    operation.resolvePreliminaryNumericOperand preliminary keyRaw outer =
      .error error := by
  simp [CheckedSemanticIndexDateRangeBoundPart.resolvePreliminaryNumericOperand,
    failed]

/-- A selected cell whose kind is not a DateRange collapses to formal unavailability rather than to
an error or a zero. The static gate makes it unreachable; this keeps a malformed checked document
from acquiring a value through the keyed route when it could not through the direct one. -/
theorem semanticIndexDateRangeBoundPart_resolve_wrongKind
    (operation : CheckedSemanticIndexDateRangeBoundPart model)
    (preliminary : CheckedIndexPreliminary model) (keyRaw : RawFlatContext)
    (outer : Env) (fault : DirectDateRangeFault)
    (failed : operation.source.observePreliminaryRange preliminary keyRaw
      .validation outer = .error (.payload fault)) :
    operation.resolvePreliminaryNumericOperand preliminary keyRaw outer =
      .ok (.unknown .malformed) := by
  simp [CheckedSemanticIndexDateRangeBoundPart.resolvePreliminaryNumericOperand,
    failed]

/-- The keyed source carries the shared semantic-index certificate unchanged, so widening the index
field's kind reaches this operand without a second admission rule. -/
theorem checkedDateRangeSemanticIndex_index_unconstrained
    (checked : CheckedDateRangeSemanticIndexSource model) :
    model.admitsSingleGroupDeclaration checked.group
        checked.indexDeclaration = true ∧
      (checked.group.indexField == some checked.indexDeclaration.id) = true :=
  ⟨checked.indexOwned, checked.indexDeclared⟩

/-- The certified component read carries its selected declaration's own exposure witness, so no
consumer can reach a component the declared profile does not expose. -/
theorem checkedSemanticIndexDateRangeBoundPart_exposed
    (operation : CheckedSemanticIndexDateRangeBoundPart model) :
    model.exposesDateRangeBoundPart operation.source.targetField
      operation.part = true :=
  operation.componentExposed

end A12Kernel
