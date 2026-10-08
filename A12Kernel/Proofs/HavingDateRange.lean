import A12Kernel.Semantics.HavingDateRange

namespace A12Kernel.HavingDateRangePredicate

/-- Empty scalar observations bypass even a failing entity-list resolver (spec/05 §8). -/
theorem evalOverlap_empty_scalar (phase : Phase) (context : ResolvingCorrelationContext Error)
    (frame : CorrelationFrame) (reference : HavingPresenceRef)
    (slots : List (HavingFieldListSlot HavingPresenceRef))
    (emptyScalar : readInterval context phase (frame.envAt reference.origin) reference = .ok .empty) :
    evalOverlap (some reference) slots phase context frame = .ok .notTrue := by
  simp [evalOverlap, emptyScalar, ComputationOverlapSearch.scalarUsing, bind, Except.bind, pure, Except.pure]

/-- Reached scalar poison is retained before any list acquisition. -/
theorem evalOverlap_poison_scalar (context : ResolvingCorrelationContext Error)
    (frame : CorrelationFrame) (reference : HavingPresenceRef)
    (slots : List (HavingFieldListSlot HavingPresenceRef)) (cause : FormalCause)
    (poisonScalar : readInterval context .computation (frame.envAt reference.origin) reference = .ok (.poison cause)) :
    evalOverlap (some reference) slots .computation context frame = .ok (.poison cause) := by
  simp [evalOverlap, poisonScalar, ComputationOverlapSearch.scalarUsing, bind, Except.bind, pure, Except.pure]

end A12Kernel.HavingDateRangePredicate
