import A12Kernel.Semantics.ComputationValueList

namespace A12Kernel

namespace ValueListCell

/-- A deciding present cell excludes every later formal cause from this scan. -/
theorem anyComputation_deciding_prefix
    (predicate : ValueListAtom kind → Bool) (value : ValueListAtom kind)
    (suffix : List (ValueListCell kind)) (decides : predicate value = true) :
    anyComputation predicate (.present value :: suffix) = .ok true := by
  simp [anyComputation, decides]

/-- A reached invalid cell excludes every later match from this scan. -/
theorem anyComputation_poison_prefix
    (predicate : ValueListAtom kind → Bool) (cause : FormalCause)
    (suffix : List (ValueListCell kind)) :
    anyComputation predicate (.unknown cause :: suffix) = .error cause := rfl

end ValueListCell

namespace ValueListQuantifier

/-- An empty member side decides AtLeastOne before any field is read. -/
theorem atLeastOne_empty_members
    (fields : List (ResolvedValueListSide kind)) :
    ValueListQuantifier.atLeastOne.evalComputation fields [] = .notTrue := rfl

end ValueListQuantifier

end A12Kernel
