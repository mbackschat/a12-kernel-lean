import A12Kernel.Elaboration.IndexedDateRangeConstructionComputation

/-! # String-keyed DateRange construction certificates -/

namespace A12Kernel

/-- The checked operation exposes one shared indexed group and the exact target ownership and presentation certificates used by execution. -/
theorem checkedIndexedDateRangeConstructionComputation_admitted
    (operation : CheckedIndexedDateRangeConstructionComputation model) :
    operation.start.key.admittedBy model = true ∧
      operation.finish.key.admittedBy model = true ∧
      operation.start.group = operation.finish.group ∧
      model.ownsDirectDateRangeTarget operation.declaringGroup operation.target = true ∧
      DateRangeConstructionTargetFormat.ofProfiles?
        (.full operation.start.format) operation.target.format = some operation.format :=
  ⟨operation.start.keyOwned, operation.finish.keyOwned, operation.sameGroup,
    operation.targetOwnedByGroup, operation.profileOwned⟩

end A12Kernel
