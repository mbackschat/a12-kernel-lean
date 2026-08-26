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

/-- Rich indexed-construction result projection retains the checked target identity and delegates all five channels to the established DateRange classifier. -/
theorem checkedIndexedDateRangeConstructionComputation_executeResult_projects
    (operation : CheckedIndexedDateRangeConstructionComputation model)
    (preliminary : CheckedIndexPreliminary model)
    (residualMessages : List ResidualMessage)
    (result : IndexedDateRangeConstructionComputationResult)
    (evaluated : operation.execute preliminary = .ok result) :
    operation.executeResult preliminary residualMessages =
      .ok (DateRangeComputationRunView.fromOutcomes preliminary.base
        residualMessages [(operation.target.source.id, result.outcome)]) := by
  rw [CheckedIndexedDateRangeConstructionComputation.executeResult, evaluated]
  rfl

end A12Kernel
