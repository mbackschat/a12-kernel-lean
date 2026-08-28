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

/-- The complete formal-input inventory is exactly the validated declarations used as an endpoint, a dynamic key, or the shared semantic-index column. -/
theorem checkedIndexedDateRangeConstructionComputation_formalInputFields_exact
    (operation : CheckedIndexedDateRangeConstructionComputation model)
    (field : FieldId) :
    field ∈ operation.formalInputFields ↔
      ∃ declaration ∈ model.fields,
        declaration.id = field ∧
          (operation.referencesEndpointField declaration.id = true ∨
            operation.referencesKeyField declaration.id = true ∨
            operation.referencesIndexField declaration.id = true) := by
  rw [CheckedIndexedDateRangeConstructionComputation.formalInputFields,
    List.mem_map]
  constructor
  · rintro ⟨declaration, member, equality⟩
    rw [List.mem_filter] at member
    simp only [Bool.or_eq_true] at member
    exact ⟨declaration, member.1, equality, by
      simpa [or_assoc] using member.2⟩
  · rintro ⟨declaration, member, equality, referenced⟩
    exact ⟨declaration, by
      rw [List.mem_filter]
      simp only [Bool.or_eq_true]
      exact ⟨member, by simpa [or_assoc] using referenced⟩, equality⟩

/-- Successful whole-call composition returns the unchanged DateRange result carrying the exact prepared inventory in its residual channel. -/
theorem checkedIndexedDateRangeConstructionComputation_executeResultWithFormalInputs_exact
    (operation : CheckedIndexedDateRangeConstructionComputation model)
    (input : CheckedDocument model)
    (plan : CheckedComputationFormalInputPlan model)
    (prepared : ComputationFormalInputPreparation model)
    (result : DateRangeComputationRunView ComputationFormalInputFinding)
    (planned : operation.formalInputPlan = .ok plan)
    (preparation : plan.prepare input = .ok prepared)
    (executed : operation.executeResult prepared.preliminary
      prepared.formalErrorsInOperands = .ok result) :
    operation.executeResultWithFormalInputs input = .ok result := by
  rw [CheckedIndexedDateRangeConstructionComputation.executeResultWithFormalInputs,
    planned]
  simp only [Except.mapError, bind, Except.bind, preparation, executed]

/-- A post-preparation indexed execution failure retains the exact eager inventory beside the unchanged existing fault. -/
theorem checkedIndexedDateRangeConstructionComputation_executeResultWithFormalInputs_failure_exact
    (operation : CheckedIndexedDateRangeConstructionComputation model)
    (input : CheckedDocument model)
    (plan : CheckedComputationFormalInputPlan model)
    (prepared : ComputationFormalInputPreparation model)
    (fault : IndexedDateRangeConstructionComputationFault)
    (planned : operation.formalInputPlan = .ok plan)
    (preparation : plan.prepare input = .ok prepared)
    (executed : operation.executeResult prepared.preliminary
      prepared.formalErrorsInOperands = .error fault) :
    operation.executeResultWithFormalInputs input =
      .error (.execution prepared.formalErrorsInOperands fault) := by
  rw [CheckedIndexedDateRangeConstructionComputation.executeResultWithFormalInputs,
    planned]
  simp only [Except.mapError, bind, Except.bind, preparation, executed]

end A12Kernel
