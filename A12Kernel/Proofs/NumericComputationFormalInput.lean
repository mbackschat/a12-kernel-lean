import A12Kernel.Elaboration.NumericComputation.FormalInput

/-! # Checked numeric-computation formal-input laws -/

namespace A12Kernel

/-- The concrete dependency inventory is exactly the validated model declarations referenced by the checked expression. -/
theorem checkedNumericComputationOperation_fieldDependencies_exact
    (operation : CheckedNumericComputationOperation model)
    (field : FieldId) :
    field ∈ operation.fieldDependencies ↔
      ∃ declaration ∈ model.fields,
        declaration.id = field ∧
          operation.core.expression.anyAtom
            (CheckedNumericComputationAtom.references model declaration.id) = true := by
  rw [CheckedNumericComputationOperation.fieldDependencies, List.mem_map]
  constructor
  · rintro ⟨declaration, member, equality⟩
    rw [List.mem_filter] at member
    exact ⟨declaration, member.1, equality, member.2⟩
  · rintro ⟨declaration, member, equality, referenced⟩
    exact ⟨declaration, by simpa using And.intro member referenced, equality⟩

/-- The table dependency inventory is exactly the validated declarations referenced by at least one checked alternative guard or operation. -/
theorem checkedNumericComputationTable_fieldDependencies_exact
    (table : CheckedNumericComputationTable model)
    (field : FieldId) :
    field ∈ table.fieldDependencies ↔
      ∃ declaration ∈ model.fields,
        declaration.id = field ∧ table.referencesField declaration.id = true := by
  rw [CheckedNumericComputationTable.fieldDependencies, List.mem_map]
  constructor
  · rintro ⟨declaration, member, equality⟩
    rw [List.mem_filter] at member
    exact ⟨declaration, member.1, equality, member.2⟩
  · rintro ⟨declaration, member, equality, referenced⟩
    exact ⟨declaration, by simpa using And.intro member referenced, equality⟩

/-- The run projection contributes every checked target exactly in run order, so global formal-input exclusion cannot silently omit an intermediate or terminal computed field. -/
theorem checkedNumericComputationRun_formalInputOperations_targets_exact
    (run : CheckedNumericComputationRun model) :
    run.formalInputOperations.map Prod.fst =
      run.tables.map (·.targetField) := by
  simp [CheckedNumericComputationRun.formalInputOperations]

/-- Whole-call composition projects the eager checked-plan findings exactly and preserves the independently classified numeric result. -/
theorem checkedNumericComputationRun_executeResultWithFormalInputs_exact
    (run : CheckedNumericComputationRun model)
    (world : World) (input : CheckedDocument model)
    (inputPlan : CheckedComputationFormalInputPlan model)
    (numeric : NumericComputationRunView (ComputationFormalMessage Unit))
    (planned : run.formalInputPlan = .ok inputPlan)
    (executed : run.executeResult world input (fun _ => ()) [] = .ok numeric) :
    (run.executeResultWithFormalInputs world input).map (fun view =>
      (view.formalErrorsInOperands, view.numeric)) =
      .ok (inputPlan.findings input, numeric) := by
  rw [CheckedNumericComputationRun.executeResultWithFormalInputs, planned]
  simp only [bind, Except.bind, Except.mapError]
  rw [executed]
  rfl

/-- Once formal-input planning succeeds, a failed numeric execution retains exactly that plan's eager raw findings beside the unchanged failure. -/
theorem checkedNumericComputationRun_executeResultWithFormalInputs_failure_exact
    (run : CheckedNumericComputationRun model)
    (world : World) (input : CheckedDocument model)
    (inputPlan : CheckedComputationFormalInputPlan model)
    (fault : NumericComputationRunResultFault)
    (planned : run.formalInputPlan = .ok inputPlan)
    (executed : run.executeResult world input (fun _ => ()) [] = .error fault) :
    run.executeResultWithFormalInputs world input =
      .error (.execution (inputPlan.findings input) fault) := by
  rw [CheckedNumericComputationRun.executeResultWithFormalInputs, planned]
  simp only [bind, Except.bind, Except.mapError]
  rw [executed]

/-- Successful addressed Number first-filled composition preserves the complete eager raw inventory beside the independently classified typed Number result. -/
theorem addressedNumberFirstFilled_executeResultWithFormalInputs_exact
    (operation : CheckedAddressedNumberFirstFilledComputation model)
    (input : CheckedDocument model)
    (plan : CheckedComputationFormalInputPlan model)
    (prepared : ComputationFormalInputPreparation model)
    (result : AddressedNumberFirstFilledComputationRunView model Unit)
    (planned : operation.formalInputPlan = .ok plan)
    (preparation : plan.prepare input = .ok prepared)
    (executed : operation.executeResultWithRead input
      prepared.preliminary.readComputation (fun _ => ()) [] = .ok result) :
    (operation.executeResultWithFormalInputs input).map (fun view =>
      (view.formalErrorsInOperands, view.numeric)) =
        .ok (prepared.formalErrorsInOperands, result.numeric) := by
  rw [CheckedAddressedNumberFirstFilledComputation.executeResultWithFormalInputs,
    planned]
  simp only [Except.mapError, bind, Except.bind, preparation]
  rw [executed]
  rfl

/-- A post-preparation addressed Number first-filled failure retains the exact eager raw inventory beside the unchanged execution fault. -/
theorem addressedNumberFirstFilled_executeResultWithFormalInputs_failure_exact
    (operation : CheckedAddressedNumberFirstFilledComputation model)
    (input : CheckedDocument model)
    (plan : CheckedComputationFormalInputPlan model)
    (prepared : ComputationFormalInputPreparation model)
    (fault : AddressedNumberFirstFilledComputationFault)
    (planned : operation.formalInputPlan = .ok plan)
    (preparation : plan.prepare input = .ok prepared)
    (executed : operation.executeResultWithRead input
      prepared.preliminary.readComputation (fun _ => ()) [] = .error fault) :
    operation.executeResultWithFormalInputs input =
      .error (.execution prepared.formalErrorsInOperands fault) := by
  rw [CheckedAddressedNumberFirstFilledComputation.executeResultWithFormalInputs,
    planned]
  simp only [Except.mapError, bind, Except.bind, preparation, executed]

end A12Kernel
