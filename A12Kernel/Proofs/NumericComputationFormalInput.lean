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

/-- The table inventory is exactly the validated declarations in its preprocessed operand scope. -/
theorem checkedNumericComputationTable_fieldDependencies_exact
    (table : CheckedNumericComputationTable model)
    (field : FieldId) :
    field ∈ table.fieldDependencies ↔
      ∃ declaration ∈ model.fields,
        declaration.id = field ∧ table.operandField declaration.id = true := by
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

/-- Whole-call composition retains the exact prepared input findings beside the numeric result over the same staged cells. -/
theorem checkedNumericComputationRun_executeResultWithFormalInputs_exact
    (run : CheckedNumericComputationRun model)
    (world : World) (input : CheckedDocument model)
    (inputPlan : CheckedComputationFormalInputPlan model)
    (prepared : ComputationFormalInputPreparation model)
    (numeric : NumericComputationRunView (ComputationFormalMessage Unit))
    (planned : run.formalInputPlan = .ok inputPlan)
    (preparation : inputPlan.prepare input = .ok prepared)
    (executed : run.executeResult world prepared.preliminary.computationInput (fun _ => ()) [] = .ok numeric)
    (assembled : ComputationFormalInputFinding.checkAssembly prepared.formalErrorsInOperands = .ok ()) :
    (run.executeResultWithFormalInputs world input).map (fun view =>
      (view.formalErrorsInOperands, view.numeric)) =
      .ok (prepared.formalErrorsInOperands, numeric) := by
  rw [CheckedNumericComputationRun.executeResultWithFormalInputs, planned]
  simp only [bind, Except.bind, Except.mapError, preparation]
  rw [executed]
  simp [ComputationFormalInputFinding.assembleResult, assembled, bind, Except.bind, pure, Except.pure, Except.map, NumericComputationFormalInputRunView.of] <;> rfl

/-- After input preparation succeeds, a failed numeric execution retains the cached and generated findings beside the unchanged failure. -/
theorem checkedNumericComputationRun_executeResultWithFormalInputs_failure_exact
    (run : CheckedNumericComputationRun model)
    (world : World) (input : CheckedDocument model)
    (inputPlan : CheckedComputationFormalInputPlan model)
    (prepared : ComputationFormalInputPreparation model)
    (fault : NumericComputationRunResultFault)
    (planned : run.formalInputPlan = .ok inputPlan)
    (preparation : inputPlan.prepare input = .ok prepared)
    (executed : run.executeResult world prepared.preliminary.computationInput (fun _ => ()) [] = .error fault) :
    run.executeResultWithFormalInputs world input =
      .error (.execution prepared.formalErrorsInOperands fault) := by
  rw [CheckedNumericComputationRun.executeResultWithFormalInputs, planned]
  simp only [bind, Except.bind, Except.mapError, preparation]
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
      prepared.preliminary.readComputation (fun _ => ()) [] = .ok result)
    (assembled : ComputationFormalInputFinding.checkAssembly prepared.formalErrorsInOperands = .ok ()) :
    (operation.executeResultWithFormalInputs input).map (fun view =>
      (view.formalErrorsInOperands, view.numeric)) =
        .ok (prepared.formalErrorsInOperands, result.numeric) := by
  rw [CheckedAddressedNumberFirstFilledComputation.executeResultWithFormalInputs,
    planned]
  simp only [Except.mapError, bind, Except.bind, preparation]
  rw [executed]
  simp [ComputationFormalInputFinding.assembleResult, assembled, bind, Except.bind, pure, Except.pure, Except.map, NumericComputationFormalInputRunView.of] <;> rfl

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
