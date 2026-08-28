import A12Kernel.Elaboration.ParallelNumericDirectRunResult
import A12Kernel.Proofs.NumericComputationRunResult

/-! # Isolated direct parallel Number-result laws -/

namespace A12Kernel

/-- Every successful merge certifies that no outcome-classified target is also claimed by its post-loop index-clearing producer. `executeResult` reaches its public view only through this gate. -/
theorem parallelNumericDirect_addIndexClears_noClassifiedIndexClear
    (classified view :
      NumericComputationRunView ResidualMessage CellAddr)
    (indexClears : List CellAddr)
    (success :
      addParallelNumericDirectIndexClears classified indexClears =
        .ok view) :
    parallelNumericDirectClassifiedIndexClear?
      classified indexClears = none := by
  unfold addParallelNumericDirectIndexClears at success
  cases overlap :
      parallelNumericDirectClassifiedIndexClear? classified indexClears with
  | some address =>
      simp [overlap] at success
  | none =>
      rfl

/-- The ordinary dependency inventory is exactly the validated declarations referenced by the checked expression or guard. -/
theorem checkedIsolatedParallelNumericDirectRun_ordinaryDependencies_exact
    (checked : CheckedIsolatedParallelNumericDirectRun model)
    (field : FieldId) :
    field ∈ checked.ordinaryFieldDependencies ↔
      ∃ declaration ∈ model.fields,
        declaration.id = field ∧
          checked.referencesField declaration.id = true := by
  rw [CheckedIsolatedParallelNumericDirectRun.ordinaryFieldDependencies,
    List.mem_map]
  constructor
  · rintro ⟨declaration, member, equality⟩
    rw [List.mem_filter] at member
    exact ⟨declaration, member.1, equality, member.2⟩
  · rintro ⟨declaration, member, equality, referenced⟩
    exact ⟨declaration, by simpa using And.intro member referenced, equality⟩

/-- The implicit index dependency inventory is exactly the validated declarations used by at least one checked parallel route. -/
theorem checkedIsolatedParallelNumericDirectRun_indexDependencies_exact
    (checked : CheckedIsolatedParallelNumericDirectRun model)
    (field : FieldId) :
    field ∈ checked.indexFieldDependencies ↔
      ∃ declaration ∈ model.fields,
        declaration.id = field ∧
          checked.referencesIndexField declaration.id = true := by
  rw [CheckedIsolatedParallelNumericDirectRun.indexFieldDependencies,
    List.mem_map]
  constructor
  · rintro ⟨declaration, member, equality⟩
    rw [List.mem_filter] at member
    exact ⟨declaration, member.1, equality, member.2⟩
  · rintro ⟨declaration, member, equality, referenced⟩
    exact ⟨declaration, by simpa using And.intro member referenced, equality⟩

/-- Successful whole-call composition preserves the existing addressed result and the exact prepared finding inventory. -/
theorem checkedIsolatedParallelNumericDirectRun_executeResultWithFormalInputs_exact
    (checked : CheckedIsolatedParallelNumericDirectRun model)
    (input : CheckedDocument model)
    (plan : CheckedComputationFormalInputPlan model)
    (prepared : ComputationFormalInputPreparation model)
    (numeric : NumericComputationRunView
      (ComputationFormalMessage Unit) CellAddr)
    (planned : checked.formalInputPlan = .ok plan)
    (preparation : plan.prepare input = .ok prepared)
    (executed : checked.executeResult prepared.preliminary
      (fun _ => ()) [] = .ok numeric) :
    checked.executeResultWithFormalInputs input =
      .ok (NumericComputationFormalInputRunView.of numeric
        prepared.formalErrorsInOperands) := by
  rw [CheckedIsolatedParallelNumericDirectRun.executeResultWithFormalInputs,
    planned]
  simp only [Except.mapError, bind, Except.bind, preparation, executed]

/-- A post-preparation execution failure retains the exact eager inventory beside the unchanged addressed fault. -/
theorem checkedIsolatedParallelNumericDirectRun_executeResultWithFormalInputs_failure_exact
    (checked : CheckedIsolatedParallelNumericDirectRun model)
    (input : CheckedDocument model)
    (plan : CheckedComputationFormalInputPlan model)
    (prepared : ComputationFormalInputPreparation model)
    (fault : ParallelNumericDirectRunResultError)
    (planned : checked.formalInputPlan = .ok plan)
    (preparation : plan.prepare input = .ok prepared)
    (executed : checked.executeResult prepared.preliminary
      (fun _ => ()) [] = .error fault) :
    checked.executeResultWithFormalInputs input =
      .error (.execution prepared.formalErrorsInOperands fault) := by
  rw [CheckedIsolatedParallelNumericDirectRun.executeResultWithFormalInputs,
    planned]
  simp only [Except.mapError, bind, Except.bind, preparation, executed]

end A12Kernel
