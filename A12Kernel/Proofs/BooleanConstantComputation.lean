import A12Kernel.Elaboration.BooleanConstantComputation

/-! # Boolean and Confirm constant-computation laws -/

namespace A12Kernel

/-- The checked gate accepts exactly both Boolean constants and the True-only Confirm case. -/
theorem checkBooleanConstantOperation_accepts_iff
    (targetKind : FieldKind) (value : Bool) :
    (checkBooleanConstantOperation targetKind value).isOk =
      (targetKind == .boolean || (targetKind == .confirm && value)) := by
  cases targetKind <;> cases value <;> rfl

/-- Checked constant execution returns the exact value retained by its target-kind-certified operation. -/
theorem checkedBooleanConstantComputation_execute_exact
    (operation : CheckedBooleanConstantComputation model) :
    operation.execute = .value operation.operation.operation.value := by
  rfl

/-- Result construction retains the exact checked definition, including its declaration group and target-owned placement. -/
theorem checkedBooleanConstantComputation_executeResult_retains_definition
    (operation : CheckedBooleanConstantComputation model)
    (input : CheckedDocument model) :
    (operation.executeResult input).operation = operation := by
  rfl

/-- Constant result construction delegates source-relative classification to the shared Boolean result owner. -/
theorem checkedBooleanConstantComputation_executeResult_projects
    (operation : CheckedBooleanConstantComputation model)
    (input : CheckedDocument model) :
    (operation.executeResult input).boolean =
      BooleanComputationRunView.fromSourcedOutcomes [] [(
        operation.target.id, operation.execute,
        input.sourceBooleanTargetState operation.target.id)] := by
  rfl

/-- Checked application delegates only the retained source-relative actions to the shared Boolean destination fold. -/
theorem booleanConstantComputationRun_applyToChecked_delegates
    (view : BooleanConstantComputationRunView model)
    (destination : CheckedDocument model) :
    view.applyToChecked destination =
      view.boolean.applyTo destination.sourceBooleanTargetState := by
  rfl

/-! ## Repeatable constant targets -/

/-- Two checked constants with the same target and the same value execute identically however they
are placed. This is the measured claim stated as a law: a root declaration and a declaration at the
target's own group produce the same rows and the same values, because iteration comes from the
target's scope and a constant supplies no other source
([checkpoint](../../docs/SOURCES.md#src-cross-group-repeatable-constant-target)). -/
theorem checkedRepeatableBooleanConstantComputation_execute_ignoresDeclaringGroup
    {model : FlatModel}
    (first second : CheckedRepeatableBooleanConstantComputation model)
    (sameTarget :
      first.checkedTarget.targetField = second.checkedTarget.targetField)
    (sameDeclaration :
      first.checkedTarget.declaration = second.checkedTarget.declaration)
    (sameValue : first.value = second.value)
    (input : CheckedDocument model) :
    first.execute input = second.execute input := by
  simp only [CheckedRepeatableBooleanConstantComputation.execute,
    sameTarget, sameDeclaration, sameValue]

/-- Every emitted row carries the same constant. The family has no per-row content beyond its
address, so a consumer needs only the row set and one value; nothing can make one row differ. -/
theorem checkedRepeatableBooleanConstantComputation_execute_constantAcrossRows
    {model : FlatModel}
    (operation : CheckedRepeatableBooleanConstantComputation model)
    (input : CheckedDocument model)
    (outcomes : List RepeatableBooleanConstantComputationOutcome)
    (executed : operation.execute input = .ok outcomes) :
    ∀ entry ∈ outcomes, entry.result = .value operation.value := by
  simp only [CheckedRepeatableBooleanConstantComputation.execute] at executed
  split at executed
  · simp at executed
  · split at executed
    · simp at executed
    · obtain ⟨rfl⟩ := Except.ok.inj executed
      intro entry member
      simp only [List.mem_map] at member
      obtain ⟨path, _, built⟩ := member
      exact built ▸ rfl

end A12Kernel
