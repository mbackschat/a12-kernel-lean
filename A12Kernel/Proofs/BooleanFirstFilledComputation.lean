import A12Kernel.Elaboration.BooleanFirstFilledComputation

/-! # Boolean `FirstFilledValue` laws at a fixed or a repeatable target -/

namespace A12Kernel

/-- An exhausted Boolean source clears rather than manufacturing `false`. -/
theorem firstFilledBoolean_exhausted_noValue :
    evalFirstFilledBoolean [] = .noValue := by
  rfl

/-- `false` is a present Boolean value, not the empty-selection identity. -/
theorem firstFilledBoolean_false_is_value
    (tail : List FirstFilledBooleanCell) :
    evalFirstFilledBoolean (.present false :: tail) =
      .value false := by
  rfl

/-- The checked operation retains Boolean carriers and excludes forbidden target references; positive conditional group membership remains in the complete inventory (spec/09 §5). -/
theorem checkedBooleanFirstFilled_carriers (operation : CheckedBooleanFirstFilledComputation model) :
    operation.target.policy.kind = .boolean ∧
      operation.site.source.declarations.all (·.policy.kind == .boolean) = true ∧
      operation.referencesWith operation.targetField (·.forbidsTarget operation.targetField) = false :=
  ⟨operation.targetBoolean, operation.sourceBoolean, operation.excludesTarget⟩

/-- The immutable-document executor is definitionally the caller-read route specialized to the document's checked read. -/
theorem checkedBooleanFirstFilled_executeWithRead_base
    (operation : CheckedBooleanFirstFilledComputation model)
    (input : CheckedDocument model) :
    operation.executeWithRead input input.read = operation.execute input := by
  rfl

/-- Result construction retains the checked operation and classifies every outcome against its exact immutable target state. -/
theorem checkedBooleanFirstFilled_executeResult_projects
    (operation : CheckedBooleanFirstFilledComputation model)
    (input : CheckedDocument model) (messages : List ResidualMessage)
    (outcomes : List BooleanFirstFilledComputationOutcome)
    (view : BooleanFirstFilledComputationRunView model ResidualMessage)
    (executed : operation.execute input = .ok outcomes)
    (produced : operation.executeResult input messages = .ok view) :
    view.operation = operation ∧
      view.boolean = BooleanComputationRunView.fromSourcedOutcomes messages
        (outcomes.map fun entry =>
          (entry.targetField, entry.result,
            input.sourceBooleanTargetStateAt entry.targetField)) := by
  rw [CheckedBooleanFirstFilledComputation.executeResult,
    CheckedBooleanFirstFilledComputation.executeResultWithRead]
    at produced
  change operation.executeWithRead input input.read = .ok outcomes at executed
  rw [executed] at produced
  simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at produced
  subst view
  exact ⟨rfl, rfl⟩

/-- Application is exactly the common Boolean fold over a separately supplied document's exact target-state projection. -/
theorem booleanFirstFilledRun_applyToChecked_delegates
    (view : BooleanFirstFilledComputationRunView model ResidualMessage)
    (destination : CheckedDocument model) :
    view.applyToChecked destination =
      view.boolean.applyTo destination.sourceBooleanTargetStateAt := by
  rfl

end A12Kernel
