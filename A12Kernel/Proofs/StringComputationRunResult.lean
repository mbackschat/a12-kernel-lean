import A12Kernel.Elaboration.StringComputationRunResult

/-! # String computation result-view laws

The public collections are extensional even though the executable representation follows plan order. These laws expose successful-instance inclusion, exact clearing classification, and the independent two-error-channel predicate.
-/

namespace A12Kernel

/-- A String target is classified as cleared exactly when it was source-filled and execution produced no computed-data instance. -/
theorem stringComputationRun_shouldClear_iff
    (input : CheckedDocument model) (field : FieldId)
    (outcome : StringTargetOutcome) :
    StringComputationRunView.shouldClear input (field, outcome) = true ↔
      outcome.hasComputedInstance = false ∧
        (input.sourceStringTargetState field).storedValue.isSome = true := by
  simp [StringComputationRunView.shouldClear]

/-- Every changed success is the identical address-and-payload member of the complete successful collection. -/
theorem stringComputationRun_withChanges_subset
    (input : CheckedDocument model) (residualMessages : List ResidualMessage)
    (outcomes : List (FieldId × StringTargetOutcome))
    (computed : StringComputedInstance)
    (member : computed ∈
      (StringComputationRunView.fromOutcomes input residualMessages outcomes).withChanges) :
    computed ∈
      (StringComputationRunView.fromOutcomes input residualMessages outcomes).withoutErrors := by
  simpa [StringComputationRunView.fromOutcomes] using
    (List.mem_filter.mp member).1

/-- The cleared collection is precisely the source-filled, no-computed-instance projection of the rich outcomes. -/
theorem stringComputationRun_cleared_iff
    (input : CheckedDocument model) (residualMessages : List ResidualMessage)
    (outcomes : List (FieldId × StringTargetOutcome)) (field : FieldId) :
    field ∈
        (StringComputationRunView.fromOutcomes input residualMessages outcomes).cleared ↔
      ∃ outcome, (field, outcome) ∈ outcomes ∧
        StringComputationRunView.shouldClear input (field, outcome) = true := by
  simp [StringComputationRunView.fromOutcomes]

/-- Construction retains the independently supplied residual messages without filtering, rendering, or reclassification. -/
theorem stringComputationRun_formalErrors_exact
    (input : CheckedDocument model) (residualMessages : List ResidualMessage)
    (outcomes : List (FieldId × StringTargetOutcome)) :
    (StringComputationRunView.fromOutcomes input residualMessages outcomes).formalErrorsInOperands =
      residualMessages := by
  rfl

/-- `noErrorOccurred` observes exactly the two error channels; successful changes and clearing are irrelevant. -/
theorem stringComputationRun_noErrorOccurred_iff
    (view : StringComputationRunView ResidualMessage) :
    view.noErrorOccurred = true ↔
      view.withErrors = [] ∧ view.formalErrorsInOperands = [] := by
  simp [StringComputationRunView.noErrorOccurred]

/-- Reordering rich outcomes or residual messages cannot change the extensional public result. -/
theorem stringComputationRun_fromOutcomes_permutation
    (input : CheckedDocument model)
    (firstMessages secondMessages : List ResidualMessage)
    (firstOutcomes secondOutcomes : List (FieldId × StringTargetOutcome))
    (messagesPermutation : firstMessages.Perm secondMessages)
    (outcomesPermutation : firstOutcomes.Perm secondOutcomes) :
    StringComputationRunView.ExtensionalEq
      (StringComputationRunView.fromOutcomes input firstMessages firstOutcomes)
      (StringComputationRunView.fromOutcomes input secondMessages secondOutcomes) := by
  simp only [StringComputationRunView.ExtensionalEq,
    StringComputationRunView.fromOutcomes]
  exact ⟨
    outcomesPermutation.filterMap _,
    (outcomesPermutation.filterMap _).filter _,
    outcomesPermutation.filterMap _,
    (outcomesPermutation.filter _).map _,
    messagesPermutation
  ⟩

end A12Kernel
