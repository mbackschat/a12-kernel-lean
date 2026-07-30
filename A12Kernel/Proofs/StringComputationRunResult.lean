import A12Kernel.Elaboration.StringComputationRunResult

/-! # String computation result-view laws

The public collections are extensional over any exact target-key domain. These laws expose successful-instance inclusion, exact source-relative clearing, and the independent two-error-channel predicate.
-/

namespace A12Kernel

/-- A String target is classified as cleared exactly when it was source-filled and execution produced no computed-data instance. -/
theorem stringComputationRun_shouldClear_iff
    (entry : SourcedStringTargetOutcome Target) :
    StringComputationRunView.shouldClear entry = true ↔
      entry.outcome.hasComputedInstance = false ∧
        entry.source.storedValue.isSome = true := by
  simp [StringComputationRunView.shouldClear]

/-- Every changed success is the identical address-and-payload member of the complete successful collection. -/
theorem stringComputationRun_withChanges_subset
    (residualMessages : List ResidualMessage)
    (entries : List (SourcedStringTargetOutcome Target))
    (computed : StringComputedInstance Target)
    (member : computed ∈
      (StringComputationRunView.fromSourcedOutcomes
        residualMessages entries).withChanges) :
    computed ∈
      (StringComputationRunView.fromSourcedOutcomes
        residualMessages entries).withoutErrors := by
  simp only [StringComputationRunView.fromSourcedOutcomes,
    List.mem_filterMap] at member ⊢
  rcases member with ⟨entry, entryMember, changed⟩
  refine ⟨entry, entryMember, ?_⟩
  cases success : StringComputationRunView.successfulInstance? entry with
  | none =>
      simp [StringComputationRunView.changedInstance?, success] at changed
  | some current =>
      by_cases same : entry.source.storedValue = some current.value
      · simp [StringComputationRunView.changedInstance?, success, same] at changed
      · simp [StringComputationRunView.changedInstance?, success, same] at changed
        subst computed
        rfl

/-- The cleared collection is precisely the source-filled, no-computed-instance projection of the sourced outcomes. -/
theorem stringComputationRun_cleared_iff
    (residualMessages : List ResidualMessage)
    (entries : List (SourcedStringTargetOutcome Target)) (target : Target) :
    target ∈
        (StringComputationRunView.fromSourcedOutcomes
          residualMessages entries).cleared ↔
      ∃ entry, entry ∈ entries ∧ entry.targetField = target ∧
        StringComputationRunView.shouldClear entry = true := by
  simp [StringComputationRunView.fromSourcedOutcomes,
    and_left_comm, and_comm]

/-- Construction retains independently supplied residual messages without filtering, rendering, or reclassification. -/
theorem stringComputationRun_formalErrors_exact
    (residualMessages : List ResidualMessage)
    (entries : List (SourcedStringTargetOutcome Target)) :
    (StringComputationRunView.fromSourcedOutcomes
      residualMessages entries).formalErrorsInOperands = residualMessages := by
  rfl

/-- `noErrorOccurred` observes exactly the two error channels; successful changes and clearing are irrelevant. -/
theorem stringComputationRun_noErrorOccurred_iff
    (view : StringComputationRunView ResidualMessage Target) :
    view.noErrorOccurred = true ↔
      view.withErrors = [] ∧ view.formalErrorsInOperands = [] := by
  simp [StringComputationRunView.noErrorOccurred]

/-- Reordering sourced outcomes or residual messages cannot change the extensional public result. -/
theorem stringComputationRun_fromOutcomes_permutation
    (firstMessages secondMessages : List ResidualMessage)
    (firstEntries secondEntries : List (SourcedStringTargetOutcome Target))
    (messagesPermutation : firstMessages.Perm secondMessages)
    (entriesPermutation : firstEntries.Perm secondEntries) :
    StringComputationRunView.ExtensionalEq
      (StringComputationRunView.fromSourcedOutcomes firstMessages firstEntries)
      (StringComputationRunView.fromSourcedOutcomes secondMessages secondEntries) := by
  simp only [StringComputationRunView.ExtensionalEq,
    StringComputationRunView.fromSourcedOutcomes]
  exact ⟨
    entriesPermutation.filterMap _,
    entriesPermutation.filterMap _,
    entriesPermutation.filterMap _,
    (entriesPermutation.filter _).map _,
    messagesPermutation
  ⟩

end A12Kernel
