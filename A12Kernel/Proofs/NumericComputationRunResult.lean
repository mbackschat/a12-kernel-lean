import A12Kernel.Elaboration.NumericComputation.RunResult

/-! # Number computation result-view laws -/

namespace A12Kernel

theorem numericComputationRun_shouldClear_iff
    (entry : SourcedNumericTargetOutcome) :
    NumericComputationRunView.shouldClear entry = true ↔
      entry.outcome.hasComputedInstance = false ∧
        entry.source.sourceIdentity.isSome = true := by
  simp [NumericComputationRunView.shouldClear]

private theorem numericComputationRun_changedInstance_successful
    (entry : SourcedNumericTargetOutcome)
    (computed : NumericComputedInstance)
    (changed :
      NumericComputationRunView.changedInstance? entry = some computed) :
    NumericComputationRunView.successfulInstance? entry = some computed := by
  cases entry with
  | mk target outcome source =>
      cases outcome <;>
        simp_all [NumericComputationRunView.changedInstance?,
          NumericComputationRunView.successfulInstance?]

/-- Every changed success is the identical address-and-payload member of the complete successful collection. -/
theorem numericComputationRun_withChanges_subset
    (residualMessages : List ResidualMessage)
    (entries : List SourcedNumericTargetOutcome)
    (computed : NumericComputedInstance)
    (member : computed ∈
      (NumericComputationRunView.fromSourceOutcomes
        residualMessages entries).withChanges) :
    computed ∈
      (NumericComputationRunView.fromSourceOutcomes
        residualMessages entries).withoutErrors := by
  change computed ∈ entries.filterMap
    NumericComputationRunView.changedInstance? at member
  change computed ∈ entries.filterMap
    NumericComputationRunView.successfulInstance?
  induction entries with
  | nil => simp at member
  | cons entry remaining inductionHypothesis =>
      cases changed :
        NumericComputationRunView.changedInstance? entry with
      | none =>
          simp [changed] at member
          have tailMember : computed ∈ remaining.filterMap
              NumericComputationRunView.changedInstance? :=
            List.mem_filterMap.mpr member
          have tail := inductionHypothesis tailMember
          cases successful :
              NumericComputationRunView.successfulInstance? entry <;>
            simp [successful, tail]
      | some head =>
          have successful :=
            numericComputationRun_changedInstance_successful
              entry head changed
          simp [changed] at member
          simp [successful]
          exact member.elim
            (fun equal => Or.inl equal)
            (fun tail => Or.inr (List.mem_filterMap.mp
              (inductionHypothesis (List.mem_filterMap.mpr tail))))

theorem numericComputationRun_formalErrors_exact
    (residualMessages : List ResidualMessage)
    (entries : List SourcedNumericTargetOutcome) :
    (NumericComputationRunView.fromSourceOutcomes
      residualMessages entries).formalErrorsInOperands = residualMessages := by
  rfl

theorem numericComputationRun_noErrorOccurred_iff
    (view : NumericComputationRunView ResidualMessage) :
    view.noErrorOccurred = true ↔
      view.withErrors = [] ∧ view.formalErrorsInOperands = [] := by
  simp [NumericComputationRunView.noErrorOccurred]

/-- Reordering successfully source-classified outcomes or residual messages cannot change the extensional public result. -/
theorem numericComputationRun_fromSourceOutcomes_permutation
    (firstMessages secondMessages : List ResidualMessage)
    (firstEntries secondEntries : List SourcedNumericTargetOutcome)
    (messagesPermutation : firstMessages.Perm secondMessages)
    (entriesPermutation : firstEntries.Perm secondEntries) :
    NumericComputationRunView.ExtensionalEq
      (NumericComputationRunView.fromSourceOutcomes firstMessages firstEntries)
      (NumericComputationRunView.fromSourceOutcomes secondMessages secondEntries) := by
  exact ⟨
    entriesPermutation.filterMap _,
    entriesPermutation.filterMap _,
    entriesPermutation.filterMap _,
    (entriesPermutation.filter _).map _,
    messagesPermutation
  ⟩

end A12Kernel
