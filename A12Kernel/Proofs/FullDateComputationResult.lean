import A12Kernel.Proofs.TemporalComputationResult

/-! # Full-Date computation result-view laws -/

namespace A12Kernel

/-- Clearing is exactly source-filled placement without a computed-data instance. -/
theorem fullDateComputationRun_shouldClear_iff
    (input : CheckedDocument model) (field : FieldId)
    (outcome : FullDateTargetOutcome) :
    FullDateComputationRunView.shouldClear input (field, outcome) = true ↔
      outcome.hasComputedInstance = false ∧
        (input.sourceFullDateTargetState field).storedValue.isSome = true := by
  simp [FullDateComputationRunView.shouldClear,
    FullDateComputationRunView.shouldClearAt]

/-- The nonrepeatable source-state projection is exactly the root-address specialization of the addressed projection. -/
theorem sourceFullDateTargetState_eq_at_root
    (input : CheckedDocument model) (field : FieldId) :
    input.sourceFullDateTargetState field =
      input.sourceFullDateTargetStateAt { field, path := [] } := by
  rfl

/-- The original nonrepeatable constructor remains definitionally the root-key specialization of the exact-key constructor. -/
theorem fullDateComputationRun_fromOutcomes_eq_fromOutcomesAt
    (input : CheckedDocument model) (messages : List ResidualMessage)
    (outcomes : List (FieldId × FullDateTargetOutcome)) :
    FullDateComputationRunView.fromOutcomes input messages outcomes =
      FullDateComputationRunView.fromOutcomesAt
        input.sourceFullDateTargetState messages outcomes := by
  rfl

/-- Every exact-key changed success is retained in the complete successful collection. -/
theorem fullDateComputationRun_fromOutcomesAt_withChanges_subset
    (sourceState : Target → FullDateTargetState)
    (messages : List ResidualMessage)
    (outcomes : List (Target × FullDateTargetOutcome))
    (computed : FullDateComputedInstance Target)
    (member : computed ∈
      (FullDateComputationRunView.fromOutcomesAt sourceState messages outcomes).withChanges) :
    computed ∈
      (FullDateComputationRunView.fromOutcomesAt sourceState messages outcomes).withoutErrors := by
  simpa [FullDateComputationRunView.fromOutcomesAt] using
    temporalComputationRun_fromErrorOutcomes_withChanges_subset
      FullDateComputationRunView.successfulInstance?
      FullDateComputationRunView.computedError?
      (FullDateComputationRunView.sourceValueChangedAt sourceState)
      (FullDateComputationRunView.shouldClearAt sourceState)
      messages outcomes computed member

/-- Every changed success is the identical member of the complete successful collection. -/
theorem fullDateComputationRun_withChanges_subset
    (input : CheckedDocument model) (messages : List ResidualMessage)
    (outcomes : List (FieldId × FullDateTargetOutcome))
    (computed : FullDateComputedInstance)
    (member : computed ∈
      (FullDateComputationRunView.fromOutcomes input messages outcomes).withChanges) :
    computed ∈
      (FullDateComputationRunView.fromOutcomes input messages outcomes).withoutErrors := by
  simpa [FullDateComputationRunView.fromOutcomes,
    FullDateComputationRunView.fromOutcomesAt] using
    temporalComputationRun_fromErrorOutcomes_withChanges_subset
      FullDateComputationRunView.successfulInstance?
      FullDateComputationRunView.computedError?
      (FullDateComputationRunView.sourceValueChangedAt
        input.sourceFullDateTargetState)
      (FullDateComputationRunView.shouldClearAt
        input.sourceFullDateTargetState)
      messages outcomes computed member

/-- The clear collection is precisely the source-filled, no-instance projection. -/
theorem fullDateComputationRun_cleared_iff
    (input : CheckedDocument model) (messages : List ResidualMessage)
    (outcomes : List (FieldId × FullDateTargetOutcome)) (field : FieldId) :
    field ∈
        (FullDateComputationRunView.fromOutcomes input messages outcomes).cleared ↔
      ∃ outcome, (field, outcome) ∈ outcomes ∧
        FullDateComputationRunView.shouldClear input (field, outcome) = true := by
  simp [FullDateComputationRunView.fromOutcomes,
    FullDateComputationRunView.fromOutcomesAt,
    FullDateComputationRunView.shouldClear,
    TemporalComputationRunView.fromErrorOutcomes]

/-- Result construction retains the supplied residual channel exactly. -/
theorem fullDateComputationRun_formalErrors_exact
    (input : CheckedDocument model) (messages : List ResidualMessage)
    (outcomes : List (FieldId × FullDateTargetOutcome)) :
    (FullDateComputationRunView.fromOutcomes input messages outcomes).formalErrorsInOperands =
      messages := by
  rfl

/-- The error predicate observes exactly its two error channels. -/
theorem fullDateComputationRun_noErrorOccurred_iff
    (view : FullDateComputationRunView ResidualMessage) :
  view.noErrorOccurred = true ↔
      view.withErrors = [] ∧ view.formalErrorsInOperands = [] := by
  simp [FullDateComputationRunView.noErrorOccurred,
    TemporalComputationRunView.noErrorOccurred]

/-- Reordering rich outcomes or residual messages preserves the extensional result. -/
theorem fullDateComputationRun_fromOutcomes_permutation
    (input : CheckedDocument model)
    (firstMessages secondMessages : List ResidualMessage)
    (firstOutcomes secondOutcomes : List (FieldId × FullDateTargetOutcome))
    (messagesPermutation : firstMessages.Perm secondMessages)
    (outcomesPermutation : firstOutcomes.Perm secondOutcomes) :
    FullDateComputationRunView.ExtensionalEq
      (FullDateComputationRunView.fromOutcomes input firstMessages firstOutcomes)
      (FullDateComputationRunView.fromOutcomes input secondMessages secondOutcomes) := by
  simp only [FullDateComputationRunView.ExtensionalEq,
    FullDateComputationRunView.fromOutcomes,
    FullDateComputationRunView.fromOutcomesAt,
    TemporalComputationRunView.fromErrorOutcomes]
  exact ⟨
    outcomesPermutation.filterMap _,
    (outcomesPermutation.filterMap _).filter _,
    outcomesPermutation.filterMap _,
    (outcomesPermutation.filter _).map _,
    messagesPermutation
  ⟩

end A12Kernel
