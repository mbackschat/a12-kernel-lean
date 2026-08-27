import A12Kernel.Elaboration.TemporalComputationResult

/-! # DateTime computation result-view laws -/

namespace A12Kernel

/-- Clearing is exactly source-filled placement without a computed-data instance. -/
theorem dateTimeComputationRun_shouldClear_iff
    (input : CheckedDocument model) (field : FieldId)
    (outcome : DateTimeTargetOutcome) :
    DateTimeComputationRunView.shouldClear input (field, outcome) = true ↔
      outcome.hasComputedInstance = false ∧
        (input.sourceDateTimeTargetState field).storedValue.isSome =
          true := by
  simp [DateTimeComputationRunView.shouldClear,
    DateTimeComputationRunView.shouldClearAt]

/-- Every changed DateTime success is the identical member of the complete successful collection. -/
theorem dateTimeComputationRun_withChanges_subset
    (input : CheckedDocument model)
    (messages : List ResidualMessage)
    (outcomes : List (FieldId × DateTimeTargetOutcome))
    (computed : DateTimeComputedInstance)
    (member : computed ∈
      (DateTimeComputationRunView.fromOutcomes
        input messages outcomes).withChanges) :
    computed ∈
      (DateTimeComputationRunView.fromOutcomes
        input messages outcomes).withoutErrors := by
  simpa [DateTimeComputationRunView.fromOutcomes,
    DateTimeComputationRunView.fromOutcomesAt,
    TemporalComputationRunView.fromValueOutcomes] using
    (List.mem_filter.mp member).1

/-- The clear collection is precisely the source-filled, no-instance projection. -/
theorem dateTimeComputationRun_cleared_iff
    (input : CheckedDocument model)
    (messages : List ResidualMessage)
    (outcomes : List (FieldId × DateTimeTargetOutcome))
    (field : FieldId) :
    field ∈
        (DateTimeComputationRunView.fromOutcomes
          input messages outcomes).cleared ↔
      ∃ outcome, (field, outcome) ∈ outcomes ∧
        DateTimeComputationRunView.shouldClear
          input (field, outcome) = true := by
  simp [DateTimeComputationRunView.fromOutcomes,
    DateTimeComputationRunView.fromOutcomesAt,
    DateTimeComputationRunView.shouldClear,
    TemporalComputationRunView.fromValueOutcomes]

/-- Result construction retains the supplied residual channel exactly. -/
theorem dateTimeComputationRun_formalErrors_exact
    (input : CheckedDocument model)
    (messages : List ResidualMessage)
    (outcomes : List (FieldId × DateTimeTargetOutcome)) :
    (DateTimeComputationRunView.fromOutcomes
      input messages outcomes).formalErrorsInOperands = messages := by
  rfl

/-- The bounded DateTime error predicate is true exactly when the residual channel is empty; target-local errors are uninhabited. -/
theorem dateTimeComputationRun_noErrorOccurred_iff
    (view : DateTimeComputationRunView ResidualMessage) :
    view.noErrorOccurred = true ↔
      view.formalErrorsInOperands = [] := by
  have noComputedErrors : view.withErrors = [] := by
    cases errorList : view.withErrors with
    | nil => rfl
    | cons error _ => exact nomatch error
  simp [DateTimeComputationRunView.noErrorOccurred,
    TemporalComputationRunView.noErrorOccurred, noComputedErrors]

/-- Reordering DateTime outcomes or residual messages preserves the extensional result. -/
theorem dateTimeComputationRun_fromOutcomes_permutation
    (input : CheckedDocument model)
    (firstMessages secondMessages : List ResidualMessage)
    (firstOutcomes secondOutcomes :
      List (FieldId × DateTimeTargetOutcome))
    (messagesPermutation : firstMessages.Perm secondMessages)
    (outcomesPermutation : firstOutcomes.Perm secondOutcomes) :
    DateTimeComputationRunView.ExtensionalEq
      (DateTimeComputationRunView.fromOutcomes
        input firstMessages firstOutcomes)
      (DateTimeComputationRunView.fromOutcomes
        input secondMessages secondOutcomes) := by
  simp only [DateTimeComputationRunView.ExtensionalEq,
    TemporalComputationRunView.ExtensionalEq,
    DateTimeComputationRunView.fromOutcomes,
    DateTimeComputationRunView.fromOutcomesAt,
    TemporalComputationRunView.fromValueOutcomes]
  exact ⟨
    outcomesPermutation.filterMap _,
    (outcomesPermutation.filterMap _).filter _,
    List.Perm.nil,
    (outcomesPermutation.filter _).map _,
    messagesPermutation
  ⟩

end A12Kernel
