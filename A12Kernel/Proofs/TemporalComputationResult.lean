import A12Kernel.Elaboration.TemporalComputationResult

/-! # Error-bearing temporal result laws -/

namespace A12Kernel

/-- Original unconverted ingress is filled for clearing but incompatible with every computed typed value (spec/09 §3.3). -/
theorem temporalUnconverted_filled_and_changed [DecidableEq Stored]
    (previous value : Stored) :
    (TemporalTargetState.presentUnconverted previous).storedValue = some previous ∧
      (TemporalTargetState.presentUnconverted previous).computedValue = none ∧
      TemporalValueDelta.projectValue value
        (TemporalTargetState.presentUnconverted previous).toDeltaPrior =
          some (.value value) ∧
      TemporalValueDelta.projectNoValue
        (TemporalTargetState.presentUnconverted previous).toDeltaPrior =
          some .cleared := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Every changed success produced by the shared projection is retained in its complete successful collection. -/
theorem temporalComputationRun_fromErrorOutcomes_withChanges_subset
    (successfulInstance? : Target × Outcome → Option ComputedInstance)
    (computedError? : Target × Outcome → Option ComputedError)
    (sourceValueChanged : ComputedInstance → Bool)
    (shouldClear : Target × Outcome → Bool)
    (messages : List ResidualMessage)
    (outcomes : List (Target × Outcome))
    (computed : ComputedInstance)
    (member : computed ∈
      (TemporalComputationRunView.fromErrorOutcomes successfulInstance?
        computedError? sourceValueChanged shouldClear
        messages outcomes).withChanges) :
    computed ∈
      (TemporalComputationRunView.fromErrorOutcomes successfulInstance?
        computedError? sourceValueChanged shouldClear
        messages outcomes).withoutErrors := by
  simpa [TemporalComputationRunView.fromErrorOutcomes] using
    (List.mem_filter.mp member).1

/-- Clearing is exactly source-filled placement without a computed-data instance. -/
theorem dateRangeComputationRun_shouldClear_iff
    (input : CheckedDocument model) (field : FieldId)
    (outcome : DateRangeTargetOutcome) :
    DateRangeComputationRunView.shouldClear input (field, outcome) = true ↔
      outcome.hasComputedInstance = false ∧
        (input.sourceDateRangeTargetState field).storedValue.isSome = true := by
  simp [DateRangeComputationRunView.shouldClear,
    DateRangeComputationRunView.shouldClearAt]

end A12Kernel
