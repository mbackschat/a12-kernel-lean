import A12Kernel.Elaboration.TemporalErroredComputationApplication

/-! # Error-bearing temporal application laws -/

namespace A12Kernel

theorem temporalComputationDestination_update_same
    (destination : TemporalComputationDestination Stored)
    (target : FieldId) (state : TemporalTargetState Stored) :
    TemporalComputationDestination.update destination target state target = state := by
  simp [TemporalComputationDestination.update]

theorem temporalComputationDestination_applyRetainedClear_same
    (destination : TemporalComputationDestination Stored)
    (target : FieldId) :
    TemporalComputationDestination.applyRetainedClear destination target target =
      .presentEmpty := by
  simp [TemporalComputationDestination.applyRetainedClear,
    TemporalComputationDestination.update,
    TemporalTargetState.applyRetainedClear]
  cases destination target <;> rfl

theorem temporalComputationDestination_applyRetainedClear_other
    (destination : TemporalComputationDestination Stored)
    (target other : FieldId) (different : other ≠ target) :
    TemporalComputationDestination.applyRetainedClear destination target other =
      destination other := by
  simp [TemporalComputationDestination.applyRetainedClear,
    TemporalComputationDestination.update, different]

/-- A DateRange retained clear preserves every unrelated destination field. -/
theorem dateRangeComputationDestination_applyRetainedClear_other
    (destination : DateRangeComputationDestination)
    (target other : FieldId) (different : other ≠ target) :
    destination.applyRetainedClear target other = destination other := by
  simpa [DateRangeComputationDestination.applyRetainedClear] using
    temporalComputationDestination_applyRetainedClear_other
      destination target other different

end A12Kernel
