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

/-- A checked DateRange application with admitted unique targets delegates exactly to the established target-state fold over the checked document's source projection. -/
theorem dateRangeComputationRunView_applyToChecked_eq_applyTo
    (view : DateRangeComputationRunView ResidualMessage)
    (destination : CheckedDocument model)
    (unique : FieldId.firstDuplicate? view.actionTargets = none)
    (valid : DateRangeComputationRunView.validateActionTargets model
      view.actionTargets = .ok ()) :
    view.applyToChecked destination =
      view.applyTo destination.sourceDateRangeTargetState := by
  simp [DateRangeComputationRunView.applyToChecked, unique, valid]
  rfl

end A12Kernel
