import A12Kernel.Elaboration.DateTimeComputation

/-! # Checked `Now` DateTime computation law -/

namespace A12Kernel

/-- Every execution transports that call's exact world instant into the checked target; elaboration retains no earlier sample. -/
theorem dateTimeComputation_transports_now
    (operation : CheckedDateTimeComputation model)
    (world : World) :
    operation.evaluateOutcome world =
      (operation.target.evaluate (.value world.now)).mapError .target := by
  rfl

/-- A value-producing dynamic shift transports that call's exact shifted instant into
    target rendering; elaboration retains no earlier world sample. -/
theorem shiftedNowDateTimeComputation_value
    (operation : CheckedShiftedNowDateTimeComputation model)
    (world : World) (input : CheckedDocument model)
    (localDateTime : LocalDateTime) (instant : Instant) (notGiven : Bool)
    (shift : operation.shift.evaluate .computation world input =
      .ok (.value localDateTime instant notGiven)) :
    operation.evaluateOutcome world input =
      (operation.target.evaluate (.value instant)).mapError .target := by
  unfold CheckedShiftedNowDateTimeComputation.evaluateOutcome
  unfold CheckedShiftedNowDateTimeComputation.evaluateOperand
  rw [shift]
  simp [ValueAsDateTimeResult.asTemporalComputationResult]

/-- Dynamic shift and target certificates select the same model-zone profile. -/
theorem shiftedNowDateTimeComputation_profiles_eq
    (operation : CheckedShiftedNowDateTimeComputation model) :
    operation.shift.profile = operation.target.profile := by
  have selected :
      some operation.shift.profile = some operation.target.profile :=
    operation.shift.profileMatches.symm.trans operation.target.profileMatches
  exact Option.some.inj selected

end A12Kernel
