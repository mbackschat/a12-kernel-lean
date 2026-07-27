import A12Kernel.Elaboration.FullDateComputation

/-! # Checked full-Date computation laws -/

namespace A12Kernel

/-- A computation-phase empty source remains clean no-value through target execution. -/
theorem fullDateComputation_field_empty
    (operation : CheckedFullDateComputation model)
    (world : World)
    (input : CheckedDocument model)
    (source : FlatTemporalField)
    (operand : operation.operand = .fieldValue source)
    (read :
      input.read { field := source.id, path := [] } = .ok cell)
    (empty :
      observeCell .computation cell = .empty) :
    operation.evaluateOutcome world input = .ok .noValue := by
  have operandRead :
      operation.evaluateOperand world input = .ok .noValue := by
    simp [CheckedFullDateComputation.evaluateOperand,
      operand, read, empty] <;> rfl
  unfold CheckedFullDateComputation.evaluateOutcome
  rw [operandRead]
  rfl

/-- A reached formal source failure preserves its exact cause and never becomes a target error. -/
theorem fullDateComputation_field_poison
    (operation : CheckedFullDateComputation model)
    (world : World)
    (input : CheckedDocument model)
    (source : FlatTemporalField)
    (operand : operation.operand = .fieldValue source)
    (read :
      input.read { field := source.id, path := [] } = .ok cell)
    (poison :
      observeCell .computation cell = .poison cause) :
    operation.evaluateOutcome world input = .ok (.poison cause) := by
  have operandRead :
      operation.evaluateOperand world input = .ok (.poison cause) := by
    simp [CheckedFullDateComputation.evaluateOperand,
      operand, read, poison] <;> rfl
  unfold CheckedFullDateComputation.evaluateOutcome
  rw [operandRead]
  rfl

/-- A checked Date source transports its exact instant to the declaration-owned target; source text, decoded parts, and calendar basis cannot replace target policy. -/
theorem fullDateComputation_field_value
    (operation : CheckedFullDateComputation model)
    (world : World)
    (input : CheckedDocument model)
    (source : FlatTemporalField)
    (operand : operation.operand = .fieldValue source)
    (read :
      input.read { field := source.id, path := [] } = .ok cell)
    (value :
      observeCell .computation cell =
        .value (.temporal (.date instant parts basis))) :
    operation.evaluateOutcome world input =
      (operation.target.evaluate (.value instant)).mapError .target := by
  have operandRead :
      operation.evaluateOperand world input = .ok (.value instant) := by
    simp [CheckedFullDateComputation.evaluateOperand,
      operand, read, value] <;> rfl
  unfold CheckedFullDateComputation.evaluateOutcome
  rw [operandRead]

/-- `Today` is resolved at execution from the supplied world and reaches the same declaration-owned target as a field value. -/
theorem fullDateComputation_today_value
    (operation : CheckedFullDateComputation model)
    (world : World)
    (input : CheckedDocument model)
    (zoneId : String)
    (instant : Instant)
    (operand : operation.operand = .todayValue zoneId)
    (resolved : world.today? zoneId = some instant) :
    operation.evaluateOutcome world input =
      (operation.target.evaluate (.value instant)).mapError .target := by
  have operandRead :
    operation.evaluateOperand world input = .ok (.value instant) := by
    simp [CheckedFullDateComputation.evaluateOperand,
      operand, resolved] <;> rfl
  unfold CheckedFullDateComputation.evaluateOutcome
  rw [operandRead]

/-- A missing model-zone capability is structural failure; `Today` never falls back to UTC or the raw clock instant. -/
theorem fullDateComputation_today_unavailable
    (operation : CheckedFullDateComputation model)
    (world : World)
    (input : CheckedDocument model)
    (zoneId : String)
    (operand : operation.operand = .todayValue zoneId)
    (unsupported : world.today? zoneId = none) :
    operation.evaluateOutcome world input =
      .error (.todayUnavailable zoneId) := by
  have operandRead :
      operation.evaluateOperand world input =
        .error (.todayUnavailable zoneId) := by
    simp [CheckedFullDateComputation.evaluateOperand,
      operand, unsupported] <;> rfl
  unfold CheckedFullDateComputation.evaluateOutcome
  rw [operandRead]

end A12Kernel
