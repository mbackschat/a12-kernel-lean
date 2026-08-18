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
    (date : DateValue)
    (value : observeCell .computation cell =
      .value (.temporal (.date date))) :
    operation.evaluateOutcome world input =
      (operation.target.evaluate (.value date.instant)).mapError .target := by
  have operandRead :
      operation.evaluateOperand world input = .ok (.value date.instant) := by
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

/-- Date-typed `BaseYear` exposes the exact model-zone January 1 instant supplied by the explicit capability. -/
theorem fullDateComputation_baseYear_value
    (operation : CheckedFullDateComputation model)
    (world : World)
    (input : CheckedDocument model)
    (zoneId : String)
    (year : Int)
    (instant : Instant)
    (operand :
      operation.operand = .baseYearValue zoneId year)
    (resolved :
      world.resolveLocal? zoneId year 1 1 0 0 0 = some instant) :
    operation.evaluateOutcome world input =
      (operation.target.evaluate (.value instant)).mapError .target := by
  have operandRead :
      operation.evaluateOperand world input = .ok (.value instant) := by
    simp [CheckedFullDateComputation.evaluateOperand,
      operand, resolved] <;> rfl
  unfold CheckedFullDateComputation.evaluateOutcome
  rw [operandRead]

/-- Base Year is model configuration: changing only the world's clock instant cannot change its operand result. -/
theorem fullDateComputation_baseYear_now_irrelevant
    (operation : CheckedFullDateComputation model)
    (world : World)
    (input : CheckedDocument model)
    (zoneId : String)
    (year : Int)
    (now : Instant)
    (operand :
      operation.operand = .baseYearValue zoneId year) :
    operation.evaluateOutcome { world with now } input =
      operation.evaluateOutcome world input := by
  simp [CheckedFullDateComputation.evaluateOutcome,
    CheckedFullDateComputation.evaluateOperand,
    operand, World.resolveLocal?]

/-- Missing model-zone label resolution is structural failure; date-typed Base Year never degrades to the numeric year. -/
theorem fullDateComputation_baseYear_unavailable
    (operation : CheckedFullDateComputation model)
    (world : World)
    (input : CheckedDocument model)
    (zoneId : String)
    (year : Int)
    (operand :
      operation.operand = .baseYearValue zoneId year)
    (unsupported :
      world.resolveLocal? zoneId year 1 1 0 0 0 = none) :
    operation.evaluateOutcome world input =
      .error (.baseYearUnavailable zoneId year) := by
  have operandRead :
      operation.evaluateOperand world input =
        .error (.baseYearUnavailable zoneId year) := by
    simp [CheckedFullDateComputation.evaluateOperand,
      operand, unsupported] <;> rfl
  unfold CheckedFullDateComputation.evaluateOutcome
  rw [operandRead]

/-- A selected Base-Year range endpoint exposes the exact model-zone instant for its January 1 or December 31 label. -/
theorem fullDateComputation_baseYearRange_value
    (operation : CheckedFullDateComputation model)
    (world : World)
    (input : CheckedDocument model)
    (zoneId : String)
    (year : Int)
    (endpoint : BaseYearRangeEndpoint)
    (instant : Instant)
    (operand :
      operation.operand =
        .baseYearRangeValue zoneId year endpoint)
    (resolved :
      let parts := baseYearRangeParts year endpoint
      world.resolveLocal? zoneId
        parts.year parts.month parts.day 0 0 0 = some instant) :
    operation.evaluateOutcome world input =
      (operation.target.evaluate (.value instant)).mapError .target := by
  have operandRead :
      operation.evaluateOperand world input = .ok (.value instant) := by
    simp [CheckedFullDateComputation.evaluateOperand,
      operand, resolved] <;> rfl
  unfold CheckedFullDateComputation.evaluateOutcome
  rw [operandRead]

/-- Base-Year range endpoints are model configuration: changing only the world's clock instant cannot change their result. -/
theorem fullDateComputation_baseYearRange_now_irrelevant
    (operation : CheckedFullDateComputation model)
    (world : World)
    (input : CheckedDocument model)
    (zoneId : String)
    (year : Int)
    (endpoint : BaseYearRangeEndpoint)
    (now : Instant)
    (operand :
      operation.operand =
        .baseYearRangeValue zoneId year endpoint) :
    operation.evaluateOutcome { world with now } input =
      operation.evaluateOutcome world input := by
  simp [CheckedFullDateComputation.evaluateOutcome,
    CheckedFullDateComputation.evaluateOperand,
    operand, World.resolveLocal?]

/-- Missing model-zone label resolution preserves the selected endpoint in structural failure. -/
theorem fullDateComputation_baseYearRange_unavailable
    (operation : CheckedFullDateComputation model)
    (world : World)
    (input : CheckedDocument model)
    (zoneId : String)
    (year : Int)
    (endpoint : BaseYearRangeEndpoint)
    (operand :
      operation.operand =
        .baseYearRangeValue zoneId year endpoint)
    (unsupported :
      let parts := baseYearRangeParts year endpoint
      world.resolveLocal? zoneId
        parts.year parts.month parts.day 0 0 0 = none) :
    operation.evaluateOutcome world input =
      .error (.baseYearRangeUnavailable zoneId year endpoint) := by
  have operandRead :
      operation.evaluateOperand world input =
        .error (.baseYearRangeUnavailable zoneId year endpoint) := by
    simp [CheckedFullDateComputation.evaluateOperand,
      operand, unsupported] <;> rfl
  unfold CheckedFullDateComputation.evaluateOutcome
  rw [operandRead]

end A12Kernel
