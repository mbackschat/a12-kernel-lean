import A12Kernel.Semantics.FlatValidation

namespace A12Kernel

/-- A supplied model-zone profile exposes its exact midnight instant to the shared temporal comparison operand. -/
theorem todayOperand_resolves_exact (context : FlatContext) (world : World)
    (zoneId : String) (today : Instant)
    (resolved : world.today? zoneId = some today) :
    (FlatTemporalOperand.todayValue zoneId).resolve
      { context with world := some world } = .value today true := by
  unfold World.today? at resolved
  simp [FlatTemporalOperand.resolve, World.today?, resolved]

/-- An unsupported model-zone id fails closed as unavailable instead of falling back to UTC or `Now`. -/
theorem todayOperand_unsupported (context : FlatContext) (world : World)
    (zoneId : String) (unsupported : world.today? zoneId = none) :
    (FlatTemporalOperand.todayValue zoneId).resolve
      { context with world := some world } = .unknown .malformed := by
  unfold World.today? at unsupported
  simp [FlatTemporalOperand.resolve, World.today?, unsupported]

theorem baseYearOperand_resolves_exact (context : FlatContext) (world : World)
    (zoneId : String) (year : Int) (start : Instant)
    (resolved : world.resolveLocal? zoneId year 1 1 0 0 0 = some start) :
    (FlatTemporalOperand.baseYearValue zoneId year).resolve
      { context with world := some world } = .value start true := by
  unfold World.resolveLocal? at resolved
  simp [FlatTemporalOperand.resolve,
    FlatContext.resolveLocalDateComparisonOperand, baseYearDateParts,
    BaseYearDateSource.parts, World.resolveLocal?, resolved]

theorem baseYearOperand_unsupported (context : FlatContext) (world : World)
    (zoneId : String) (year : Int)
    (unsupported : world.resolveLocal? zoneId year 1 1 0 0 0 = none) :
    (FlatTemporalOperand.baseYearValue zoneId year).resolve
      { context with world := some world } = .unknown .malformed := by
  unfold World.resolveLocal? at unsupported
  simp [FlatTemporalOperand.resolve,
    FlatContext.resolveLocalDateComparisonOperand, baseYearDateParts,
    BaseYearDateSource.parts, World.resolveLocal?, unsupported]

/-- Selecting the range start does not create another Base-Year date meaning: both checked operands resolve the same January 1 label. -/
theorem baseYearRangeStartOperand_eq_baseYearOperand
    (context : FlatContext) (zoneId : String) (year : Int) :
    (FlatTemporalOperand.baseYearRangeValue zoneId year .start).resolve context =
      (FlatTemporalOperand.baseYearValue zoneId year).resolve context := by
  rfl

/-- A supplied model-zone profile receives the selected December 31 label and exposes its exact instant without stored-Date admission. -/
theorem baseYearRangeFinishOperand_resolves_exact
    (context : FlatContext) (world : World) (zoneId : String)
    (year : Int) (finish : Instant)
    (resolved : world.resolveLocal? zoneId year 12 31 0 0 0 = some finish) :
    (FlatTemporalOperand.baseYearRangeValue zoneId year .finish).resolve
      { context with world := some world } = .value finish true := by
  unfold World.resolveLocal? at resolved
  simp [FlatTemporalOperand.resolve,
    FlatContext.resolveLocalDateComparisonOperand, baseYearRangeParts,
    BaseYearDateSource.parts, World.resolveLocal?, resolved]

/-- An unsupported selected range endpoint fails closed instead of falling back to the direct January 1 Base-Year meaning. -/
theorem baseYearRangeOperand_unsupported
    (context : FlatContext) (world : World) (zoneId : String)
    (year : Int) (endpoint : BaseYearRangeEndpoint)
    (unsupported :
      let parts := baseYearRangeParts year endpoint
      world.resolveLocal? zoneId parts.year parts.month parts.day 0 0 0 = none) :
    (FlatTemporalOperand.baseYearRangeValue zoneId year endpoint).resolve
      { context with world := some world } = .unknown .malformed := by
  unfold World.resolveLocal? at unsupported
  simp [FlatTemporalOperand.resolve,
    FlatContext.resolveLocalDateComparisonOperand, World.resolveLocal?, unsupported]

end A12Kernel
