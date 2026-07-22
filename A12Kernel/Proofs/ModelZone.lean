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
  simp [FlatTemporalOperand.resolve, World.resolveLocal?, resolved]

theorem baseYearOperand_unsupported (context : FlatContext) (world : World)
    (zoneId : String) (year : Int)
    (unsupported : world.resolveLocal? zoneId year 1 1 0 0 0 = none) :
    (FlatTemporalOperand.baseYearValue zoneId year).resolve
      { context with world := some world } = .unknown .malformed := by
  unfold World.resolveLocal? at unsupported
  simp [FlatTemporalOperand.resolve, World.resolveLocal?, unsupported]

end A12Kernel
