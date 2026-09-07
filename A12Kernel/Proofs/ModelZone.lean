import A12Kernel.Proofs.BerlinLegacyTimeZone
import A12Kernel.Semantics.FlatValidation
import A12Kernel.Semantics.ModelZone

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

/-- **Fresh-label resolution is injective on every concrete profile**, so within one model zone a
wall label and the exact instant it resolves to determine each other.

    Both arms hold for their own reason. UTC resolves every label and is injective because the label
    is its own coordinate; Europe/Berlin recovers the offset from the resolved instant and reduces to
    the same coordinate law. A wider profile added later must carry its own instance of this proof —
    a resolver that selected an offset without checking it is in force at the resulting instant
    could map two labels onto one instant, and then the two identities below would come apart.

    **Why a consumer cares.** Any value read out of a *cell* has its instant derived from a stored
    wall label, because A12's document form carries a model-format string with no offset and a
    computed value is rendered into that same text before it is stored. So for cell-sourced values,
    comparing exact instants and comparing decoded labels are the **same** relation, and an operator
    such as the temporal distinct count returns the same answer under either account. The two come
    apart only for a value that *retains* an instant a label never produced — a constructed or
    shifted DateTime compared in flight — which is exactly where this project's extrema fixtures
    keep the exact-instant distinction. -/
theorem concreteProfile_resolveLocal_injective
    (profile : ModelZone.ConcreteProfile)
    {left right : LocalDateTime} {instant : Instant}
    (leftResolved : profile.resolveLocal? left = some instant)
    (rightResolved : profile.resolveLocal? right = some instant) :
    left = right := by
  cases profile with
  | utc =>
      simp only [ModelZone.ConcreteProfile.resolveLocal?, Option.some.injEq]
        at leftResolved rightResolved
      exact localDateTime_resolveUtc_injective _ _
        (leftResolved.trans rightResolved.symm)
  | europeBerlin =>
      exact berlinLegacy_resolveLocal_injective leftResolved rightResolved

end A12Kernel
