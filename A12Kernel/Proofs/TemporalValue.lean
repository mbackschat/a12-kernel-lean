import A12Kernel.Semantics.FlatValidation
import A12Kernel.Semantics.DateRangeOverlap
import A12Kernel.Elaboration.FullDateInput

/-! # Admitted temporal payload laws -/

namespace A12Kernel

/-- The same clean checked Date payload supplies exact comparison identity and fixed direct numeric components. -/
theorem flatTemporalDate_projects_instant_and_component
    (context : FlatContext) (field : FlatTemporalField)
    (date : DateValue)
    (part : DateNumericPart)
    (kind : field.kind = .date)
    (observed : context.observeValidationAt field.id =
      .value (.temporal (.date date))) :
    context.resolveTemporalComparisonOperand field = .value date.instant true ∧
      context.resolveDateNumericOperand field part =
        .value (part.extract date.parts) .fixed := by
  simp [FlatContext.resolveTemporalComparisonOperand,
    FlatContext.resolveDateNumericOperand, observed, kind,
    TemporalValue.kind, TemporalValue.instant, TemporalValue.dateParts?]

/-- The universal range reaches the established resolved range whenever both endpoint projections succeed. -/
theorem dateRangeValue_toResolvedDateRange_of_endpoints
    (value : DateRangeValue) (start finish : FullDate)
    (startResolved : value.start.toFullDate? = some start)
    (finishResolved : value.finish.toFullDate? = some finish) :
    value.toResolvedDateRange? = some { start, finish } := by
  simp [DateRangeValue.toResolvedDateRange?, startResolved, finishResolved]

/-- Every successfully resolved stored Date retains the exact decoded components and stored-Gregorian provenance supplied by the input boundary. -/
theorem resolveStoredDate_identity
    (profile : ModelZone.ConcreteProfile) (date : CivilDate)
    (value : DateValue)
    (resolved : profile.resolveStoredDate? date = some value) :
    value.parts = date.parts ∧ value.basis = .storedGregorian := by
  unfold ModelZone.ConcreteProfile.resolveStoredDate? at resolved
  change (FullDate.ofCivil? date).bind (fun full =>
    (LocalDateTime.ofDateHms? full 0 0 0).bind (fun localDateTime =>
      (profile.resolveLocal? localDateTime).bind fun instant => some {
        instant, parts := date.parts, basis := .storedGregorian })) = some value at resolved
  simp only [Option.bind_eq_some_iff, Option.some.injEq] at resolved
  rcases resolved with ⟨_, _, _, _, _, _, rfl⟩
  simp

/-- The same clean checked DateTime payload supplies exact comparison identity and both fixed numeric component families. -/
theorem flatTemporalDateTime_projects_all_consumers
    (context : FlatContext) (field : FlatTemporalField)
    (instant : Instant) (date : DateParts) (time : TimeOfDay)
    (basis : DateCalendarBasis) (datePart : DateNumericPart)
    (timePart : TimeNumericPart)
    (kind : field.kind = .dateTime)
    (observed : context.observeValidationAt field.id =
      .value (.temporal (.dateTime instant date time basis))) :
    context.resolveTemporalComparisonOperand field = .value instant true ∧
      context.resolveDateNumericOperand field datePart =
        .value (datePart.extract date) .fixed ∧
      context.resolveTimeNumericOperand field timePart =
        .value (timePart.extract time) .fixed := by
  simp [FlatContext.resolveTemporalComparisonOperand,
    FlatContext.resolveDateNumericOperand,
    FlatContext.resolveTimeNumericOperand, observed, kind,
    TemporalValue.kind, TemporalValue.instant, TemporalValue.dateParts?,
    TemporalValue.time?]

end A12Kernel
