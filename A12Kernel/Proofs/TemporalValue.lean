import A12Kernel.Semantics.FlatValidation

/-! # Admitted temporal payload laws -/

namespace A12Kernel

/-- The same clean checked Date payload supplies exact comparison identity and fixed direct numeric components. -/
theorem flatTemporalDate_projects_instant_and_component
    (context : FlatContext) (field : FlatTemporalField)
    (instant : Instant) (parts : DateParts) (basis : DateCalendarBasis)
    (part : DateNumericPart)
    (kind : field.kind = .date)
    (observed : context.observeValidationAt field.id =
      .value (.temporal (.date instant parts basis))) :
    context.resolveTemporalComparisonOperand field = .value instant true ∧
      context.resolveDateNumericOperand field part =
        .value (part.extract parts) .fixed := by
  simp [FlatContext.resolveTemporalComparisonOperand,
    FlatContext.resolveDateNumericOperand, observed, kind,
    TemporalValue.kind, TemporalValue.instant, TemporalValue.dateParts?]

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
