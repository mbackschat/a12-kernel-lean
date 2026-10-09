import A12Kernel.Elaboration.YearlessDateRangeBound

/-! # Numeric Date components of a selected DateRange endpoint

`DayFromDate`, `MonthFromDate`, `QuarterFromDate`, and `YearFromDate` accept a selected
DateRange endpoint as their source, producing a number rather than a verdict. The two endpoint
owners retain different runtime carriers — an exact range yields a complete Date, an
unconfigured yearless one yields only the labels its declaration keeps — yet a component read
treats them uniformly, because both expose the same calendar-part view.

Interpreted endpoints expose full-Date components. Uninterpreted endpoints use the declaration's
own component set supplemented by Base Year: an unconfigured month range exposes month and
quarter while refusing day and year. Locus admission, arithmetic composition, and the comparison
consumers remain with their existing owners.
-/

namespace A12Kernel

/-- Whether one DateRange declaration exposes the requested date component at its selected endpoint.
Interpreted declarations expose a full Date; otherwise the declared component set and Base Year
decide (spec/05 §8). -/
def FlatModel.exposesDateRangeBoundPart (model : FlatModel)
    (field : FlatDateRangeField) (part : DateNumericPart) : Bool :=
  match model.lookupUniqueId field.id with
  | .ok declaration =>
      match (certifyDateRangeInputField declaration).toOption with
      | some checked =>
          part.admittedBy model.hasBaseYear (checked.policy.endpointComponents checked.format)
      | none => false
  | .error _ => false

/-- Read one certified endpoint's numeric Date component through the heterogeneous flat validation
context. Empty substitutes symmetric zero and formal unavailability keeps its exact cause, which is
the established direct-component account; only a cell whose kind is not a DateRange at all stays
malformed. -/
def FlatContext.resolveDateRangeBoundNumericOperand (context : FlatContext)
    (source : FlatDateRangeField) (bound : DateRangeBound)
    (part : DateNumericPart) : NumericOperand :=
  (observeCell .validation (context.read source.id)).asDateRangeBoundNumericOperand bound part

end A12Kernel
