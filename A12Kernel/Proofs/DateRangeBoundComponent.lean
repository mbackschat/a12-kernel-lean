import A12Kernel.Elaboration.DateRangeBoundComponent

/-! # Selected-endpoint numeric component laws

These lock the one claim the component read depends on: it reaches the same endpoint the two
existing endpoint owners reach, and it then applies the established direct-component projection
rather than a second account of emptiness, unavailability, or fillability.
-/

namespace A12Kernel

/-- The cross-carrier endpoint selection and the yearless owner's own selection cannot disagree
about which label an endpoint carries. The two are written independently over the same carriers,
so this is what keeps a component read from silently picking the opposite end. -/
theorem dateRangeCellValue_selectBoundObservation_yearless
    (bound : DateRangeBound) (value : DateRangeCellValue) :
    (match value.selectBoundObservation bound with
      | .yearless selected => some selected
      | .exact _ => none) = value.selectYearlessBound bound := by
  cases value <;> cases bound <;> rfl

/-- An exact carrier reaches the endpoint the comparable-endpoint owner selects, so a component
read and a fixed-Date comparison of the same authored operand read the same end. -/
@[simp] theorem dateRangeCellValue_selectBoundParts_exact
    (bound : DateRangeBound) (range : DateRangeValue) :
    (DateRangeCellValue.exact range).selectBoundParts bound =
      (range.select bound).parts := rfl

/-- The flat validation read factors into the shared range observation followed by the established
direct-component projection. Emptiness, unavailability, and fillability therefore follow from that
owner's laws instead of being restated here. -/
theorem resolveDateRangeBoundNumericOperand_factors
    (context : FlatContext) (source : FlatDateRangeField)
    (bound : DateRangeBound) (part : DateNumericPart)
    (observed : CellObservation DateRangeCellValue)
    (reached : CheckedDateRangeSource.observeRange source.id .validation
      (context.read source.id) = .ok observed) :
    context.resolveDateRangeBoundNumericOperand source bound part =
      part.fromObservation (·.selectBoundParts bound) observed := by
  simp [FlatContext.resolveDateRangeBoundNumericOperand, reached]

/-- A cell whose kind is not a DateRange at all stays formally unavailable. The static gate makes
this unreachable, so it exists to keep a malformed checked document from acquiring a zero. -/
theorem resolveDateRangeBoundNumericOperand_wrongKind
    (context : FlatContext) (source : FlatDateRangeField)
    (bound : DateRangeBound) (part : DateNumericPart) (value : Value)
    (notRange : ∀ range, value ≠ .dateRange range)
    (observed : observeCell .validation (context.read source.id) = .value value) :
    context.resolveDateRangeBoundNumericOperand source bound part =
      .unknown .malformed := by
  unfold FlatContext.resolveDateRangeBoundNumericOperand
  rw [CheckedDateRangeSource.observeRange, observed]
  cases value with
  | dateRange range => exact absurd rfl (notRange range)
  | _ => rfl

end A12Kernel
