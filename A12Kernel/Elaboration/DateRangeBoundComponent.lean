import A12Kernel.Elaboration.YearlessDateRangeBound

/-! # Numeric Date components of a selected DateRange endpoint

`DayFromDate`, `MonthFromDate`, `QuarterFromDate`, and `YearFromDate` accept a selected
DateRange endpoint as their source, producing a number rather than a verdict. The two endpoint
owners retain different runtime carriers — an exact range yields a complete Date, an
unconfigured yearless one yields only the labels its declaration keeps — yet a component read
treats them uniformly, because both expose the same calendar-part view.

The static gate is therefore the declaration's own component set supplemented by the model's
Base Year, exactly as it is for a direct Date field, and *not* the exact-value gate that a
comparable endpoint carries: an unconfigured yearless month range exposes month and quarter
while refusing day and year. Locus admission, arithmetic composition, and the comparison
consumers remain with their existing owners.
-/

namespace A12Kernel

/-- One endpoint selected from whichever runtime carrier its declaration produced. -/
inductive DateRangeBoundObservation where
  | exact (value : DateValue)
  | yearless (value : YearlessDateRangeBoundValue)
  deriving Repr, DecidableEq

/-- The calendar-part view both endpoint carriers expose. A yearless carrier's absent labels are
the same literal zeroes a partially known Date uses, and the static component gate is what keeps
them unobservable. -/
def DateRangeBoundObservation.parts : DateRangeBoundObservation → DateParts
  | .exact value => value.parts
  | .yearless value => value.parts

/-- Every runtime carrier selects an endpoint, so a component read needs no profile refusal of its
own. `dateRangeCellValue_selectBoundObservation_yearless` locks this against the yearless owner's
own selection. -/
def DateRangeCellValue.selectBoundObservation (bound : DateRangeBound) :
    DateRangeCellValue → DateRangeBoundObservation
  | .exact value => .exact (value.select bound)
  | .yearlessMonth start finish =>
      .yearless (.month (match bound with | .start => start | .finish => finish))
  | .yearlessMonthDay start finish =>
      .yearless
        (.monthDay (match bound with | .start => start | .finish => finish))

/-- The selected endpoint's calendar parts, independent of which carrier supplied them. -/
def DateRangeCellValue.selectBoundParts (value : DateRangeCellValue)
    (bound : DateRangeBound) : DateParts :=
  (value.selectBoundObservation bound).parts

/-- The one component clause every read route shares: select the requested endpoint from whichever
carrier the declaration produced, then apply the symmetric validation projection. Routing the direct
and the keyed read through this makes their agreement structural rather than a proved coincidence. -/
def DateNumericPart.fromDateRangeBoundObservation (part : DateNumericPart)
    (bound : DateRangeBound) :
    CellObservation DateRangeCellValue → NumericOperand :=
  part.fromObservation (·.selectBoundParts bound)

/-- Whether one DateRange declaration exposes the requested date component at its selected endpoint.
The declared profile's own component set decides, with the model's Base Year supplementing the year
exactly as it does for a direct Date field. -/
def FlatModel.exposesDateRangeBoundPart (model : FlatModel)
    (field : FlatDateRangeField) (part : DateNumericPart) : Bool :=
  match model.lookupUniqueId field.id with
  | .ok declaration =>
      match (certifyDateRangeInputField declaration).toOption with
      | some checked =>
          part.admittedBy model.hasBaseYear checked.format.components
      | none => false
  | .error _ => false

/-- Read one certified endpoint's numeric Date component through the heterogeneous flat validation
context. Empty substitutes symmetric zero and formal unavailability keeps its exact cause, which is
the established direct-component account; only a cell whose kind is not a DateRange at all stays
malformed. -/
def FlatContext.resolveDateRangeBoundNumericOperand (context : FlatContext)
    (source : FlatDateRangeField) (bound : DateRangeBound)
    (part : DateNumericPart) : NumericOperand :=
  match CheckedDateRangeSource.observeRange source.id .validation
      (context.read source.id) with
  | .error _ => .unknown .malformed
  | .ok observed => part.fromDateRangeBoundObservation bound observed

end A12Kernel
