import A12Kernel.Semantics.DateConstructionNumeric
import A12Kernel.Semantics.DateTime
import A12Kernel.Semantics.Observation

/-! # Typed Date, DateTime and DateRange numeric-component projection

This capsule consumes an already phase-classified typed Date or DateTime observation for `DayFromDate`, `MonthFromDate`, `QuarterFromDate`, or `YearFromDate`. Present values expose the selected component as fixed. Empty input substitutes numeric zero with symmetric fillability, while formal unavailability preserves its exact cause.

DateTime extraction deliberately projects its Date component and ignores the clock. Concrete parsing, authored source admission, partial-Date completion, the heterogeneous flat context, arithmetic composition, computation reads, and target application remain outside.
-/

namespace A12Kernel

namespace DateNumericPart

/-- Static format admission for one direct date-component extractor. Base Year supplements only the year component. Partial-known Date policy is an earlier model fact outside this flat declaration fragment. -/
def admittedBy (part : DateNumericPart) (hasBaseYear : Bool)
    (components : TemporalComponents) : Bool :=
  match part with
  | .day => components.day
  | .month | .quarter => components.month
  | .year => components.year || hasBaseYear

/-- Apply the shared validation-phase empty/unavailable projection before selecting a date component. The caller supplies the already-admitted value's calendar parts. -/
def fromObservation (part : DateNumericPart) (partsOf : α → DateParts) :
    CellObservation α → NumericOperand :=
  symmetricValidationNumericOperand
    (fun value => part.extract (partsOf value))

/-- Select a numeric component from a typed full-Date validation observation. -/
def fromFullDateObservation (part : DateNumericPart) :
    CellObservation FullDate → NumericOperand :=
  part.fromObservation (·.civil.parts)

/-- Select a numeric date component from a typed DateTime validation observation, ignoring its clock. -/
def fromDateTimeObservation (part : DateNumericPart) :
    CellObservation LocalDateTime → NumericOperand :=
  part.fromObservation (·.date.civil.parts)

end DateNumericPart

/-- One extracted endpoint of a yearless range: only the labels the declaration retains. -/
inductive YearlessDateRangeBoundValue where
  | month (month : Nat)
  | monthDay (value : MonthDayValue)
  deriving Repr, DecidableEq

/-- Project the retained labels into the shared calendar-part carrier. An absent component is
the literal zero a partially known Date uses; the static component gate keeps it unobservable. -/
def YearlessDateRangeBoundValue.parts : YearlessDateRangeBoundValue → DateParts
  | .month value => { year := 0, month := value, day := 0 }
  | .monthDay value => { year := 0, month := value.month, day := value.day }

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

/-- Project a typed endpoint observation with symmetric validation fillability. Keyed reads consume
this clause directly; `resolveDateRangeBoundNumericOperand_factors` proves the ordinary heterogeneous
read agrees with it, including empty and unavailable observations. -/
def DateNumericPart.fromDateRangeBoundObservation (part : DateNumericPart)
    (bound : DateRangeBound) :
    CellObservation DateRangeCellValue → NumericOperand :=
  part.fromObservation (·.selectBoundParts bound)

/-- Keep the declared endpoint labels and ordinary component fillability (spec/05); a wrong cell kind stays malformed. -/
def CellObservation.asDateRangeBoundNumericOperand (bound : DateRangeBound) (part : DateNumericPart) :
    CellObservation → NumericOperand
  | .empty => .value 0 .both
  | .value (.dateRange rangeValue) => .value (part.extract (rangeValue.selectBoundParts bound)) .fixed
  | .value _ => .unknown .malformed
  | .unknown cause | .poison cause => .unknown cause

end A12Kernel
