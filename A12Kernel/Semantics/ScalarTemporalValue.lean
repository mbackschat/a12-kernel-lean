import A12Kernel.Semantics.DateAggregate
import A12Kernel.Semantics.DateTimeAggregate
import A12Kernel.Semantics.TimeAggregate
import A12Kernel.Semantics.LegacyCalendarExpression
import A12Kernel.Semantics.FlatValidation
import A12Kernel.Semantics.NumericExpression

namespace A12Kernel

inductive ScalarTemporalValue where
  /-- Payload absence and non-relevance are independent of the enclosing operand's missing flag.
  Date, Time and DateTime constructors share this domain (stamp-construction grid, 2026-10-04). -/
  | noValue
  | nonRelevant
  | date (value : DateValue)
  | yearless (value : DateValue) (key : MonthDayValue)
  | time (value : TimeOfDay)
  | instant (value : Instant)
  deriving Repr, DecidableEq

namespace ScalarTemporalValue

def select (operator : TemporalExtremumOp) : ScalarTemporalValue → ScalarTemporalValue → ScalarTemporalValue
  | .nonRelevant, _ | _, .nonRelevant => .nonRelevant
  | .noValue, right => right
  | left, .noValue => left
  | .date left, .date right =>
      .date (match operator with
        | .minimum => if right.instant.epochMillis < left.instant.epochMillis then right else left
        | .maximum => if left.instant.epochMillis < right.instant.epochMillis then right else left)
  | .yearless left leftKey, .yearless right rightKey =>
      match operator with
      | .minimum => if rightKey.before leftKey then .yearless right rightKey else .yearless left leftKey
      | .maximum => if leftKey.before rightKey then .yearless right rightKey else .yearless left leftKey
  | .time left, .time right => .time (operator.selectTime left right)
  | .instant left, .instant right => .instant (operator.selectInstant left right)
  | left, _ => left

def holds (operator : TemporalComparisonOp) : ScalarTemporalValue → ScalarTemporalValue → Bool
  | .date left, .date right => operator.holdsInstant left.instant right.instant
  | .yearless _ left, .yearless _ right => operator.holdsMonthDay left right
  | .time left, .time right => operator.holdsTime left right
  | .instant left, .instant right => operator.holdsInstant left right
  | _, _ => false

end ScalarTemporalValue

inductive ScalarTemporalPrimitiveFault where
  | calendarUnavailable
  | dateTimeLabelUnresolved
  deriving Repr, DecidableEq

private def liftScalarTemporal (wrap : α → ScalarTemporalValue) :
    SimpleComparisonOperand α → SimpleComparisonOperand ScalarTemporalValue
  | .value value given => .value (wrap value) given
  | .notEvaluated => .notEvaluated
  | .unknown cause => .unknown cause

/-- Preserve each declaration's precision before model Base Year completion (LF163). Both direct
and expanded operands use this projection, so a row-set cannot borrow another field's components. -/
def projectScalarTemporalObservationWith (baseYear : Option Int) (profile : Option ModelZone.ConcreteProfile)
    (field : FlatTemporalField)
    (observation : CellObservation) : SimpleComparisonOperand ScalarTemporalValue :=
  let components := if field.components.hasDate then field.components.withBaseYear baseYear.isSome else field.components
  if components == TemporalComponents.now then
    liftScalarTemporal .instant observation.asDateTimeExtremumOperand
  else if components == TemporalComponents.time then
    liftScalarTemporal .time observation.asTimeExtremumOperand
  else if components.year then
    match observation with
    | .empty => .notEvaluated
    | .unknown cause | .poison cause => .unknown cause
    | .value (.temporal (.date stored)) =>
        let (year, month, day) := maskedDateComponents field.components baseYear stored.parts
        let parts : DateParts := { year, month, day }
        if stored.parts == parts then .value (.date stored) true
        else match profile.bind
            (fun profile => profile.resolveCompletedDateParts? parts) with
          | some value => .value (.date value) true
          | none => .unknown .malformed
    | _ => .unknown .malformed
  else match observation.asYearlessDateExtremumOperand field.components, observation with
    | .value key given, .value (.temporal (.date value)) => .value (.yearless value key) given
    | .notEvaluated, _ => .notEvaluated
    | .unknown cause, _ => .unknown cause
    | _, _ => .unknown .malformed

def TemporalNumericPart.admitsComponents (part : TemporalNumericPart)
    (components : TemporalComponents) (hasBaseYear : Bool) : Bool :=
  match part with
  | .date part => part.admittedBy hasBaseYear components
  | .time part => part.admittedBy components

def TemporalNumericPart.projectScalarCore (part : TemporalNumericPart) (profile : ModelZone.ConcreteProfile) :
    ScalarTemporalValue → Except ScalarTemporalPrimitiveFault Rat
  | .date value | .yearless value _ =>
      match part with
      | .date part => pure (part.extract value.parts)
      | .time _ => throw .calendarUnavailable
  | .time value =>
      match part with
      | .time part => pure (part.extract value)
      | .date _ => throw .calendarUnavailable
  | .instant instant => do
      let some label := profile.calendarLabel? instant | throw .calendarUnavailable
      match part with
      | .date part => pure (part.extract label.parts)
      | .time part => pure (part.extract label.time)
  | .noValue | .nonRelevant => throw .calendarUnavailable

/-- The Kernel's numeric extraction preserves non-relevance and symmetric missingness separately
from the projected amount (BedingungsOperatorHelper.getDatumsTeil; recursive-temporal grid, 2026-10-04).
A missing payload contributes zero, while a formally unavailable source keeps its cause. -/
def TemporalNumericPart.observeScalarCore (part : TemporalNumericPart) (profile : ModelZone.ConcreteProfile)
    (source : SimpleComparisonOperand ScalarTemporalValue)
    (formal : FormalCause → Unavailable) (nonRelevant : Unavailable) : Except ScalarTemporalPrimitiveFault
      (Except Unavailable NumericArithmeticOutcome) := do
  match source with
  | .unknown cause => pure (.error (formal cause))
  | .notEvaluated => pure (.ok (.value 0 .both))
  | .value .nonRelevant _ => pure (.error nonRelevant)
  | .value .noValue given => pure (.ok (.value 0 (if given then .fixed else .both)))
  | .value value given =>
      pure (.ok (.value (← part.projectScalarCore profile value) (if given then .fixed else .both)))

inductive ScalarTemporalConstructorOp where
  | dateTime
  | dateFromDateTime
  | timeFromDateTime
  deriving Repr, DecidableEq

/-- Resolve already-read constructor arguments without collapsing payload absence, formal
unavailability or the retained instant (spec/05; stamp-construction grid, 2026-10-04). -/
def ScalarTemporalConstructorOp.apply (operation : ScalarTemporalConstructorOp)
    (profile : ModelZone.ConcreteProfile) (operands : List (SimpleComparisonOperand ScalarTemporalValue)) :
    Except ScalarTemporalPrimitiveFault (SimpleComparisonOperand ScalarTemporalValue) := do
  match operation, operands with
  | .dateTime, [date, time] =>
      match date, time with
      | .unknown cause, _ | _, .unknown cause => pure (.unknown cause)
      | .value .nonRelevant _, _ | _, .value .nonRelevant _ => pure (.value .nonRelevant true)
      | .value (.date date) dateGiven, .value (.time time) timeGiven => do
          let some label := profile.calendarLabel? date.instant | throw .calendarUnavailable
          let instant := profile.resolveCalendarLabel? { label with time }
          pure (.value (instant.map ScalarTemporalValue.instant |>.getD .noValue) (dateGiven && timeGiven))
      | .notEvaluated, _ | _, .notEvaluated | .value .noValue _, _ | _, .value .noValue _ =>
          let given : SimpleComparisonOperand ScalarTemporalValue → Bool
            | .value _ given => given
            | _ => false
          pure (.value .noValue (given date && given time))
      | _, _ => throw .calendarUnavailable
  | .dateFromDateTime, [source] =>
      match source with
      | .value (.instant instant) given =>
          let some label := profile.calendarLabel? instant | throw .calendarUnavailable
          let midnight := { label with time := { hour := 0, minute := 0, second := 0, valid := by decide } }
          let some instant := profile.resolveCalendarLabel? midnight | throw .dateTimeLabelUnresolved
          pure (.value (.date { instant, parts := label.parts, basis := .legacyHybrid }) given)
      | .value .noValue given => pure (.value .noValue given)
      | .value .nonRelevant _ => pure (.value .nonRelevant true)
      | .notEvaluated => pure .notEvaluated
      | .unknown cause => pure (.unknown cause)
      | _ => throw .calendarUnavailable
  | .timeFromDateTime, [source] =>
      match source with
      | .value (.instant instant) given =>
          let some label := profile.calendarLabel? instant | throw .calendarUnavailable
          pure (.value (.time label.time) given)
      | .value .noValue given => pure (.value .noValue given)
      | .value .nonRelevant _ => pure (.value .nonRelevant true)
      | .notEvaluated => pure .notEvaluated
      | .unknown cause => pure (.unknown cause)
      | _ => throw .calendarUnavailable
  | _, _ => throw .calendarUnavailable

end A12Kernel
