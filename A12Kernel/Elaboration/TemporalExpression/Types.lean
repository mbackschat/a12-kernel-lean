import A12Kernel.Elaboration.ConstructedDateEvaluation
import A12Kernel.Semantics.TemporalExpression
import A12Kernel.Elaboration.TemporalExtremumStream
import A12Kernel.Elaboration.Flat.FieldValueRead
import A12Kernel.Elaboration.ValueAsDateTimeWorldComponents
import A12Kernel.Elaboration.DateRangeBoundComparison

/-! # Scalar temporal expression types

Fields, clocks, typed literals and constructors share the expression tree with extrema, projections
and elapsed or calendar shifts. Date values retain exact instants and calendar provenance through
composition; yearless comparisons additionally retain their declared component key. Storage limits
are applied by the target, after arithmetic (spec/05 and calendar-expression grid, 2026-10-04).
-/

namespace A12Kernel

inductive SurfaceScalarTemporalExpression where
  | field (reference : SurfaceFieldPath)
  | group (source : SurfaceScalarTemporalExpression)
  | extremum (operator : TemporalExtremumOp) (source : SurfaceFieldEntitySource)
  | combine (operator : TemporalExtremumOp)
      (first : SurfaceScalarTemporalExpression) (rest : List SurfaceScalarTemporalExpression)
  | now
  | today
  | dateLiteral (value : FullDate)
  | timeLiteral (value : TimeOfDay)
  | dateTimeLiteral (value : LocalDateTime)
  | rangeBound (reference : SurfaceFieldPath) (bound : DateRangeBound)
  | baseYearBound (bound : BaseYearRangeEndpoint)
  | dateTimeConstruction (date time : SurfaceScalarTemporalExpression)
  | valueAsDate (reference : SurfaceFieldPath) (endpoint : ValueAsDateEndpoint)
  | dateConstruction (components : SurfaceConstructedDateComponents)
  | calendarShift (unit : DateShiftUnit) (source : SurfaceScalarTemporalExpression)
      (amount : AuthoredNumericExpr (Sum SurfaceNumericAtom (TemporalNumericPart × SurfaceScalarTemporalExpression)))
  | timeConstruction (components : TimeComponentPrefix (Sum SurfaceTimeComponent (TimeNumericPart × SurfaceScalarTemporalExpression)))
  | dateFromDateTime (source : SurfaceScalarTemporalExpression)
  | timeFromDateTime (source : SurfaceScalarTemporalExpression)
  | subdayShift (unit : DateTimeSubdayUnit) (source : SurfaceScalarTemporalExpression)
      (amount : AuthoredNumericExpr (Sum SurfaceNumericAtom (TemporalNumericPart × SurfaceScalarTemporalExpression)))

/-- Temporal source slots exclude the grouped comparison and extrema productions; each nested
operation checks its own slot (spec/12 §3, grammar `datumAngabe`/`datumAngabe2`). -/
def SurfaceScalarTemporalExpression.admittedSourceSlot : SurfaceScalarTemporalExpression → Bool
  | .group _ | .extremum _ _ | .combine _ _ _ => false
  | .field _ | .now | .today | .dateLiteral _ | .timeLiteral _ | .dateTimeLiteral _
  | .dateTimeConstruction _ _ | .valueAsDate _ _ | .rangeBound _ _ | .baseYearBound _ | .dateConstruction _ | .calendarShift _ _ _
  | .timeConstruction _ | .dateFromDateTime _ | .timeFromDateTime _ | .subdayShift _ _ _ => true

inductive ScalarTemporalExpressionError where
  | model (error : ResolveError)
  | read (error : ResolveError)
  | extremum (error : TemporalExtremumOperandElabError)
  | amount (error : TemporalShiftAmountElabError)
  | dateComponents (error : ConstructedDateComponentsElabError)
  | timeComponents (error : TimeComponentsElabError)
  | rangeBound (error : YearlessDateRangeBoundElabError)
  | partialDate (error : ValueAsDateZonedElabError)
  | nonTemporal (path : List String)
  | unsupportedSource
  | incompatibleFormats
  deriving Repr, DecidableEq

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

inductive ScalarTemporalEvaluationFault where
  | indexedOperandNotSupported
  | dateTimeLabelUnresolved
  | calendarUnavailable
  deriving Repr, DecidableEq

mutual
inductive ScalarTemporalAtom (model : FlatModel) where
  | field (source : FlatTemporalField)
  | entityExtremum (operator : TemporalExtremumOp) (source : CheckedTemporalExtremumOperands model)
  | fixed (value : ScalarTemporalValue)
  | now
  | today (profile : ModelZone.ConcreteProfile)
  | dateLiteral (profile : ModelZone.ConcreteProfile) (value : FullDate)
  | dateTimeLiteral (profile : ModelZone.ConcreteProfile) (value : LocalDateTime)
  | dateConstruction (components : CheckedConstructedDateComponents model)
  | timeConstruction (components : TimeComponentPrefix (Sum (CheckedTimeComponent model) (ScalarTemporalNumericAtom model)))
  | valueAsDate (source : CheckedZonedValueAsDateSource model)
  | rangeBound (profile : ModelZone.ConcreteProfile) (source : CheckedDateRangeBoundOperand model)
  | baseYearBound (profile : ModelZone.ConcreteProfile) (year : Int) (bound : BaseYearRangeEndpoint)

inductive ScalarTemporalTransform (model : FlatModel) where
  | extremum (operator : TemporalExtremumOp)
  | dateTime (profile : ModelZone.ConcreteProfile)
  | calendarShift (profile : ModelZone.ConcreteProfile)
      (unit : DateShiftUnit) (amount : AuthoredNumericExpr (ScalarTemporalNumericAtom model))
  | dateFromDateTime (profile : ModelZone.ConcreteProfile)
  | timeFromDateTime (profile : ModelZone.ConcreteProfile)
  | subdayShift (profile : ModelZone.ConcreteProfile)
      (unit : DateTimeSubdayUnit) (amount : AuthoredNumericExpr (ScalarTemporalNumericAtom model))

inductive ScalarTemporalNumericAtom (model : FlatModel) where
  | ordinary (source : CheckedTemporalShiftAmount model)
  | projection (part : TemporalNumericPart) (profile : ModelZone.ConcreteProfile)
      (source : TemporalExpressionOf (ScalarTemporalAtom model) (ScalarTemporalTransform model))
end

abbrev ScalarTemporalExpression (model : FlatModel) :=
  TemporalExpressionOf (ScalarTemporalAtom model) (ScalarTemporalTransform model)

/-- Extractor admission follows the source's component set, including its Base Year completion
(spec/05 and the numeric-extractor branch of CheckDatumExtractOpImpl). -/
def TemporalNumericPart.admitsComponents (part : TemporalNumericPart)
    (components : TemporalComponents) (hasBaseYear : Bool) : Bool :=
  match part with
  | .date part => part.admittedBy hasBaseYear components
  | .time part => part.admittedBy components

def TemporalNumericPart.projectScalar (part : TemporalNumericPart) (profile : ModelZone.ConcreteProfile) :
    ScalarTemporalValue → Except ScalarTemporalEvaluationFault Rat
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
def TemporalNumericPart.observeScalar (part : TemporalNumericPart) (profile : ModelZone.ConcreteProfile)
    (source : SimpleComparisonOperand ScalarTemporalValue) : Except ScalarTemporalEvaluationFault
      (Except NumericValidationUnavailable NumericArithmeticOutcome) := do
  match source with
  | .unknown cause => pure (.error (.formal cause))
  | .notEvaluated => pure (.ok (.value 0 .both))
  | .value .nonRelevant _ => pure (.error .nonRelevant)
  | .value .noValue given => pure (.ok (.value 0 (if given then .fixed else .both)))
  | .value value given =>
      pure (.ok (.value (← part.projectScalar profile value) (if given then .fixed else .both)))

end A12Kernel
