import A12Kernel.Semantics.ScalarTemporalValue
import A12Kernel.Semantics.ConstructedDateDifference

namespace A12Kernel

/-- Computation stops at a formal first operand; validation still reaches the second. The
ordinary/Having direct, shifted and constructed difference controls isolate this order
(docs/sources/temporal-runtime-fold-probes.md#src-recursive-difference-effects). -/
def readTemporalPairWith (phase : Phase) (readFirst : Except Error First)
    (formalCause? : First → Option FormalCause) (readSecond : Unit → Except Error Second) :
    Except Error (Except FormalCause (First × Second)) := do
  let first ← readFirst
  if phase == .computation then
    if let some cause := formalCause? first then return .error cause
  pure (.ok (first, ← readSecond ()))

def readTemporalPair (phase : Phase) (read : Source → Except Error Operand)
    (formalCause? : Operand → Option FormalCause) (left right : Source) :
    Except Error (Except FormalCause (Operand × Operand)) :=
  readTemporalPairWith phase (read left) formalCause? (fun () => read right)

def scalarTemporalFormalCause? : SimpleComparisonOperand ScalarTemporalValue → Option FormalCause
  | .unknown cause => some cause
  | _ => none

def TemporalOperationUnit.admitsScalarDifference (unit : TemporalOperationUnit) (hasBaseYear : Bool)
    (left right : TemporalComponents) : Bool :=
  match unit with
  | .days => CalendarDayDifference.admittedBy left && CalendarDayDifference.admittedBy right &&
      CalendarDayDifference.yearCompatible hasBaseYear left right
  | .months => DateDifferenceUnit.months.compatible hasBaseYear left right
  | .years => DateDifferenceUnit.years.compatible hasBaseYear left right
  | .hours => DateTimeSubdayUnit.hours.compatible left right
  | .minutes => DateTimeSubdayUnit.minutes.compatible left right
  | .seconds => DateTimeSubdayUnit.seconds.compatible left right

private def scalarInstant? : ScalarTemporalValue → Option Instant
  | .date value | .yearless value _ => some value.instant
  | .instant value => some value
  | _ => none

/-- Recursive sources retain exact instants; calendar differences use the existing concrete-profile
owners and sub-day differences use elapsed time (spec/05 §2). -/
def scalarTemporalDifference? (profile : ModelZone.ConcreteProfile) (unit : TemporalOperationUnit)
    (left right : ScalarTemporalValue) : Option Int := do
  let first ← scalarInstant? left
  let second ← scalarInstant? right
  match unit with
  | .hours => pure (first.difference .hours second)
  | .minutes => pure (first.difference .minutes second)
  | .seconds => pure (first.difference .seconds second)
  | .days =>
      match profile with
      | .utc => pure ((second.epochMillis - first.epochMillis).tdiv 86400000)
      | .europeBerlin =>
          let firstLabel ← profile.calendarLabel? first
          let secondLabel ← profile.calendarLabel? second
          profile.differenceResolvedInDays? firstLabel first secondLabel second
  | .months | .years =>
      match profile with
      | .utc =>
          let unit : DateDifferenceUnit := if unit == .months then .months else .years
          unit.betweenLegacy? (← profile.calendarLabel? first).parts (← profile.calendarLabel? second).parts
      | .europeBerlin =>
          let firstLabel ← profile.calendarLabel? first
          let secondLabel ← profile.calendarLabel? second
          if unit == .months then
            EuropeBerlinLegacyProfile.differenceResolvedInMonths? firstLabel first secondLabel second
          else EuropeBerlinLegacyProfile.differenceResolvedInYears? firstLabel first secondLabel second

/-- Operand evaluation precedes this joint observation. Missing payloads contribute zero, while a
present payload with missing provenance retains its computed difference (spec/05 §2). -/
def observeScalarTemporalDifference (profile : ModelZone.ConcreteProfile) (unit : TemporalOperationUnit)
    (left right : SimpleComparisonOperand ScalarTemporalValue)
    (formal : FormalCause → Unavailable) (nonRelevant : Unavailable) :
    Except ScalarTemporalPrimitiveFault (Except Unavailable NumericArithmeticOutcome) := do
  match left, right with
  | .unknown cause, _ | _, .unknown cause => pure (.error (formal cause))
  | .value .nonRelevant _, _ | _, .value .nonRelevant _ => pure (.error nonRelevant)
  | .notEvaluated, _ | _, .notEvaluated => pure (.ok (.value 0 .both))
  | .value first firstGiven, .value second secondGiven =>
      let fillability := if firstGiven && secondGiven then NumericFillability.fixed else .both
      match first, second with
      | .noValue, _ | _, .noValue => pure (.ok (.value 0 fillability))
      | _, _ =>
          let some result := scalarTemporalDifference? profile unit first second | throw .calendarUnavailable
          pure (.ok (.value result fillability))

end A12Kernel
