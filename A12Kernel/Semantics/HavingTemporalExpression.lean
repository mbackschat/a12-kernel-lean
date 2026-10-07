import A12Kernel.Semantics.CorrelationContext
import A12Kernel.Semantics.ScalarTemporalValue
import A12Kernel.Semantics.TemporalExpression

namespace A12Kernel

/-- Each temporal-tree read retains its declared carrier as well as its capture origin. -/
structure HavingTemporalExpressionRef where
  origin : HavingOrigin
  source : Sum FlatTemporalField (FlatDateRangeField × TemporalComponents)
  deriving Repr, DecidableEq

def HavingTemporalExpressionRef.fieldId (reference : HavingTemporalExpressionRef) : FieldId :=
  match reference.source with | .inl field => field.id | .inr (field, _) => field.id

inductive HavingTemporalAtom where
  | field (reference : HavingTemporalRef)
  | rangeBound (origin : HavingOrigin) (source : FlatDateRangeField) (components : TemporalComponents) (bound : DateRangeBound)
  | dateLiteral (value : FullDate) (yearPresent : Bool)
  | timeLiteral (value : TimeOfDay)
  | dateTimeLiteral (value : LocalDateTime)
  | today
  | now
  | baseYearBound (bound : BaseYearRangeEndpoint)
  deriving Repr, DecidableEq

structure HavingTemporalExpression where
  core : TemporalExpressionOf HavingTemporalAtom ScalarTemporalConstructorOp
  profile : ModelZone.ConcreteProfile
  baseYear : Option Int
  grouped : Bool := false
  deriving Repr, DecidableEq

namespace HavingTemporalExpression

def references (source : HavingTemporalExpression) : List HavingTemporalExpressionRef :=
  source.core.atoms.filterMap fun
    | .field reference => some { origin := reference.origin, source := .inl reference.field }
    | .rangeBound origin field components _ => some { origin, source := .inr (field, components) }
    | _ => none

def componentsWith (baseYear : Option Int) :
    TemporalExpressionOf HavingTemporalAtom ScalarTemporalConstructorOp → Option TemporalComponents
  | .atom atom => match atom with
      | .field reference => some (if reference.field.components.hasDate then
          reference.field.components.withBaseYear baseYear.isSome else reference.field.components)
      | .rangeBound _ _ components _ => some (components.withBaseYear baseYear.isSome)
      | .dateLiteral _ yearPresent => some ({ TemporalComponents.fullDate with year := yearPresent }.withBaseYear baseYear.isSome)
      | .timeLiteral _ => some TemporalComponents.time
      | .dateTimeLiteral _ | .now => some TemporalComponents.now
      | .today | .baseYearBound _ => some TemporalComponents.fullDate
  | .apply .dateTime date [time] => do
      let date ← componentsWith baseYear date
      let time ← componentsWith baseYear time
      if !date.hasDate || !date.year || date.hasTime || time.hasDate || !time.hasTime then none
      else some TemporalComponents.now
  | .apply .dateFromDateTime source [] => do
      let components ← componentsWith baseYear source
      if components.isFullDateTime then some TemporalComponents.fullDate else none
  | .apply .timeFromDateTime source [] => do
      let components ← componentsWith baseYear source
      if components.isFullDateTime then some TemporalComponents.time else none
  | _ => none

def components? (source : HavingTemporalExpression) : Option TemporalComponents :=
  componentsWith source.baseYear source.core

private def readAtom (source : HavingTemporalExpression) (phase : Phase)
    (context : ResolvingCorrelationContext Error) (frame : CorrelationFrame) :
    HavingTemporalAtom → Except Error (SimpleComparisonOperand ScalarTemporalValue)
  | .field reference => do
      let cell ← context.read (frame.envAt reference.origin) reference.field.id
      pure (projectScalarTemporalObservationWith source.baseYear (some source.profile)
        reference.field (observeCell phase cell))
  | .rangeBound origin field components bound => do
      let cell ← context.read (frame.envAt origin) field.id
      (projectScalarRangeBoundObservation source.profile (!components.year && source.baseYear.isNone)
        bound (observeCell phase cell)).mapError fun _ => context.unsupportedDateCalendar
  | .timeLiteral value => pure (.value (.time value) true)
  | .dateTimeLiteral value => do
      let some instant := source.profile.resolveLocal? value | throw context.temporalValueFailure
      pure (.value (.instant instant) true)
  | .dateLiteral value yearPresent => do
      let some date := source.profile.resolveCompletedDateParts? value.civil.parts | throw context.temporalValueFailure
      pure (.value (if yearPresent || source.baseYear.isSome then .date date
        else .yearless date { month := date.parts.month, day := date.parts.day }) true)
  | .baseYearBound bound => do
      let some year := source.baseYear | throw context.unsupportedDateCalendar
      let some date := source.profile.resolveCompletedDateParts? (baseYearRangeParts year bound) |
        throw context.unsupportedDateCalendar
      pure (.value (.date date) true)
  | .now => do
      let some world := context.world | throw context.worldUnavailable
      pure (.value (.instant world.now) true)
  | .today => do
      let some world := context.world | throw context.worldUnavailable
      let some label := source.profile.localDate? world.now | throw context.unsupportedDateCalendar
      let some date := source.profile.resolveCompletedDateParts? label.civil.parts | throw context.temporalValueFailure
      pure (.value (.date date) true)

/-- The shared temporal tree reaches arguments in order; computation poison aborts before
later arguments, while validation keeps reading (spec/05 stamp-construction grid). -/
def evaluate (source : HavingTemporalExpression) (phase : Phase)
    (context : ResolvingCorrelationContext Error) (frame : CorrelationFrame) :
    Except Error (SimpleComparisonOperand ScalarTemporalValue) :=
  let reached (operand : SimpleComparisonOperand ScalarTemporalValue) :
      Except (Sum FormalCause Error) (SimpleComparisonOperand ScalarTemporalValue) :=
    match phase, operand with
    | .computation, .unknown cause => .error (.inl cause)
    | _, operand => .ok operand
  let result := source.core.evalWithResult
    (fun atom => do reached (← (source.readAtom phase context frame atom).mapError Sum.inr))
    (fun operation operands => do
      let value ← (operation.apply source.profile operands).mapError fun
        | .calendarUnavailable => .inr context.unsupportedDateCalendar
        | .dateTimeLabelUnresolved => .inr context.temporalValueFailure
      reached value)
  match result with
  | .ok value => .ok value
  | .error (.inl cause) => .ok (.unknown cause)
  | .error (.inr error) => .error error

def readNumeric (source : HavingTemporalExpression) (part : TemporalNumericPart) (phase : Phase)
    (context : ResolvingCorrelationContext Error) (frame : CorrelationFrame)
    (formal : FormalCause → Unavailable) (nonRelevant : Unavailable) :
    Except Error (Except Unavailable NumericArithmeticOutcome) := do
  let value ← source.evaluate phase context frame
  (part.observeScalarCore source.profile value formal nonRelevant).mapError fun _ => context.unsupportedDateCalendar

end HavingTemporalExpression

structure HavingTemporalComparison where
  operator : TemporalComparisonOp
  left : HavingTemporalExpression
  right : HavingTemporalExpression
  deriving Repr, DecidableEq

namespace HavingTemporalComparison

def references (comparison : HavingTemporalComparison) : List HavingTemporalExpressionRef :=
  comparison.left.references ++ comparison.right.references

private def read (comparison : HavingTemporalComparison) (source : HavingTemporalExpression)
    (phase : Phase) (context : ResolvingCorrelationContext Error) (frame : CorrelationFrame) :
    Except Error (SimpleComparisonOperand ScalarTemporalValue) := do
  let value ← source.evaluate phase context frame
  pure (match value with
    | .value .noValue _ => .notEvaluated
    | .value (.date date) given =>
        if (comparison.left.components?.map (·.hasTime)) != (comparison.right.components?.map (·.hasTime)) then
          .value (.instant date.instant) given else value
    | _ => value)

def evalValidationRead (comparison : HavingTemporalComparison)
    (context : ResolvingCorrelationContext Error) (frame : CorrelationFrame) : Except Error Verdict := do
  let left ← comparison.read comparison.left .validation context frame
  let right ← comparison.read comparison.right .validation context frame
  pure (match left, right with
    | .value .nonRelevant _, _ | _, .value .nonRelevant _ => .unknown
    | _, _ => evalSymmetricComparison (ScalarTemporalValue.holds comparison.operator) left right)

def evalComputationRead (comparison : HavingTemporalComparison)
    (context : ResolvingCorrelationContext Error) (frame : CorrelationFrame) : Except Error ComputationConditionResult :=
  evalComputationComparisonExcept (ScalarTemporalValue.holds comparison.operator)
    (comparison.read comparison.left .computation context frame)
    (fun _ => comparison.read comparison.right .computation context frame)

end HavingTemporalComparison
end A12Kernel
