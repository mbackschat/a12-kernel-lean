import A12Kernel.Semantics.TimeConstructionInputs
import A12Kernel.Semantics.HavingDateValidity
import A12Kernel.Semantics.ScalarTemporalValue
import A12Kernel.Semantics.TemporalExpression
import A12Kernel.Semantics.HavingTemporalSelection

namespace A12Kernel

inductive HavingTemporalReadSource where
  | temporal (field : FlatTemporalField)
  | range (field : FlatDateRangeField) (components : TemporalComponents)
  | number (field : FlatNumberField)
  | string (field : FlatStringField)
  deriving Repr, DecidableEq

/-- Each temporal-tree read retains its declared carrier as well as its capture origin. -/
structure HavingTemporalExpressionRef where
  origin : HavingOrigin
  source : HavingTemporalReadSource
  deriving Repr, DecidableEq

def HavingTemporalExpressionRef.fieldId (reference : HavingTemporalExpressionRef) : FieldId :=
  match reference.source with
  | .temporal field => field.id
  | .range field _ => field.id
  | .number field => field.id
  | .string field => field.id

abbrev HavingTimeComponents := TimeComponentPrefix (HavingOrigin × ResolvedTimeConstructionSource)

private def HavingTimeComponents.read (components : HavingTimeComponents) (profile : ModelZone.ConcreteProfile)
    (phase : Phase) (context : ResolvingCorrelationContext Error) (frame : CorrelationFrame) :
    Except Error TimeConstructionResult :=
  components.evaluateWith (fun (origin, source) => do
    let classify (value : Except TimeConstructionInputFault TimeConstructionComponent) :=
      match value with
      | .ok component => pure component
      | .error (.stringNotConvertible _ _) => throw context.temporalValueFailure
      | .error _ => pure (.unavailable .malformed)
    match source with
    | .constant value => pure (.value value)
    | .number field => classify (classifyTimeNumberComponent field.id
        (observeCell phase (← context.read (frame.envAt origin) field.id)))
    | .string field => classify (classifyTimeStringComponent field.id
        (observeCell phase (← context.read (frame.envAt origin) field.id)))
    | .extractor field part => classify (classifyTimeExtractorComponent field.id part
        (observeCell phase (← context.read (frame.envAt origin) field.id)))
    | .nowExtractor part =>
        let some world := context.world | throw context.worldUnavailable
        let some label := profile.localDateTime? world.now | throw context.unsupportedDateCalendar
        pure (.value (part.extract label.time).num)) phase

inductive HavingTemporalAtom where
  | selection (kind : HavingTemporalSelection) (slots : List (HavingFieldListSlot HavingTemporalSelectionRef))
  | field (reference : HavingTemporalRef)
  | rangeBound (origin : HavingOrigin) (source : FlatDateRangeField) (components : TemporalComponents) (bound : DateRangeBound)
  | timeConstruction (components : HavingTimeComponents)
  | dateConstruction (components : HavingDateComponents)
  | dateLiteral (value : FullDate) (yearPresent : Bool)
  | timeLiteral (value : TimeOfDay)
  | dateTimeLiteral (value : LocalDateTime)
  | today
  | now
  | baseYearBound (bound : BaseYearRangeEndpoint)
  deriving Repr, DecidableEq

inductive HavingTemporalOperation where
  | constructor (operation : ScalarTemporalConstructorOp)
  | extremum (operator : TemporalExtremumOp)
  deriving Repr, DecidableEq

structure HavingTemporalExpression where
  core : TemporalExpressionOf HavingTemporalAtom HavingTemporalOperation
  profile : ModelZone.ConcreteProfile
  baseYear : Option Int
  grouped : Bool := false
  deriving Repr, DecidableEq

namespace HavingTemporalExpression

def referenceSlots (source : HavingTemporalExpression) : List (HavingFieldListSlot HavingTemporalExpressionRef) :=
  source.core.atoms.flatMap fun atom =>
    match atom with
    | .selection _ slots => slots.map (·.map fun reference => { origin := reference.origin, source := .temporal reference.field })
    | atom => (show List HavingTemporalExpressionRef from match atom with
        | .field reference => [{ origin := reference.origin, source := .temporal reference.field }]
        | .rangeBound origin field components _ => [{ origin, source := .range field components }]
        | .timeConstruction components => components.sources.filterMap fun (origin, component) =>
            match component with
            | .number field => some { origin, source := .number field }
            | .string field => some { origin, source := .string field }
            | .extractor field _ => some { origin, source := .temporal field }
            | _ => none
        | .dateConstruction components => components.sources.filterMap fun (origin, component) =>
            match component with
            | .numberField field => some { origin, source := .number field }
            | .stringField field => some { origin, source := .string field }
            | .dateYearField field | .extractor field _ _ => some { origin, source := .temporal field }
            | _ => none
        | _ => []).map HavingFieldListSlot.direct

def references (source : HavingTemporalExpression) : List HavingTemporalExpressionRef :=
  source.referenceSlots.flatMap (·.references)

def presenceSlots (source : HavingTemporalExpression) : List (HavingFieldListSlot HavingPresenceRef) :=
  source.referenceSlots.map (·.map fun reference => { origin := reference.origin, field := reference.fieldId })

/-- Checked core constructors retain the same source-slot boundary as authored elaboration
(spec/05 §§3,6); a hand-built tree cannot carry a value-expression selector here. -/
private def coreAdmittedSourceSlot : TemporalExpressionOf HavingTemporalAtom HavingTemporalOperation → Bool
  | .atom (.selection _ _) | .apply (.extremum _) _ _ => false
  | _ => true

def admittedSourceSlot (source : HavingTemporalExpression) : Bool :=
  !source.grouped && coreAdmittedSourceSlot source.core

def componentsWith (baseYear : Option Int) :
    TemporalExpressionOf HavingTemporalAtom HavingTemporalOperation → Option TemporalComponents
  | .atom atom => match atom with
      | .selection _ slots => do
          let reference ← (slots.flatMap (·.references)).head?
          pure (if reference.field.components.hasDate then reference.field.components.withBaseYear baseYear.isSome
            else reference.field.components)
      | .field reference => some (if reference.field.components.hasDate then
          reference.field.components.withBaseYear baseYear.isSome else reference.field.components)
      | .rangeBound _ _ components _ => some (components.withBaseYear baseYear.isSome)
      | .dateLiteral _ yearPresent => some ({ TemporalComponents.fullDate with year := yearPresent }.withBaseYear baseYear.isSome)
      | .timeLiteral _ | .timeConstruction _ => some TemporalComponents.time
      | .dateTimeLiteral _ | .now => some TemporalComponents.now
      | .today | .baseYearBound _ | .dateConstruction _ => some TemporalComponents.fullDate
  | .apply (.constructor .dateTime) date [time] => do
      if !coreAdmittedSourceSlot date || !coreAdmittedSourceSlot time then none else pure ()
      let date ← componentsWith baseYear date
      let time ← componentsWith baseYear time
      if !date.hasDate || !date.year || date.hasTime || time.hasDate || !time.hasTime then none
      else some TemporalComponents.now
  | .apply (.constructor .dateFromDateTime) source [] => do
      if !coreAdmittedSourceSlot source then none else pure ()
      let components ← componentsWith baseYear source
      if components.isFullDateTime then some TemporalComponents.fullDate else none
  | .apply (.constructor .timeFromDateTime) source [] => do
      if !coreAdmittedSourceSlot source then none else pure ()
      let components ← componentsWith baseYear source
      if components.isFullDateTime then some TemporalComponents.time else none
  | .apply (.extremum _) first rest => do
      let components ← componentsWith baseYear first
      let remaining ← rest.mapM (componentsWith baseYear)
      let constant : TemporalExpressionOf HavingTemporalAtom HavingTemporalOperation → Bool
        | .atom (.dateLiteral _ _) | .atom (.timeLiteral _) | .atom (.dateTimeLiteral _) | .atom .now | .atom .today => true
        | _ => false
      if remaining.all (· == components) && ((first :: rest).filter constant).length ≤ 1 then
        some components else none
  | _ => none

def components? (source : HavingTemporalExpression) : Option TemporalComponents :=
  componentsWith source.baseYear source.core

private def readAtom (source : HavingTemporalExpression) (phase : Phase)
    (context : ResolvingCorrelationContext Error) (frame : CorrelationFrame) :
    HavingTemporalAtom → Except Error (SimpleComparisonOperand ScalarTemporalValue)
  | .selection kind slots => kind.evaluate source.baseYear source.profile phase context frame slots
  | .field reference => do
      let cell ← context.read (frame.envAt reference.origin) reference.field.id
      pure (projectScalarTemporalObservationWith source.baseYear (some source.profile)
        reference.field (observeCell phase cell))
  | .rangeBound origin field components bound => do
      let cell ← context.read (frame.envAt origin) field.id
      (projectScalarRangeBoundObservation source.profile (!components.year && source.baseYear.isNone)
        bound (observeCell phase cell)).mapError fun _ => context.unsupportedDateCalendar
  | .timeConstruction components => do
      pure (← components.read source.profile phase context frame).asScalarTemporalOperand
  | .dateConstruction components => do
      pure (components.finishValue (← components.observe phase context frame)).asScalarTemporalOperand
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
      let result := match operation with
        | .constructor operation => operation.apply source.profile operands
        | .extremum operator => pure (evalTemporalExtremumAggregate (ScalarTemporalValue.select operator)
            { operands, hasUninstantiatedTail := false, hasHaving := false })
      let value ← result.mapError fun
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

def presenceSlots (comparison : HavingTemporalComparison) : List (HavingFieldListSlot HavingPresenceRef) :=
  comparison.left.presenceSlots ++ comparison.right.presenceSlots

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
