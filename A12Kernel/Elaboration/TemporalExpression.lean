import A12Kernel.Elaboration.ConstructedDateEvaluation
import A12Kernel.Semantics.TemporalExpression
import A12Kernel.Elaboration.TemporalExtremumStream
import A12Kernel.Elaboration.Flat.FieldValueRead
import A12Kernel.Elaboration.ValueAsDateTimeWorldComponents
import A12Kernel.Elaboration.DateRangeBoundComparison

/-! # Checked scalar temporal expressions

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
      (left right : SurfaceScalarTemporalExpression)
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
      (amount : AuthoredNumericExpr SurfaceNumericAtom)
  | timeConstruction (components : SurfaceTimeComponents)
  | dateFromDateTime (source : SurfaceScalarTemporalExpression)
  | timeFromDateTime (source : SurfaceScalarTemporalExpression)
  | subdayShift (unit : DateTimeSubdayUnit) (source : SurfaceScalarTemporalExpression)
      (amount : AuthoredNumericExpr SurfaceNumericAtom)
  deriving Repr, DecidableEq

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

inductive ScalarTemporalAtom (model : FlatModel) where
  | field (source : FlatTemporalField)
  | fixed (value : ScalarTemporalValue)
  | now
  | today (profile : ModelZone.ConcreteProfile)
  | dateLiteral (profile : ModelZone.ConcreteProfile) (value : FullDate)
  | dateTimeLiteral (profile : ModelZone.ConcreteProfile) (value : LocalDateTime)
  | dateConstruction (components : CheckedConstructedDateComponents model)
  | timeConstruction (components : CheckedTimeComponents model)
  | valueAsDate (source : CheckedZonedValueAsDateSource model)
  | rangeBound (profile : ModelZone.ConcreteProfile) (source : CheckedDateRangeBoundOperand model)
  | baseYearBound (profile : ModelZone.ConcreteProfile) (year : Int) (bound : BaseYearRangeEndpoint)

inductive ScalarTemporalEvaluationFault where
  | dateTimeLabelUnresolved
  | calendarUnavailable
  deriving Repr, DecidableEq

inductive ScalarTemporalTransform (model : FlatModel) where
  | extremum (operator : TemporalExtremumOp)
  | dateTime (profile : ModelZone.ConcreteProfile)
  | calendarShift (profile : ModelZone.ConcreteProfile)
      (unit : DateShiftUnit) (amount : CheckedTemporalShiftAmount model)
  | dateFromDateTime (profile : ModelZone.ConcreteProfile)
  | timeFromDateTime (profile : ModelZone.ConcreteProfile)
  | subdayShift (profile : ModelZone.ConcreteProfile)
      (unit : DateTimeSubdayUnit) (amount : CheckedTemporalShiftAmount model)

abbrev ScalarTemporalExpression (model : FlatModel) :=
  TemporalExpressionOf (ScalarTemporalAtom model) (ScalarTemporalTransform model)

/-- The sealed core records the component set established at each compositional boundary. -/
structure CheckedScalarTemporalExpression (model : FlatModel) where
  private mk ::
  core : ScalarTemporalExpression model
  components : TemporalComponents
  modelWellFormed : model.validate.isOk = true

/-- Both operands are independently checked before the existing comparison-format gate is asked. -/
structure CheckedScalarTemporalComparison (model : FlatModel) where
  private mk ::
  left : CheckedScalarTemporalExpression model
  right : CheckedScalarTemporalExpression model
  operator : TemporalComparisonOp
  comparisonZone? : Option ModelZone.ConcreteProfile := none
  modelWellFormed : model.validate.isOk = true

private def scalarProfile (model : FlatModel) :
    Except ScalarTemporalExpressionError ModelZone.ConcreteProfile :=
  match ModelZone.ConcreteProfile.ofId? model.timeZoneId with
  | some profile => pure profile
  | none => throw .unsupportedSource

/-- Base Year completes a date without changing a clock's value family. The family gate precedes
year supplementation in spec/05; the configured/unconfigured stamp grid locks both consumers. -/
private def scalarComponents (model : FlatModel) (components : TemporalComponents) : TemporalComponents :=
  if components.hasDate then components.withBaseYear model.hasBaseYear else components

private def resolveScalarTemporalExpression (model : FlatModel) (rowGroup : GroupPath)
    (targetGroup? : Option GroupPath) :
    SurfaceScalarTemporalExpression → Except ScalarTemporalExpressionError
      (ScalarTemporalExpression model × TemporalComponents)
  | .field reference => do
      let declaration ← (match targetGroup? with
        | none => model.resolveFieldValueRead rowGroup reference
        | some targetGroup => model.resolveComputationFieldValueRead rowGroup targetGroup reference).mapError .read
      let some field := declaration.toTemporalField? | throw (.nonTemporal declaration.path)
      if declaration.toTemporalTargetPolicy?.any (·.partialMode != .full) then
        throw .unsupportedSource
      pure (.atom (.field field), scalarComponents model field.components)
  | .group source => resolveScalarTemporalExpression model rowGroup targetGroup? source
  | .extremum operator operands => do
      let scope := targetGroup?.map model.repeatableScopeForGroupPath |>.getD []
      let source ← (TemporalExtremumOperands.elaborate model rowGroup operands
        (targetGroup?.getD rowGroup) scope).mapError .extremum
      let fields ← source.shape.operands.mapM fun
        | .field declaration _ => do
            if !declaration.repeatableScope.isPrefixOf scope then throw .unsupportedSource
            let some field := declaration.toTemporalField? | throw (.nonTemporal declaration.path)
            pure field
        | _ => throw .unsupportedSource
      let first :: rest := fields | throw .unsupportedSource
      pure (.apply (.extremum operator) (.atom (.field first))
        (rest.map fun field => .atom (.field field)), scalarComponents model first.components)
  | .combine operator left right => do
      let (left, leftComponents) ← resolveScalarTemporalExpression model rowGroup targetGroup? left
      let (right, rightComponents) ← resolveScalarTemporalExpression model rowGroup targetGroup? right
      if leftComponents != rightComponents then throw .incompatibleFormats
      pure (.apply (.extremum operator) left [right], leftComponents)
  | .now => pure (.atom .now, TemporalComponents.now)
  | .today => do pure (.atom (.today (← scalarProfile model)), TemporalComponents.fullDate)
  | .dateLiteral value => do
      pure (.atom (.dateLiteral (← scalarProfile model) value), TemporalComponents.fullDate)
  | .timeLiteral value => pure (.atom (.fixed (.time value)), TemporalComponents.time)
  | .dateTimeLiteral value => do
      let profile ← scalarProfile model
      pure (.atom (.dateTimeLiteral profile value), TemporalComponents.now)
  | .rangeBound reference bound => do
      let declaration ← (model.resolveFieldDeclarationUnchecked rowGroup reference).mapError .read
      let scope := targetGroup?.map model.repeatableScopeForGroupPath |>.getD []
      let source ← (elaborateDateRangeBoundOperand model declaration.id bound scope).mapError .rangeBound
      pure (.atom (.rangeBound (← scalarProfile model) source),
        source.components.withBaseYear model.hasBaseYear)
  | .baseYearBound bound => do
      let some year := model.baseYear | throw .unsupportedSource
      pure (.atom (.baseYearBound (← scalarProfile model) year bound), TemporalComponents.fullDate)
  | .valueAsDate reference endpoint => do
      let declaration ← (model.resolveFieldDeclarationUnchecked rowGroup reference).mapError .read
      let scope := targetGroup?.map model.repeatableScopeForGroupPath |>.getD []
      let source ← (elaborateZonedValueAsDateSource model declaration.id endpoint scope).mapError .partialDate
      pure (.atom (.valueAsDate source), TemporalComponents.fullDate)
  | .dateTimeConstruction date time => do
      if !date.admittedSourceSlot || !time.admittedSourceSlot then throw .unsupportedSource
      let (date, dateComponents) ← resolveScalarTemporalExpression model rowGroup targetGroup? date
      let (time, timeComponents) ← resolveScalarTemporalExpression model rowGroup targetGroup? time
      if !dateComponents.hasDate || !dateComponents.year || dateComponents.hasTime ||
          timeComponents.hasDate || !timeComponents.hasTime then throw .incompatibleFormats
      pure (.apply (.dateTime (← scalarProfile model)) date [time], TemporalComponents.now)
  | .dateConstruction source => do
      let scope := targetGroup?.map model.repeatableScopeForGroupPath |>.getD []
      let components ← (elaborateConstructedDateSources model source scope).mapError .dateComponents
      pure (.atom (.dateConstruction components), TemporalComponents.fullDate)
  | .calendarShift unit source amount => do
      if !source.admittedSourceSlot then throw .unsupportedSource
      let (source, components) ← resolveScalarTemporalExpression model rowGroup targetGroup? source
      let componentPresent := match unit with
        | .days => components.day
        | .months => components.month
        | .years => components.year
      if !componentPresent || (unit != .days && components.hasTime) then throw .incompatibleFormats
      let profile ← scalarProfile model
      let amount ← (match targetGroup? with
        | none => elaborateTemporalExpressionShiftAmount model rowGroup amount
        | some binding => elaborateRepeatableTemporalExpressionShiftAmount model binding amount rowGroup).mapError .amount
      pure (.apply (.calendarShift profile unit amount) source [], components)
  | .timeConstruction source => do
      let scope := targetGroup?.map model.repeatableScopeForGroupPath |>.getD []
      let components ← (elaborateTimeComponents model source scope).mapError .timeComponents
      pure (.atom (.timeConstruction components), TemporalComponents.time)
  | .dateFromDateTime source => do
      if !source.admittedSourceSlot then throw .unsupportedSource
      let (source, components) ← resolveScalarTemporalExpression model rowGroup targetGroup? source
      if !components.isFullDateTime then throw .incompatibleFormats
      pure (.apply (.dateFromDateTime (← scalarProfile model)) source [], TemporalComponents.fullDate)
  | .timeFromDateTime source => do
      if !source.admittedSourceSlot then throw .unsupportedSource
      let (source, components) ← resolveScalarTemporalExpression model rowGroup targetGroup? source
      if !components.isFullDateTime then throw .incompatibleFormats
      pure (.apply (.timeFromDateTime (← scalarProfile model)) source [], TemporalComponents.time)
  | .subdayShift unit source amount => do
      if !source.admittedSourceSlot then throw .unsupportedSource
      let (source, components) ← resolveScalarTemporalExpression model rowGroup targetGroup? source
      if !unit.admittedBy components || !components.isFullDateTime then throw .incompatibleFormats
      let profile ← scalarProfile model
      let amount ← (match targetGroup? with
        | none => elaborateTemporalExpressionShiftAmount model rowGroup amount
        | some binding => elaborateRepeatableTemporalExpressionShiftAmount model binding amount rowGroup).mapError .amount
      pure (.apply (.subdayShift profile unit amount) source [], components)

def elaborateScalarTemporalExpression (model : FlatModel) (rowGroup : GroupPath)
    (surface : SurfaceScalarTemporalExpression) (targetGroup? : Option GroupPath := none) :
    Except ScalarTemporalExpressionError (CheckedScalarTemporalExpression model) := do
  match h : model.validate with
  | .error error => throw (.model error)
  | .ok () =>
      let (core, components) ← resolveScalarTemporalExpression model rowGroup targetGroup? surface
      pure { core, components, modelWellFormed := by rw [h]; rfl }

private def temporalConstant : SurfaceScalarTemporalExpression → Bool
  | .now | .today | .dateLiteral _ | .timeLiteral _ | .dateTimeLiteral _ => true
  | .group source => temporalConstant source
  | _ => false

private def ungroupedClock : SurfaceScalarTemporalExpression → Bool
  | .now | .today => true
  | _ => false

private def nowOperand : SurfaceScalarTemporalExpression → Bool
  | .now => true
  | .group source => nowOperand source
  | _ => false

/-- Typed component admission is shared by scalar validation and target-bound computation guards. -/
def elaborateScalarTemporalComparison (model : FlatModel) (rowGroup : GroupPath)
    (operator : TemporalComparisonOp) (left right : SurfaceScalarTemporalExpression)
    (targetGroup? : Option GroupPath := none) :
    Except ScalarTemporalExpressionError (CheckedScalarTemporalComparison model) := do
  if temporalConstant left && temporalConstant right &&
      ungroupedClock left == ungroupedClock right then throw .unsupportedSource
  let leftNow := nowOperand left
  let rightNow := nowOperand right
  let left ← elaborateScalarTemporalExpression model rowGroup left targetGroup?
  let right ← elaborateScalarTemporalExpression model rowGroup right targetGroup?
  if (leftNow && !operator.admitsNow model.hasBaseYear right.components) ||
      (rightNow && !operator.admitsNow model.hasBaseYear left.components) then
    throw .incompatibleFormats
  if !operator.admitsFormats model.hasBaseYear left.components right.components then
    throw .incompatibleFormats
  for components in [left.components, right.components] do
    if components.hasTime && components != TemporalComponents.now && components != TemporalComponents.time then
      throw .unsupportedSource
  let comparisonZone? ← if left.components.hasTime != right.components.hasTime then
      some <$> scalarProfile model else pure none
  pure { left, right, operator, comparisonZone?, modelWellFormed := left.modelWellFormed }

private def liftScalarTemporal (wrap : α → ScalarTemporalValue) :
    SimpleComparisonOperand α → SimpleComparisonOperand ScalarTemporalValue
  | .value value given => .value (wrap value) given
  | .notEvaluated => .notEvaluated
  | .unknown cause => .unknown cause

private def readScalarTemporalAmount (context : FlatContext) (phase : Phase) :
    CheckedTemporalShiftAmount model → Except NumericValidationUnavailable NumericArithmeticOutcome
  | .literal value => .ok (.value value .fixed)
  | .field source _ =>
      (context.resolveNumberComparisonOperandAt phase source).toValidationArithmetic
  | .expression checked _ => checked.evalWith fun
      | .field source => (context.resolveNumberComparisonOperandAt phase source).toValidationArithmetic
      | _ => .error .groupState

private def resolvedScalarDate (profile : ModelZone.ConcreteProfile) (date : FullDate) :
    Option DateValue := do
  let instant ← profile.resolveLocal? {
    date, time := { hour := 0, minute := 0, second := 0, valid := by decide } }
  pure { instant, parts := date.civil.parts, basis := .storedGregorian }

private def readScalarTemporalAtom (model : FlatModel) (phase : Phase) (context : FlatContext)
    (atom : ScalarTemporalAtom model) :
    Except ScalarTemporalEvaluationFault (SimpleComparisonOperand ScalarTemporalValue) := do
  match atom with
  | .dateTimeLiteral profile value =>
      match profile.resolveLocal? value with
      | some instant => pure (.value (.instant instant) true)
      | none => throw .dateTimeLabelUnresolved
  | .dateLiteral profile value =>
      match resolvedScalarDate profile value with
      | some value => pure (.value (.date value) true)
      | none => throw .dateTimeLabelUnresolved
  | .fixed value => pure (.value value true)
  | .baseYearBound profile year bound =>
      match profile.resolveCompletedDateParts? (baseYearRangeParts year bound) with
      | some value => pure (.value (.date value) true)
      | none => throw .calendarUnavailable
  | .rangeBound profile source =>
      match source with
      | .exact bound => do
          let range ← (CheckedDateRangeSource.observeRange bound.source.id phase
            (context.read bound.source.id)).mapError (fun _ => .calendarUnavailable)
          let selected ← (CheckedDateRangeSource.selectBound bound.source.id bound.bound range)
            |>.mapError (fun _ => .calendarUnavailable)
          pure (liftScalarTemporal (fun value => .date value) selected.asValidationSimpleOperand)
      | .yearless bound => do
          let range ← (CheckedDateRangeSource.observeRange bound.source.id phase
            (context.read bound.source.id)).mapError (fun _ => .calendarUnavailable)
          let selected ← (CheckedYearlessDateRangeBound.projectYearless bound.source.id bound.bound range)
            |>.mapError (fun _ => .calendarUnavailable)
          match selected with
          | .empty => pure .notEvaluated
          | .unknown cause | .poison cause => pure (.unknown cause)
          | .value label =>
              let key := label.completed bound.bound
              -- The yearless comparison key stays independent of the runtime completion year.
              -- KF201 and the range-expression grid retain February 29 at a month-only end.
              let some value := profile.resolveCompletedDateParts? {
                year := 2000, month := key.month, day := key.day } | throw .calendarUnavailable
              pure (.value (.yearless value key) true)
  | .now => pure (match context.world with
      | some world => .value (.instant world.now) true
      | none => .unknown .malformed)
  | .today profile => pure (match context.world.bind (fun world => profile.localDate? world.now)
      |>.bind (resolvedScalarDate profile) with
      | some date => .value (.date date) true
      | none => .unknown .malformed)
  | .valueAsDate source => do
      let cell := context.read source.source.target.id
      let checked := source.toCheckedValueAsDateSource.checkSourceText {
        rawPresent := cell.rawPresent, parsed := context.storedText source.source.target.id
        findings := cell.findings }
      match source.toCheckedValueAsDateSource.observe phase checked with
      | .empty => pure .notEvaluated
      | .unavailable cause => pure (.unknown cause)
      | .nonRelevant => pure (.value .nonRelevant true)
      | .date date =>
          let some value := resolvedScalarDate source.profile date | throw .calendarUnavailable
          pure (.value (.date value) true)
  | .dateConstruction components =>
      let read (source : CheckedConstructedDateSource model) := match source with
        | .numberField checked => checked.classify (observeCell phase (context.read checked.source.id))
        | .stringField checked => checked.classify (observeCell phase (context.read checked.source.id))
        | .dateYearField checked => checked.classify (observeCell phase (context.read checked.source.id))
            (context.storedText checked.source.id)
        | .constant value => pure (.value value)
        | .extractor checked => checked.classify (observeCell phase (context.read checked.source.id))
        | .baseYearExtractor checked => pure (.value
            (baseYearDateSourceNumericPart checked.year checked.source checked.part).num)
        | .pointInTimeExtractor checked => checked.read context.world
      match components.evaluateValueWith read with
      | .ok (.value instant parts notGiven) =>
          pure (.value (.date { instant, parts, basis := .legacyHybrid }) (!notGiven))
      | .ok (.noValue notGiven) => pure (.value .noValue (!notGiven))
      | .ok (.unavailable cause) => pure (.unknown cause)
      | .error _ => throw .calendarUnavailable
  | .timeConstruction components =>
      let read (component : CheckedTimeComponent model) : Except TimeComponentsFault TimeConstructionComponent :=
        match component with
        | .constant value => pure (.value value)
        | .number checked => checked.classify (observeCell phase (context.read checked.source.id))
        | .string checked => checked.classify (observeCell phase (context.read checked.source.id))
        | .extractor checked => checked.classify (observeCell phase (context.read checked.source.id))
        | .shiftedExtractor checked => do
            let source := checked.source
            let result ← ValueAsDateTimeResult.evaluateShiftedDateTimeObservation
              source.profile source.unit source.source.id
              (observeCell phase (context.read source.source.id))
              (fun _ => pure (readScalarTemporalAmount context phase source.amount))
              TimeComponentsFault.shifted
            pure (result.asTimeOperand.extractComponent checked.part)
      pure (match components.evaluateWith read with
      | .ok (.value time) => .value (.time time) true
      | .ok (.unavailable cause) => .unknown cause
      | .ok .incomplete => .value .noValue false
      | .ok .unreal => .value .noValue true
      | .ok .nonRelevant => .value .nonRelevant true
      | .error _ => .unknown .malformed)
  | .field field =>
      let observation := observeCell phase (context.read field.id)
      let components := scalarComponents model field.components
      pure (if components == TemporalComponents.now then
        liftScalarTemporal .instant observation.asDateTimeExtremumOperand
      else if components == TemporalComponents.time then
        liftScalarTemporal .time observation.asTimeExtremumOperand
      else if components.year then
        match observation with
        | .empty => .notEvaluated
        | .unknown cause | .poison cause => .unknown cause
        | .value (.temporal (.date stored)) =>
            let (year, month, day) := maskedDateComponents field.components model.baseYear stored.parts
            let parts : DateParts := { year, month, day }
            if stored.parts == parts then .value (.date stored) true
            else match (ModelZone.ConcreteProfile.ofId? model.timeZoneId).bind
                (fun profile => profile.resolveCompletedDateParts? parts) with
              | some value => .value (.date value) true
              | none => .unknown .malformed
        | _ => .unknown .malformed
      else match observation.asYearlessDateExtremumOperand field.components, observation with
        | .value key given, .value (.temporal (.date value)) => .value (.yearless value key) given
        | .notEvaluated, _ => .notEvaluated
        | .unknown cause, _ => .unknown cause
        | _, _ => .unknown .malformed)

private def applyScalarTemporalTransform (phase : Phase) (context : FlatContext)
    (operation : ScalarTemporalTransform model)
    (source : SimpleComparisonOperand ScalarTemporalValue) :
    Except ScalarTemporalEvaluationFault (SimpleComparisonOperand ScalarTemporalValue) :=
  match source with
  | .unknown cause => pure (.unknown cause)
  | source => match operation with
      | .calendarShift profile unit amount => do
          match readScalarTemporalAmount context phase amount with
          | .error (.formal cause) => pure (.unknown cause)
          | .error _ => throw .calendarUnavailable
          | .ok .notEvaluated => pure .notEvaluated
          | .ok (.value amount fillability) =>
              let shift (instant : Instant) (wrap : LegacyCalendarLabel → Instant → ScalarTemporalValue) (given : Bool) :
                  Except ScalarTemporalEvaluationFault (SimpleComparisonOperand ScalarTemporalValue) :=
                match profile.shiftCalendar? unit instant (temporalShiftAmountToInt32 amount) with
                | some (label, instant) => pure (.value
                    (wrap label instant)
                    (given && !fillability.canGrow && !fillability.canShrink))
                | none => throw .calendarUnavailable
              match source with
              | .value .nonRelevant _ => pure (.value .nonRelevant true)
              | .value .noValue given =>
                  pure (.value .noValue (given && !fillability.canGrow && !fillability.canShrink))
              | .value (.date value) given =>
                  shift value.instant (fun label instant => .date { instant, parts := label.parts, basis := .legacyHybrid }) given
              | .value (.yearless value _) given =>
                  shift value.instant (fun label instant => .yearless { instant, parts := label.parts, basis := .legacyHybrid }
                    { month := label.parts.month, day := label.parts.day }) given
              | .value (.instant instant) given => shift instant (fun _ instant => .instant instant) given
              | .notEvaluated => pure .notEvaluated
              | _ => throw .calendarUnavailable
      | .dateFromDateTime profile => do
          match source with
          | .value (.instant instant) given =>
              let some label := profile.calendarLabel? instant | throw .calendarUnavailable
              let midnight := { label with time := { hour := 0, minute := 0, second := 0, valid := by decide } }
              let some instant := profile.resolveCalendarLabel? midnight | throw .dateTimeLabelUnresolved
              pure (.value (.date { instant, parts := label.parts, basis := .legacyHybrid }) given)
          | .value .noValue given => pure (.value .noValue given)
          | .value .nonRelevant _ => pure (.value .nonRelevant true)
          | .notEvaluated => pure .notEvaluated
          | _ => throw .calendarUnavailable
      | .timeFromDateTime profile => do
          match source with
          | .value (.instant instant) given =>
              let some label := profile.calendarLabel? instant | throw .calendarUnavailable
              pure (.value (.time label.time) given)
          | .value .noValue given => pure (.value .noValue given)
          | .value .nonRelevant _ => pure (.value .nonRelevant true)
          | .notEvaluated => pure .notEvaluated
          | _ => throw .calendarUnavailable
      | .subdayShift _ unit amount => do
          match readScalarTemporalAmount context phase amount with
          | .error (.formal cause) => pure (.unknown cause)
          | .error _ => throw .calendarUnavailable
          | .ok .notEvaluated => pure .notEvaluated
          | .ok (.value amount fillability) =>
              match source with
              | .value (.instant instant) given =>
                  pure (.value (.instant (instant.shift unit (temporalShiftAmountToInt32 amount)))
                    (given && !fillability.canGrow && !fillability.canShrink))
              | .value .noValue given =>
                  pure (.value .noValue (given && !fillability.canGrow && !fillability.canShrink))
              | .value .nonRelevant _ => pure (.value .nonRelevant true)
              | .notEvaluated => pure .notEvaluated
              | _ => throw .calendarUnavailable
      | .extremum _ | .dateTime _ => throw .calendarUnavailable

/-- Constructor arguments have already been reached by the shared ordered application. A missing
payload keeps its own provenance; non-relevance suppresses a result without inventing a formal cause. -/
private def applyScalarTemporalOperation (phase : Phase) (context : FlatContext)
    (operation : ScalarTemporalTransform model)
    (operands : List (SimpleComparisonOperand ScalarTemporalValue)) :
    Except ScalarTemporalEvaluationFault (SimpleComparisonOperand ScalarTemporalValue) :=
  match operation, operands with
  | .extremum operator, operands => pure (evalTemporalExtremumAggregate (ScalarTemporalValue.select operator)
      { operands, hasUninstantiatedTail := false, hasHaving := false })
  | .dateTime profile, [date, time] =>
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
  | _, [source] => applyScalarTemporalTransform phase context operation source
  | _, _ => throw .calendarUnavailable

namespace CheckedScalarTemporalExpression

/-- The two source contracts that consume exact stored text in addition to a typed cell. -/
def storedTextFields (expression : CheckedScalarTemporalExpression model) : List FieldId :=
  expression.core.dependencies
    (fun | .dateConstruction components => components.sources.filterMap fun
           | .dateYearField checked => some checked.source.id
           | _ => none
         | .valueAsDate source => [source.source.target.id]
         | _ => [])
    (fun _ => [])

def fieldIds (expression : CheckedScalarTemporalExpression model) : List FieldId :=
  expression.core.dependencies
    (fun | .field source => [source.id]
         | .dateConstruction components => components.fields
         | .timeConstruction components => components.toWorld.fieldDependencies
         | .valueAsDate source => [source.source.target.id]
         | .rangeBound _ (.exact source) => [source.source.id]
         | .rangeBound _ (.yearless source) => [source.source.id]
         | _ => [])
    (fun | .subdayShift _ _ amount | .calendarShift _ _ amount => amount.fieldDependencies | _ => [])

def referencesField (expression : CheckedScalarTemporalExpression model) (field : FieldId) : Bool :=
  expression.fieldIds.contains field

/-- Model-zone literal resolution belongs to execution, retaining value failure separately from
missingness and operand poison (the DateTime constant zone-split checkpoint, spec/09). -/
def evalResult (expression : CheckedScalarTemporalExpression model) (phase : Phase) (context : FlatContext) :
    Except ScalarTemporalEvaluationFault (SimpleComparisonOperand ScalarTemporalValue) :=
  let reached (operand : SimpleComparisonOperand ScalarTemporalValue) :
      Except (Sum FormalCause ScalarTemporalEvaluationFault) (SimpleComparisonOperand ScalarTemporalValue) :=
    match phase, operand with
    | .computation, .unknown cause => .error (.inl cause)
    | _, operand => .ok operand
  let result := expression.core.evalWithResult
    (fun atom => do
      let operand ← (readScalarTemporalAtom model phase context atom).mapError Sum.inr
      reached operand)
    (fun operation operands => do
      reached (← (applyScalarTemporalOperation phase context operation operands).mapError Sum.inr))
  match result with
  | .ok operand => .ok operand
  | .error (.inl cause) => .ok (.unknown cause)
  | .error (.inr fault) => .error fault

end CheckedScalarTemporalExpression

namespace CheckedScalarTemporalComparison

def fieldIds (comparison : CheckedScalarTemporalComparison model) : List FieldId :=
  comparison.left.fieldIds ++ comparison.right.fieldIds

def declarations (comparison : CheckedScalarTemporalComparison model) : List FlatFieldDecl :=
  comparison.fieldIds.filterMap fun field => (model.lookupUniqueId field).toOption

def referencesField (comparison : CheckedScalarTemporalComparison model) (field : FieldId) : Bool :=
  comparison.fieldIds.contains field

/-- Mixed Date/DateTime ordering uses the Date's retained instant; same-family comparison
keeps its existing identity domain (KF386 and the comparison-guard grid, 2026-10-04). -/
private def readOperand (comparison : CheckedScalarTemporalComparison model) (phase : Phase)
    (context : FlatContext) (expression : CheckedScalarTemporalExpression model) :
    Except ScalarTemporalEvaluationFault (SimpleComparisonOperand ScalarTemporalValue) := do
  let operand ← expression.evalResult phase context
  match comparison.comparisonZone?, operand with
  | _, .value .noValue _ => pure .notEvaluated
  | some _, .value (.date date) given => pure (.value (.instant date.instant) given)
  | _, _ => pure operand

/-- Temporal guards use the shared ordered computation comparison, preserving label failure as a
runtime effect and aborting on a reached operand poison (comparison-guard grid, 2026-10-04). -/
def evalComputation (comparison : CheckedScalarTemporalComparison model)
    (context : FlatContext) : Except ScalarTemporalEvaluationFault ComputationConditionResult :=
  evalComputationComparisonExcept (ScalarTemporalValue.holds comparison.operator)
    (comparison.readOperand .computation context comparison.left)
    (fun _ => comparison.readOperand .computation context comparison.right)

/-- Retain runtime label failure outside the comparison verdict; the enclosing rule owns its
value-error projection (temporal review grid, 2026-10-03). -/
def evalResult (comparison : CheckedScalarTemporalComparison model) (phase : Phase)
    (context : FlatContext) : Except ScalarTemporalEvaluationFault Verdict := do
  match phase with
  | .computation => pure (match ← comparison.evalComputation context with
      | .holds => .fired .value
      | .notTrue => .notFired
      | .poison _ => .unknown)
  | .validation =>
      let left ← comparison.readOperand phase context comparison.left
      let right ← comparison.readOperand phase context comparison.right
      match left, right with
      | .value .nonRelevant _, _ | _, .value .nonRelevant _ => pure .unknown
      | _, _ => pure (evalSymmetricComparison (ScalarTemporalValue.holds comparison.operator) left right)

def evalAt (comparison : CheckedScalarTemporalComparison model) (phase : Phase)
    (context : FlatContext) : Verdict :=
  match comparison.evalResult phase context with
  | .ok verdict => verdict
  | .error .dateTimeLabelUnresolved => .fired .value
  | .error .calendarUnavailable => .unknown

def eval (comparison : CheckedScalarTemporalComparison model) (context : FlatContext) : Verdict :=
  comparison.evalAt .validation context

end CheckedScalarTemporalComparison

end A12Kernel
