import A12Kernel.Elaboration.TemporalExpression.EntityList

namespace A12Kernel

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

private def temporalConstant : SurfaceScalarTemporalExpression → Bool
  | .now | .today | .dateLiteral _ _ | .timeLiteral _ | .dateTimeLiteral _ => true
  | .group source => temporalConstant source
  | _ => false

mutual
private def resolveScalarTemporalExpression (model : FlatModel) (rowGroup : GroupPath)
    (targetGroup? : Option GroupPath) (surface : SurfaceScalarTemporalExpression) :
    Except ScalarTemporalExpressionError (ScalarTemporalExpression model × TemporalComponents) :=
  match surface with
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
      if !source.bindingScopes.all (·.isPrefixOf scope) then throw .unsupportedSource
      let some first := source.shape.first.expansionDeclarations.head? | throw .unsupportedSource
      let some field := first.toTemporalField? | throw (.nonTemporal first.path)
      pure (.atom (.entityExtremum operator source), scalarComponents model field.components)
  | .combine operator first rest => do
      if ((first :: rest).filter temporalConstant).length > 1 then throw .unsupportedSource
      let (first, components) ← resolveScalarTemporalExpression model rowGroup targetGroup? first
      let rest ← rest.attach.mapM fun operand => do
        have := List.sizeOf_lt_of_mem operand.property
        let (core, operandComponents) ← resolveScalarTemporalExpression model rowGroup targetGroup? operand.val
        if components != operandComponents then throw .incompatibleFormats
        pure core
      pure (.apply (.extremum operator) first rest, components)
  | .now => pure (.atom .now, TemporalComponents.now)
  | .today => do pure (.atom (.today (← scalarProfile model)), TemporalComponents.fullDate)
  | .dateLiteral value yearPresent => do
      let value ← if yearPresent then pure value else do
        let source : AuthoredDateLiteral := { year := none, month := value.civil.parts.month, day := value.civil.parts.day }
        let some value := (source.completedDate? model).bind FullDate.ofCivil? | throw .unsupportedSource
        pure value
      pure (.atom (.dateLiteral (← scalarProfile model) value yearPresent),
        scalarComponents model { TemporalComponents.fullDate with year := yearPresent })
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
      let amount ← resolveScalarTemporalAmount model rowGroup targetGroup? amount
      pure (.apply (.calendarShift profile unit amount) source [], components)
  | .timeConstruction source => do
      let components ← resolveScalarTimeComponents model rowGroup targetGroup? source
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
      let amount ← resolveScalarTemporalAmount model rowGroup targetGroup? amount
      pure (.apply (.subdayShift profile unit amount) source [], components)

termination_by (sizeOf surface, 0)

private def resolveScalarTemporalProjection (model : FlatModel) (rowGroup : GroupPath)
    (targetGroup? : Option GroupPath) (surface : SurfaceScalarTemporalExpression) (part : TemporalNumericPart) :
    Except ScalarTemporalExpressionError (ScalarTemporalNumericAtom model) := do
  match surface with
  | .dateLiteral _ _ | .timeLiteral _ | .dateTimeLiteral _ => throw .unsupportedSource
  | _ => pure ()
  if !surface.admittedSourceSlot then throw .unsupportedSource
  let (source, components) ← resolveScalarTemporalExpression model rowGroup targetGroup? surface
  if !part.admitsComponents components model.hasBaseYear then throw .incompatibleFormats
  pure (.projection part (← scalarProfile model) source)
termination_by (sizeOf surface, 1)

private def resolveScalarTemporalAmount (model : FlatModel) (rowGroup : GroupPath)
    (targetGroup? : Option GroupPath)
    (surface : AuthoredNumericExpr (Sum SurfaceNumericAtom (TemporalNumericPart × SurfaceScalarTemporalExpression))) :
    Except ScalarTemporalExpressionError (AuthoredNumericExpr (ScalarTemporalNumericAtom model)) := do
  let core ← surface.mapMSubterm fun atom _ => do
    match atom with
    | .inl source =>
        let checked ← (match targetGroup? with
          | none => elaborateTemporalExpressionShiftAmount model rowGroup (.atom source)
          | some binding => elaborateRepeatableTemporalExpressionShiftAmount model binding (.atom source) rowGroup).mapError .amount
        pure (.ordinary checked)
    | .inr (part, source) => resolveScalarTemporalProjection model rowGroup targetGroup? source part
  if !core.isAdmittedResolvedNumericOperation then throw (.amount (.expression .unsupportedExpression))
  match core.numericOperationAuthoringCheck with
  | .accepted => pure ()
  | result => throw (.amount (.expression (.authoring result)))
  let summary : ScalarTemporalNumericAtom model → NumericScaleSummary
    | .projection _ _ _ => .field 0
    | .ordinary (.literal _) => .field 0
    | .ordinary (.field source _) => .field source.info.scale
    | .ordinary (.expression checked _) => (checked.core.summary? numericValidationSummary).getD (.field 0)
  if (core.summary? summary).isNone then throw (.amount (.expression .unsupportedExpression))
  pure core
termination_by (sizeOf surface, 0)
decreasing_by
  all_goals first | decreasing_tactic | (apply Prod.Lex.left; simp_all +arith <;> omega)

private def resolveScalarTimeComponent (model : FlatModel) (rowGroup : GroupPath)
    (targetGroup? : Option GroupPath) (position : TimeComponentPosition)
    (surface : Sum SurfaceTimeComponent (TimeNumericPart × SurfaceScalarTemporalExpression)) :
    Except ScalarTemporalExpressionError (Sum (CheckedTimeComponent model) (ScalarTemporalNumericAtom model)) := do
  match surface with
  | .inl source =>
      let scope := targetGroup?.map model.repeatableScopeForGroupPath |>.getD []
      .inl <$> (elaborateTimeComponent model position source scope).mapError .timeComponents
  | .inr (part, source) =>
      if position.extractor != part then throw .incompatibleFormats
      .inr <$> resolveScalarTemporalProjection model rowGroup targetGroup? source (.time part)
termination_by (sizeOf surface, 0)

private def resolveScalarTimeComponents (model : FlatModel) (rowGroup : GroupPath)
    (targetGroup? : Option GroupPath)
    (surface : TimeComponentPrefix (Sum SurfaceTimeComponent (TimeNumericPart × SurfaceScalarTemporalExpression))) :
    Except ScalarTemporalExpressionError (TimeComponentPrefix (Sum (CheckedTimeComponent model) (ScalarTemporalNumericAtom model))) :=
  match surface with
  | .empty => pure .empty
  | .hour hour => do pure (.hour (← resolveScalarTimeComponent model rowGroup targetGroup? .hour hour))
  | .minute hour minute => do
      pure (.minute (← resolveScalarTimeComponent model rowGroup targetGroup? .hour hour)
        (← resolveScalarTimeComponent model rowGroup targetGroup? .minute minute))
  | .second hour minute second => do
      pure (.second (← resolveScalarTimeComponent model rowGroup targetGroup? .hour hour)
        (← resolveScalarTimeComponent model rowGroup targetGroup? .minute minute)
        (← resolveScalarTimeComponent model rowGroup targetGroup? .second second))
termination_by (sizeOf surface, 0)
end

def elaborateScalarTemporalExpression (model : FlatModel) (rowGroup : GroupPath)
    (surface : SurfaceScalarTemporalExpression) (targetGroup? : Option GroupPath := none) :
    Except ScalarTemporalExpressionError (CheckedScalarTemporalExpression model) := do
  match h : model.validate with
  | .error error => throw (.model error)
  | .ok () =>
      let (core, components) ← resolveScalarTemporalExpression model rowGroup targetGroup? surface
      pure { core, components, modelWellFormed := by rw [h]; rfl }


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

private def readScalarTimeComponent (context : FlatContext) (phase : Phase)
    (component : CheckedTimeComponent model) : Except TimeComponentsFault TimeConstructionComponent :=
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

/-- Both shift families preserve source missingness when arithmetic has no value. Relevance is
independent of that payload, while reached formal causes remain unavailable (BedingungsOperatorHelper.addTime;
temporal numeric effects grid, 2026-10-04). The caller reaches the amount before this pure classification. -/
private def applyScalarTemporalShift
    (source : SimpleComparisonOperand ScalarTemporalValue)
    (amount : Except NumericValidationUnavailable NumericArithmeticOutcome)
    (shift : ScalarTemporalValue → Rat → Except ScalarTemporalEvaluationFault ScalarTemporalValue) :
    Except ScalarTemporalEvaluationFault (SimpleComparisonOperand ScalarTemporalValue) := do
  match source, amount with
  | .unknown cause, _ | _, .error (.formal cause) => pure (.unknown cause)
  | .value .nonRelevant _, _ | _, .error .nonRelevant => pure (.value .nonRelevant true)
  | _, .error _ => throw .calendarUnavailable
  | .notEvaluated, .ok .notEvaluated => pure (.value .noValue false)
  | .value _ given, .ok .notEvaluated => pure (.value .noValue given)
  | .notEvaluated, .ok (.value _ _) => pure .notEvaluated
  | .value value given, .ok (.value amount fillability) =>
      let given := given && !fillability.canGrow && !fillability.canShrink
      match value with
      | .noValue => pure (.value .noValue given)
      | value => pure (.value (← shift value amount) given)

mutual
private def readScalarTemporalAtom (model : FlatModel) (phase : Phase) (context : ScalarComputationContext)
    (atom : ScalarTemporalAtom model) :
    Except ScalarTemporalEvaluationFault (SimpleComparisonOperand ScalarTemporalValue) := do
  match atom with
  | .dateTimeLiteral profile value =>
      match profile.resolveLocal? value with
      | some instant => pure (.value (.instant instant) true)
      | none => throw .dateTimeLabelUnresolved
  | .dateLiteral profile value yearPresent =>
      match resolvedScalarDate profile value with
      | some value => pure (.value (if yearPresent || model.hasBaseYear then .date value else
          .yearless value { month := value.parts.month, day := value.parts.day }) true)
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
      let read (source : CheckedConstructedDateSource model) :=
        source.readWith phase context.read context.storedText context.world
      match components.evaluateValueWith read phase with
      | .ok (.value instant parts notGiven) =>
          pure (.value (.date { instant, parts, basis := .legacyHybrid }) (!notGiven))
      | .ok (.noValue notGiven) => pure (.value .noValue (!notGiven))
      | .ok (.unavailable cause) => pure (.unknown cause)
      | .error (.stringNotConvertible _ _) => throw .componentNumberInvalid
      | .error _ => throw .calendarUnavailable
  | .timeConstruction components => do
      pure (match ← readRecursiveTimeComponents phase context components with
      | .value time => .value (.time time) true
      | .unavailable cause => .unknown cause
      | .incomplete => .value .noValue false
      | .unreal => .value .noValue true
      | .nonRelevant => .value .nonRelevant true)
  | .field field => pure (readScalarTemporalField model phase field (context.read field.id))
  | .entityExtremum operator source => source.evalScalar operator phase context

termination_by (sizeOf atom, 0)

private def applyScalarTemporalTransform (phase : Phase) (context : ScalarComputationContext)
    (operation : ScalarTemporalTransform model)
    (source : SimpleComparisonOperand ScalarTemporalValue) :
    Except ScalarTemporalEvaluationFault (SimpleComparisonOperand ScalarTemporalValue) := do
  match operation with
  | .calendarShift profile unit amount =>
      let amount ← readRecursiveScalarAmount phase context amount
      applyScalarTemporalShift source amount fun value amount => do
        let instant ← match value with
          | .date value | .yearless value _ => pure value.instant
          | .instant instant => pure instant
          | _ => throw .calendarUnavailable
        let some (label, shifted) := profile.shiftCalendar? unit instant (temporalShiftAmountToInt32 amount)
          | throw .calendarUnavailable
        match value with
        | .date _ => pure (.date { instant := shifted, parts := label.parts, basis := .legacyHybrid })
        | .yearless _ _ => pure (.yearless { instant := shifted, parts := label.parts, basis := .legacyHybrid }
            { month := label.parts.month, day := label.parts.day })
        | .instant _ => pure (.instant shifted)
        | _ => throw .calendarUnavailable
  | .subdayShift _ unit amount =>
      let amount ← readRecursiveScalarAmount phase context amount
      applyScalarTemporalShift source amount fun value amount =>
        match value with
        | .instant instant => pure (.instant (instant.shift unit (temporalShiftAmountToInt32 amount)))
        | _ => throw .calendarUnavailable
  | .dateFromDateTime profile =>
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
  | .timeFromDateTime profile =>
      match source with
      | .value (.instant instant) given =>
          let some label := profile.calendarLabel? instant | throw .calendarUnavailable
          pure (.value (.time label.time) given)
      | .value .noValue given => pure (.value .noValue given)
      | .value .nonRelevant _ => pure (.value .nonRelevant true)
      | .notEvaluated => pure .notEvaluated
      | .unknown cause => pure (.unknown cause)
      | _ => throw .calendarUnavailable
  | .extremum _ | .dateTime _ => throw .calendarUnavailable

termination_by (sizeOf operation, 0)

/-- Constructor arguments have already been reached by the shared ordered application. A missing
payload keeps its own provenance; non-relevance suppresses a result without inventing a formal cause. -/
private def applyScalarTemporalOperation (phase : Phase) (context : ScalarComputationContext)
    (operation : ScalarTemporalTransform model)
    (operands : List (SimpleComparisonOperand ScalarTemporalValue)) :
    Except ScalarTemporalEvaluationFault (SimpleComparisonOperand ScalarTemporalValue) :=
  match _h : operation, operands with
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

termination_by (sizeOf operation, 1)
decreasing_by
  all_goals simp_all
  all_goals apply Prod.Lex.right
  all_goals omega

private def readRecursiveScalarAtom (phase : Phase) (context : ScalarComputationContext)
    (atom : ScalarTemporalNumericAtom model) : Except ScalarTemporalEvaluationFault
      (Except NumericValidationUnavailable NumericArithmeticOutcome) := do
  match atom with
  | .ordinary amount => pure (readScalarTemporalAmount { read := context.read, storedText := context.storedText, world := context.world } phase amount)
  | .projection part profile source => part.observeScalar profile (← evalScalarTemporalCore phase context source)
termination_by (sizeOf atom, 0)

private def readRecursiveScalarAmount (phase : Phase) (context : ScalarComputationContext)
    (amount : AuthoredNumericExpr (ScalarTemporalNumericAtom model)) : Except ScalarTemporalEvaluationFault
      (Except NumericValidationUnavailable NumericArithmeticOutcome) := do
  let resolved := amount.mapMSubterm fun atom _ => do
    let value ← (readRecursiveScalarAtom phase context atom).mapError Sum.inr
    match phase, value with
    | .computation, .error (.formal cause) => throw (Sum.inl cause)
    | _, value => pure value
  match resolved with
  | .error (.inl cause) => pure (.error (.formal cause))
  | .error (.inr fault) => throw fault
  | .ok expression => pure (expression.lowerForEvaluation.evalNumericOperationTree id)
termination_by (sizeOf amount, 0)

private def readRecursiveTimeComponents (phase : Phase) (context : ScalarComputationContext)
    (components : TimeComponentPrefix (Sum (CheckedTimeComponent model) (ScalarTemporalNumericAtom model))) :
    Except ScalarTemporalEvaluationFault TimeConstructionResult :=
  components.evaluateWithSubterm (fun component _ => do
    match component with
    | .inl source => match readScalarTimeComponent { read := context.read, storedText := context.storedText, world := context.world } phase source with
        | .ok value => pure value
        | .error (.stringNotConvertible _ _) => throw .componentNumberInvalid
        | .error _ => pure (.unavailable .malformed)
    | .inr source =>
        match ← readRecursiveScalarAtom phase context source with
        | .error (.formal cause) => pure (.unavailable cause)
        | .error .nonRelevant => pure .nonRelevant
        | .error _ => throw .calendarUnavailable
        | .ok .notEvaluated => pure .empty
        | .ok (.value value fillability) =>
            pure (if fillability.canGrow || fillability.canShrink then .empty
              else .value (temporalShiftAmountToInt32 value))) phase
termination_by (sizeOf components, 0)
decreasing_by
  all_goals first | decreasing_tactic | (apply Prod.Lex.left; simp_all +arith <;> omega)

private def evalScalarTemporalCore (phase : Phase) (context : ScalarComputationContext)
    (expression : ScalarTemporalExpression model) :
    Except ScalarTemporalEvaluationFault (SimpleComparisonOperand ScalarTemporalValue) :=
  let reached (operand : SimpleComparisonOperand ScalarTemporalValue) :
      Except (Sum FormalCause ScalarTemporalEvaluationFault) (SimpleComparisonOperand ScalarTemporalValue) :=
    match phase, operand with
    | .computation, .unknown cause => .error (.inl cause)
    | _, operand => .ok operand
  let result := expression.evalWithResultSubterm
    (fun atom _ => do
      let operand ← (readScalarTemporalAtom model phase context atom).mapError Sum.inr
      reached operand)
    (fun operation _ operands => do
      reached (← (applyScalarTemporalOperation phase context operation operands).mapError Sum.inr))
  match result with
  | .ok operand => .ok operand
  | .error (.inl cause) => .ok (.unknown cause)
  | .error (.inr fault) => .error fault
termination_by (sizeOf expression, 0)
end

mutual
private def scalarTemporalDependencies (storedOnly : Bool)
    (field : FieldId → List α) (entity : CheckedTemporalExtremumOperands model → List α) (expression : ScalarTemporalExpression model) : List α :=
  match expression with
  | .atom source => scalarTemporalAtomDependencies storedOnly field entity source
  | .apply operation first rest =>
      scalarTemporalDependencies storedOnly field entity first ++
        (rest.attach.flatMap fun ⟨source, _⟩ => scalarTemporalDependencies storedOnly field entity source) ++
        scalarTemporalOperationDependencies storedOnly field entity operation
termination_by sizeOf expression

private def scalarTemporalAtomDependencies (storedOnly : Bool)
    (field : FieldId → List α) (entity : CheckedTemporalExtremumOperands model → List α) (atom : ScalarTemporalAtom model) : List α :=
  match atom with
  | .dateConstruction components =>
      (if storedOnly then components.sources.filterMap fun
        | .dateYearField checked => some checked.source.id | _ => none
      else components.fields).flatMap field
  | .valueAsDate source => field source.source.target.id
  | .timeConstruction components => scalarTemporalComponentDependencies storedOnly field entity components
  | .field source => if storedOnly then [] else field source.id
  | .entityExtremum _ source => if storedOnly then [] else entity source
  | .rangeBound _ (.exact source) => if storedOnly then [] else field source.source.id
  | .rangeBound _ (.yearless source) => if storedOnly then [] else field source.source.id
  | _ => []
termination_by sizeOf atom

private def scalarTemporalOperationDependencies (storedOnly : Bool)
    (field : FieldId → List α) (entity : CheckedTemporalExtremumOperands model → List α) (operation : ScalarTemporalTransform model) : List α :=
  match operation with
  | .subdayShift _ _ amount | .calendarShift _ _ amount =>
      match amount.mapMSubterm (fun atom _ => (Except.ok (scalarTemporalNumericDependencies storedOnly field entity atom) : Except Empty (List α))) with
      | .ok result => result.atoms.flatten
      | .error error => nomatch error
  | _ => []
termination_by sizeOf operation

private def scalarTemporalNumericDependencies (storedOnly : Bool)
    (field : FieldId → List α) (entity : CheckedTemporalExtremumOperands model → List α) (atom : ScalarTemporalNumericAtom model) : List α :=
  match atom with
  | .ordinary source => if storedOnly then [] else source.fieldDependencies.flatMap field
  | .projection _ _ source => scalarTemporalDependencies storedOnly field entity source
termination_by sizeOf atom

private def scalarTemporalComponentDependency (storedOnly : Bool)
    (field : FieldId → List α) (entity : CheckedTemporalExtremumOperands model → List α)
    (component : Sum (CheckedTimeComponent model) (ScalarTemporalNumericAtom model)) : List α :=
  match component with
  | .inl source => if storedOnly then [] else source.fieldDependencies.flatMap field
  | .inr source => scalarTemporalNumericDependencies storedOnly field entity source
termination_by sizeOf component

private def scalarTemporalComponentDependencies (storedOnly : Bool)
    (field : FieldId → List α) (entity : CheckedTemporalExtremumOperands model → List α)
    (components : TimeComponentPrefix (Sum (CheckedTimeComponent model) (ScalarTemporalNumericAtom model))) : List α :=
  match components with
  | .empty => []
  | .hour hour => scalarTemporalComponentDependency storedOnly field entity hour
  | .minute hour minute => scalarTemporalComponentDependency storedOnly field entity hour ++ scalarTemporalComponentDependency storedOnly field entity minute
  | .second hour minute second => scalarTemporalComponentDependency storedOnly field entity hour ++
      scalarTemporalComponentDependency storedOnly field entity minute ++ scalarTemporalComponentDependency storedOnly field entity second
termination_by sizeOf components
end

namespace CheckedScalarTemporalExpression

/-- Stored-text requirements include recursively nested temporal operands. -/
def storedTextFields (expression : CheckedScalarTemporalExpression model) : List FieldId :=
  scalarTemporalDependencies true (fun field => [field]) (·.fieldIds) expression.core

def fieldIds (expression : CheckedScalarTemporalExpression model) : List FieldId :=
  scalarTemporalDependencies false (fun field => [field]) (·.fieldIds) expression.core

/-- Dependencies below a star remain scheduler inputs, but the star binds those row levels itself. -/
def bindingScopes (expression : CheckedScalarTemporalExpression model) : List (List RepeatableLevel) :=
  scalarTemporalDependencies false
    (fun field => ((model.lookupUniqueId field).toOption.map (·.repeatableScope)).toList)
    (·.bindingScopes) expression.core

def boundFieldIds (expression : CheckedScalarTemporalExpression model) : List FieldId :=
  scalarTemporalDependencies false (fun field => [field]) (·.boundFieldIds) expression.core

/-- Expanded operands need topology and selected row reads; a flat validation carrier must defer
these expressions to the existing addressed extrema carrier. -/
def requiresAddressed (expression : CheckedScalarTemporalExpression model) : Bool :=
  (scalarTemporalDependencies false (fun _ => []) (fun source =>
    [source.shape.operands.any fun | .field .. => false | _ => true]) expression.core).any id

def referencesField (expression : CheckedScalarTemporalExpression model) (field : FieldId) : Bool :=
  expression.fieldIds.contains field

/-- Model-zone literal resolution belongs to execution, retaining value failure separately from
missingness and operand poison (the DateTime constant zone-split checkpoint, spec/09). -/
def evalResult (expression : CheckedScalarTemporalExpression model) (phase : Phase) (context : FlatContext)
    (addressed : Option ComputationFillContext := none) (row : Env := []) :
    Except ScalarTemporalEvaluationFault (SimpleComparisonOperand ScalarTemporalValue) :=
  evalScalarTemporalCore phase
    { read := context.read, storedText := context.storedText, world := context.world, addressed, row } expression.core

end CheckedScalarTemporalExpression

namespace CheckedScalarTemporalComparison

def fieldIds (comparison : CheckedScalarTemporalComparison model) : List FieldId :=
  comparison.left.fieldIds ++ comparison.right.fieldIds

def bindingScopes (comparison : CheckedScalarTemporalComparison model) : List (List RepeatableLevel) :=
  comparison.left.bindingScopes ++ comparison.right.bindingScopes

def declarations (comparison : CheckedScalarTemporalComparison model) : List FlatFieldDecl :=
  comparison.fieldIds.filterMap fun field => (model.lookupUniqueId field).toOption

def referencesField (comparison : CheckedScalarTemporalComparison model) (field : FieldId) : Bool :=
  comparison.fieldIds.contains field

/-- Mixed Date/DateTime ordering uses the Date's retained instant; same-family comparison
keeps its existing identity domain (KF386 and the comparison-guard grid, 2026-10-04). -/
private def readOperand (comparison : CheckedScalarTemporalComparison model) (phase : Phase)
    (context : FlatContext) (addressed : Option ComputationFillContext) (row : Env)
    (expression : CheckedScalarTemporalExpression model) :
    Except ScalarTemporalEvaluationFault (SimpleComparisonOperand ScalarTemporalValue) := do
  let operand ← expression.evalResult phase context addressed row
  match comparison.comparisonZone?, operand with
  | _, .value .noValue _ => pure .notEvaluated
  | some _, .value (.date date) given => pure (.value (.instant date.instant) given)
  | _, _ => pure operand

/-- Temporal guards use the shared ordered computation comparison, preserving label failure as a
runtime effect and aborting on a reached operand poison (comparison-guard grid, 2026-10-04). -/
def evalComputation (comparison : CheckedScalarTemporalComparison model)
    (context : FlatContext) (addressed : Option ComputationFillContext := none) (row : Env := []) : Except ScalarTemporalEvaluationFault ComputationConditionResult :=
  evalComputationComparisonExcept (ScalarTemporalValue.holds comparison.operator)
    (comparison.readOperand .computation context addressed row comparison.left)
    (fun _ => comparison.readOperand .computation context addressed row comparison.right)

/-- Retain runtime label failure outside the comparison verdict; the enclosing rule owns its
value-error projection (temporal review grid, 2026-10-03). -/
def evalResult (comparison : CheckedScalarTemporalComparison model) (phase : Phase)
    (context : FlatContext) (addressed : Option ComputationFillContext := none) (row : Env := []) : Except ScalarTemporalEvaluationFault Verdict := do
  match phase with
  | .computation => pure (match ← comparison.evalComputation context addressed row with
      | .holds => .fired .value
      | .notTrue => .notFired
      | .poison _ => .unknown)
  | .validation =>
      let left ← comparison.readOperand phase context addressed row comparison.left
      let right ← comparison.readOperand phase context addressed row comparison.right
      match left, right with
      | .value .nonRelevant _, _ | _, .value .nonRelevant _ => pure .unknown
      | _, _ => pure (evalSymmetricComparison (ScalarTemporalValue.holds comparison.operator) left right)

def evalAt (comparison : CheckedScalarTemporalComparison model) (phase : Phase)
    (context : FlatContext) (addressed : Option ComputationFillContext := none) (row : Env := []) : Verdict :=
  match comparison.evalResult phase context addressed row with
  | .ok verdict => verdict
  | .error .dateTimeLabelUnresolved | .error .componentNumberInvalid => .fired .value
  | .error .calendarUnavailable | .error .indexedOperandNotSupported => .unknown

def eval (comparison : CheckedScalarTemporalComparison model) (context : FlatContext) (addressed : Option ComputationFillContext := none) (row : Env := []) : Verdict :=
  comparison.evalAt .validation context addressed row

end CheckedScalarTemporalComparison

end A12Kernel
