import A12Kernel.Elaboration.TemporalExpression.Reads
import A12Kernel.Elaboration.TemporalExpression.Dependencies

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
  | .indexed authored => do
      let source ← (elaborateSemanticIndexSource model rowGroup authored
        (targetGroup?.map model.repeatableScopeForGroupPath)).mapError .indexed
      let some field := source.targetDeclaration.toTemporalField? | throw (.nonTemporal source.targetDeclaration.path)
      if source.targetDeclaration.toTemporalTargetPolicy?.any (·.partialMode != .full) then
        throw .unsupportedSource
      pure (.atom (.indexed source), scalarComponents model field.components)
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
        let source : AuthoredDateLiteral := { year := none, month := value.month, day := value.day }
        let some value := source.completedParts? model | throw .unsupportedSource
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
  | .indexedRangeBound authored bound => do
      let source ← (elaborateDateRangeSemanticIndexSource model rowGroup authored
        (targetGroup?.map model.repeatableScopeForGroupPath)).mapError .indexedRangeBound
      pure (.atom (.indexedRangeBound (← scalarProfile model) source bound),
        (source.policy.endpointComponents source.format).withBaseYear model.hasBaseYear)
  | .baseYearBound bound => do
      let some year := model.baseYear | throw .unsupportedSource
      pure (.atom (.baseYearBound (← scalarProfile model) year bound), TemporalComponents.fullDate)
  | .valueAsDate reference endpoint => do
      let declaration ← (model.resolveFieldDeclarationUnchecked rowGroup reference).mapError .read
      let scope := targetGroup?.map model.repeatableScopeForGroupPath |>.getD []
      let source ← (elaborateZonedValueAsDateSource model declaration.id endpoint scope).mapError .partialDate
      pure (.atom (.valueAsDate source), TemporalComponents.fullDate)
  | .indexedValueAsDate authored endpoint => do
      let selection ← (elaborateSemanticIndexSource model rowGroup authored
        (targetGroup?.map model.repeatableScopeForGroupPath)).mapError .indexed
      let source ← (elaborateZonedValueAsDateSource model selection.targetDeclaration.id endpoint
        selection.targetDeclaration.repeatableScope).mapError .partialDate
      if sameTarget : source.source.target.id = selection.targetDeclaration.id then
        pure (.atom (.indexedValueAsDate { selection, source, sameTarget }), TemporalComponents.fullDate)
      else throw .unsupportedSource
  | .dateTimeConstruction date time => do
      if !date.admittedSourceSlot .withPartialDate || !time.admittedSourceSlot .ordinary then throw .unsupportedSource
      let (date, dateComponents) ← resolveScalarTemporalExpression model rowGroup targetGroup? date
      let (time, timeComponents) ← resolveScalarTemporalExpression model rowGroup targetGroup? time
      if !dateComponents.hasDate || !dateComponents.year || dateComponents.hasTime ||
          timeComponents.hasDate || !timeComponents.hasTime then throw .incompatibleFormats
      pure (.apply (.dateTime (← scalarProfile model)) date [time], TemporalComponents.now)
  | .dateConstruction source => do
      let components ← resolveScalarDateComponents model rowGroup targetGroup? source
      pure (.atom (.dateConstruction components), TemporalComponents.fullDate)
  | .calendarShift unit source amount => do
      if !source.admittedSourceSlot .withPartialDate then throw .unsupportedSource
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
      if !source.admittedSourceSlot .ordinary then throw .unsupportedSource
      let (source, components) ← resolveScalarTemporalExpression model rowGroup targetGroup? source
      if !components.isFullDateTime then throw .incompatibleFormats
      pure (.apply (.dateFromDateTime (← scalarProfile model)) source [], TemporalComponents.fullDate)
  | .timeFromDateTime source => do
      if !source.admittedSourceSlot .ordinary then throw .unsupportedSource
      let (source, components) ← resolveScalarTemporalExpression model rowGroup targetGroup? source
      if !components.isFullDateTime then throw .incompatibleFormats
      pure (.apply (.timeFromDateTime (← scalarProfile model)) source [], TemporalComponents.time)
  | .subdayShift unit source amount => do
      if !source.admittedSourceSlot .withPartialDate then throw .unsupportedSource
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
  if !surface.admittedSourceSlot .ordinary then throw .unsupportedSource
  match surface with
  | .field reference => do
      let declaration ← (match targetGroup? with
        | none => model.resolveFieldValueRead rowGroup reference
        | some targetGroup => model.resolveComputationFieldValueRead rowGroup targetGroup reference).mapError .read
      if !declaration.admitsTemporalPartPrecision part then
        throw (.temporalPartPrecision declaration.path part)
      if declaration.toTemporalTargetPolicy?.any (·.partialMode != .full) then
        let some field := declaration.toTemporalField? | throw (.nonTemporal declaration.path)
        let format := model.temporalNumericPartialFormat field.id
        if !model.admitsTemporalNumericPart field part format then throw .incompatibleFormats
        return .numeric (.temporalPart .inner field part format)
  | .indexed authored => do
      let selection ← (elaborateSemanticIndexSource model rowGroup authored
        (targetGroup?.map model.repeatableScopeForGroupPath)).mapError .indexed
      let declaration := selection.targetDeclaration
      if !declaration.admitsTemporalPartPrecision part then
        throw (.temporalPartPrecision declaration.path part)
      if declaration.toTemporalTargetPolicy?.any (·.partialMode != .full) then
        let some field := declaration.toTemporalField? | throw (.nonTemporal declaration.path)
        let format := model.temporalNumericPartialFormat field.id
        if !model.admitsTemporalNumericPart field part format then throw .incompatibleFormats
        return .indexedPart selection part format
  | _ => pure ()
  let (source, components) ← resolveScalarTemporalExpression model rowGroup targetGroup? surface
  if !part.admitsComponents components model.hasBaseYear then throw .incompatibleFormats
  pure (.projection part (← scalarProfile model) source)
termination_by (sizeOf surface, 1)

private def resolveScalarTemporalAmount (model : FlatModel) (rowGroup : GroupPath)
    (targetGroup? : Option GroupPath)
    (surface : AuthoredNumericExpr (Sum (SurfaceHavingNumericAtomOf SurfaceScalarTemporalExpression) SurfaceFilteredShiftAmount)) :
    Except ScalarTemporalExpressionError (AuthoredNumericExpr (ScalarTemporalNumericAtom model)) := do
  let scope := model.repeatableScopeForGroupPath (targetGroup?.getD rowGroup)
  let resolvers := model.havingNumericResolvers rowGroup scope scope
  let core ← surface.mapMSubterm fun authored _hAuthored => do
    match _hSum : authored with
    | .inr filtered => do
        let checked ← (elaborateFilteredShiftAmount model rowGroup (targetGroup?.getD rowGroup) filtered).mapError
          .filteredAmount
        if !checked.bindingScopes.all (·.isPrefixOf scope) then throw (.filteredAmount .unbound)
        pure (.filtered checked)
    | .inl atom => do
      match _hProjection : atom with
      | .temporalExpressionPart part source =>
          return ← resolveScalarTemporalProjection model rowGroup targetGroup? source part
      | _ => pure ()
      let resolved ← (resolvers.resolveWith atom
        (fun unit left right _ _ => do
          if !left.admittedSourceSlot .withPartialDate || !right.admittedSourceSlot .withPartialDate then throw .numericExpressionUnsupported
          let (left, first) ← (resolveScalarTemporalExpression model rowGroup targetGroup? left).mapError (fun _ => .numericExpressionUnsupported)
          let (right, second) ← (resolveScalarTemporalExpression model rowGroup targetGroup? right).mapError (fun _ => .numericExpressionUnsupported)
          if !unit.admitsScalarDifference model.hasBaseYear first second then throw .numericExpressionUnsupported
          pure (.temporalDifference unit left right))
        (fun part source _ => do
          let projected ← (resolveScalarTemporalProjection model rowGroup targetGroup? source part).mapError (fun _ => .numericExpressionUnsupported)
          match projected with
          | .projection _ _ core => pure (.temporalExpressionPart part core)
          | _ => throw .numericExpressionUnsupported)).mapError .numeric
      if !(resolved.originsWith (fun _ => [])).all (· == .inner) then throw .unsupportedSource
      if !resolved.admitsTemporalAmountSources model then throw .unsupportedSource
      if !resolved.wellFormedWith model scope scope (fun _ _ _ => true) (fun _ _ => true) then throw .unsupportedSource
      pure (.numeric resolved)
  if !core.isAdmittedResolvedNumericOperation then throw (.amount (.expression .unsupportedExpression))
  match core.numericOperationAuthoringCheck with
  | .accepted => pure ()
  | result => throw (.amount (.expression (.authoring result)))
  let summary : ScalarTemporalNumericAtom model → NumericScaleSummary
    | .numeric source => source.summary
    | .projection _ _ _ | .indexedPart _ _ _ => .field 0
    | .filtered source => source.summary
    | .ordinary (.literal _) => .field 0
    | .ordinary (.field source _) => .field source.info.scale
    | .ordinary (.expression checked _) => (checked.core.summary? numericValidationSummary).getD (.field 0)
  if (core.summary? summary).isNone then throw (.amount (.expression .unsupportedExpression))
  pure core
termination_by (sizeOf surface, 0)
decreasing_by
  all_goals first | decreasing_tactic | (apply Prod.Lex.left; simp_all +arith <;> omega)

private def resolveScalarDateComponent (model : FlatModel) (rowGroup : GroupPath)
    (targetGroup? : Option GroupPath) (position : ConstructedDateComponentPosition)
    (surface : Sum (Sum SurfaceConstructedDateSource SurfaceSemanticIndex) (DateNumericPart × SurfaceScalarTemporalExpression)) :
    Except ScalarTemporalExpressionError (ScalarDateComponent model) := do
  match surface with
  | .inl source =>
      let scope := targetGroup?.map model.repeatableScopeForGroupPath |>.getD []
      .inl <$> elaborateScalarDateLeaf model rowGroup scope position source
  | .inr (part, source) =>
      if position.extractor? != some part then throw .incompatibleFormats
      .inr <$> resolveScalarTemporalProjection model rowGroup targetGroup? source (.date part)
termination_by (sizeOf surface, 0)

private def resolveScalarDateComponents (model : FlatModel) (rowGroup : GroupPath)
    (targetGroup? : Option GroupPath)
    (surface : SurfaceConstructedDateComponents
      (Sum (Sum SurfaceConstructedDateSource SurfaceSemanticIndex) (DateNumericPart × SurfaceScalarTemporalExpression))) :
    Except ScalarTemporalExpressionError (CheckedConstructedDateComponents model (ScalarDateComponent model)) := do
  match selected : ModelZone.ConcreteProfile.ofId? model.timeZoneId with
  | none => throw .unsupportedSource
  | some profile => do
      let day ← resolveScalarDateComponent model rowGroup targetGroup? .day surface.day
      let month ← resolveScalarDateComponent model rowGroup targetGroup? .month surface.month
      let year ← match _yearShape : surface.year with
        | .complete source => .complete <$> resolveScalarDateComponent model rowGroup targetGroup? .year source
        | .baseYear =>
            match model.baseYear with
            | some year => pure (.baseYear year)
            | none => throw (.dateComponents .missingBaseYear)
        | .centuryAndShortYear century shortYear => do
            pure (.centuryAndShortYear
              (← resolveScalarDateComponent model rowGroup targetGroup? .century century)
              (← resolveScalarDateComponent model rowGroup targetGroup? .shortYear shortYear))
      pure { day, month, year, profile, profileSelected := selected }
termination_by (sizeOf surface, 0)
decreasing_by
  all_goals first | decreasing_tactic | (apply Prod.Lex.left; cases surface; simp_all +arith <;> omega)

private def resolveScalarTimeComponent (model : FlatModel) (rowGroup : GroupPath)
    (targetGroup? : Option GroupPath) (position : TimeComponentPosition)
    (surface : SurfaceScalarTimeComponent) :
    Except ScalarTemporalExpressionError (ScalarTimeComponent model) := do
  match surface with
  | .inl (.inl source) =>
      let scope := targetGroup?.map model.repeatableScopeForGroupPath |>.getD []
      let checked ← (elaborateTimeComponent model position source scope).mapError .timeComponents
      pure (.inl (.inl checked))
  | .inl (.inr authored) =>
      let selection ← (elaborateSemanticIndexSource model rowGroup authored
        (targetGroup?.map model.repeatableScopeForGroupPath)).mapError .indexed
      let field := selection.targetDeclaration
      let source ← match field.policy.kind.surfaceKind with
        | .number => pure (SurfaceTimeComponent.number field.id)
        | .string => pure (.string field.id)
        | _ => throw .unsupportedSource
      let source ← (elaborateTimeComponent model position source field.repeatableScope).mapError .timeComponents
      if sameTarget : source.fieldDependencies = [selection.targetDeclaration.id] then
        pure (.inl (.inr { selection, source, sameTarget }))
      else throw .unsupportedSource
  | .inr (part, source) =>
      if position.extractor != part then throw .incompatibleFormats
      .inr <$> resolveScalarTemporalProjection model rowGroup targetGroup? source (.time part)
termination_by (sizeOf surface, 0)

private def resolveScalarTimeComponents (model : FlatModel) (rowGroup : GroupPath)
    (targetGroup? : Option GroupPath)
    (surface : TimeComponentPrefix (SurfaceScalarTimeComponent)) :
    Except ScalarTemporalExpressionError (TimeComponentPrefix (ScalarTimeComponent model)) :=
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

def elaborateScalarTemporalProjection (model : FlatModel) (rowGroup : GroupPath)
    (surface : SurfaceScalarTemporalExpression) (part : TemporalNumericPart)
    (targetGroup? : Option GroupPath := none) :
    Except ScalarTemporalExpressionError (ScalarTemporalNumericAtom model) := do
  discard <| model.validate.mapError .model
  resolveScalarTemporalProjection model rowGroup targetGroup? surface part

def elaborateScalarTemporalExpression (model : FlatModel) (rowGroup : GroupPath)
    (surface : SurfaceScalarTemporalExpression) (targetGroup? : Option GroupPath := none) :
    Except ScalarTemporalExpressionError (CheckedScalarTemporalExpression model) := do
  match h : model.validate with
  | .error error => throw (.model error)
  | .ok () =>
      let (core, components) ← resolveScalarTemporalExpression model rowGroup targetGroup? surface
      pure { core, components, modelWellFormed := by rw [h]; rfl }


def elaborateScalarDateValidityComponents (model : FlatModel) (rowGroup : GroupPath)
    (surface : SurfaceConstructedDateComponents SurfaceScalarDateComponent)
    (targetGroup : GroupPath := rowGroup) :
    Except ScalarTemporalExpressionError (CheckedConstructedDateComponents model (ScalarDateComponent model)) := do
  let components ← resolveScalarDateComponents model rowGroup (some targetGroup) surface
  if !components.hasImmediateEntity then throw (.dateComponents .onlyConstantsUsed)
  pure components

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


/-- Whether a partial call evaluates an aggregate or filled-field-count shift amount such as
`Sum(Rows*/N)`: each walked extent member passes the all-rows aggregate gate, and each direct slot is
relevant at the bound row. Wildcard relevance of the column or its group passes; one concrete row, or
concrete group rows beside the wildcard, does not, alike for `Sum`, `MaxValue`, `MinValue`,
`NumberOfDifferentValues` and `NumberOfFilledFields` (k22-runtime-r7-2026-10-24, `rC`, `KS3`,
`KX5`–`KX8`). `none` for any other amount: no other expanded amount is measured under partial
validation, so each keeps its structural refusal. -/
private def partialAggregateAmountCovered (context : ScalarComputationContext)
    (partialRead : TemporalPartialReadContext model)
    (atom : HavingNumericAtomOf (ScalarTemporalExpression model)) :
    Except ScalarTemporalEvaluationFault (Option Bool) := do
  match atom with
  | .aggregate _ _ | .collectionCount (.filledFields _ _) => pure ()
  | _ => return none
  let scope := partialRead.effectiveScope
  let memberCovered (bound : Nat) (field : FieldId) : Bool :=
    (model.lookupUniqueId field).toOption.any fun declaration =>
      scope.coversAggregateExtent model declaration.path (declaration.repeatableScope.take bound)
        (declaration.repeatableScope.drop bound) context.row
  let slotCovered (slot : HavingFieldListSlot HavingPresenceRef) :
      Except ScalarTemporalEvaluationFault Bool := match slot with
    | .direct reference => return (← partialRead.readCell context.row reference.field).isSome
    | .extent source references => return references.all (memberCovered source.boundCount ·.field)
  pure (some (← (atom.presenceSlotsWith (fun _ _ => [])).allM slotCovered))

mutual
private def readScalarTemporalAtom (model : FlatModel) (phase : Phase) (context : ScalarComputationContext)
    (partialRead? : Option (TemporalPartialReadContext model))
    (filtered : FilteredShiftAmountReader model)
    (atom : ScalarTemporalAtom model) :
    Except ScalarTemporalEvaluationFault (SimpleComparisonOperand ScalarTemporalValue) := do
  if let some partialRead := partialRead? then
    if let some result := readPartialScalarTemporalAtom context partialRead atom then return ← result
  match atom with
  | .indexed source =>
      let some field := source.targetDeclaration.toTemporalField? | throw .calendarUnavailable
      let observation ← (source.observeColumnWith phase context.semanticIndexColumnReader
        context.row context.read context.storedText).mapError (fun _ => .calendarUnavailable)
      pure (projectScalarTemporalObservation model field observation)
  | .dateTimeLiteral profile value =>
      match profile.resolveCalendarLabel? value with
      | some instant => pure (.value (.instant instant) true)
      | none => throw .dateTimeLabelUnresolved
  | .dateLiteral profile value yearPresent =>
      match profile.resolveCompletedDateParts? value with
      | some value => pure (.value (if yearPresent || model.hasBaseYear then .date value else
          .yearless value { month := value.parts.month, day := value.parts.day }) true)
      | none => throw .dateTimeLabelUnresolved
  | .fixed value => pure (.value value true)
  | .baseYearBound profile year bound =>
      match profile.resolveCompletedDateParts? (baseYearRangeParts year bound) with
      | some value => pure (.value (.date value) true)
      | none => throw .calendarUnavailable
  | .rangeBound profile source => readScalarRangeBound phase profile source context.read
  | .indexedRangeBound profile source bound => do
      let observation ← (source.toCheckedSemanticIndexSource.observeColumnWith phase
        context.semanticIndexColumnReader context.row context.read context.storedText).mapError
          (fun _ => .calendarUnavailable)
      (projectScalarRangeBoundObservation profile (!source.exactDomain) bound observation).mapError
        ScalarTemporalPrimitiveFault.toEvaluation
  | .now => pure (match context.world with
      | some world => .value (.instant world.now) true
      | none => .unknown .malformed)
  | .today profile => pure (match context.world.bind (fun world => profile.todayLabel? world.now) with
      | some (parts, instant) => .value (.date { instant, parts, basis := .storedGregorian }) true
      | none => .unknown .malformed)
  | .valueAsDate source =>
      readScalarValueAsDate phase source (context.read source.source.target.id)
        (context.storedText source.source.target.id)
  | .indexedValueAsDate source => do
      let some addressed := context.addressed | throw .calendarUnavailable
      match ← (source.selection.selectEnvironmentWith phase context.semanticIndexColumnReader
          context.row context.read context.storedText).mapError (fun _ => .calendarUnavailable) with
      | .empty => pure .notEvaluated
      | .unknown cause | .poison cause => pure (.unknown cause)
      | .value row =>
          readScalarValueAsDate phase source.source (addressed.read row source.selection.targetDeclaration.id)
            (addressed.storedText row source.selection.targetDeclaration.id)
  | .dateConstruction components => readRecursiveDateComponents phase context partialRead? filtered components
  | .timeConstruction components => do
      pure (← readRecursiveTimeComponents phase context partialRead? filtered components).asScalarTemporalOperand
  | .field field => pure (readScalarTemporalField model phase field (context.read field.id))
  | .entityExtremum operator source => source.evalScalar operator phase context partialRead?

termination_by (sizeOf atom, 0)

private def applyScalarTemporalTransform (phase : Phase) (context : ScalarComputationContext)
    (partialRead? : Option (TemporalPartialReadContext model))
    (filtered : FilteredShiftAmountReader model)
    (operation : ScalarTemporalTransform model)
    (source : SimpleComparisonOperand ScalarTemporalValue) :
    Except ScalarTemporalEvaluationFault (SimpleComparisonOperand ScalarTemporalValue) := do
  match operation with
  | .calendarShift profile unit amount =>
      let amount ← readRecursiveScalarAmount phase context partialRead? filtered amount
      (applyScalarTemporalShift source amount (shiftScalarTemporalValue profile (match unit with
        | .days => .days | .months => .months | .years => .years))).mapError ScalarTemporalPrimitiveFault.toEvaluation
  | .subdayShift profile unit amount =>
      let amount ← readRecursiveScalarAmount phase context partialRead? filtered amount
      (applyScalarTemporalShift source amount (shiftScalarTemporalValue profile (match unit with
        | .hours => .hours | .minutes => .minutes | .seconds => .seconds))).mapError ScalarTemporalPrimitiveFault.toEvaluation
  | .dateFromDateTime profile =>
      (ScalarTemporalConstructorOp.dateFromDateTime.apply profile [source]).mapError ScalarTemporalPrimitiveFault.toEvaluation
  | .timeFromDateTime profile =>
      (ScalarTemporalConstructorOp.timeFromDateTime.apply profile [source]).mapError ScalarTemporalPrimitiveFault.toEvaluation
  | .extremum _ | .dateTime _ => throw .calendarUnavailable

termination_by (sizeOf operation, 0)

/-- Constructor arguments have already been reached by the shared ordered application. A missing
payload keeps its own provenance; non-relevance suppresses a result without inventing a formal cause. -/
private def applyScalarTemporalOperation (phase : Phase) (context : ScalarComputationContext)
    (partialRead? : Option (TemporalPartialReadContext model))
    (filtered : FilteredShiftAmountReader model)
    (operation : ScalarTemporalTransform model)
    (operands : List (SimpleComparisonOperand ScalarTemporalValue)) :
    Except ScalarTemporalEvaluationFault (SimpleComparisonOperand ScalarTemporalValue) :=
  match _h : operation, operands with
  | .extremum operator, operands => pure (evalTemporalExtremumAggregate (ScalarTemporalValue.select operator)
      { operands, hasUninstantiatedTail := false, hasHaving := false })
  | .dateTime profile, [date, time] =>
      (ScalarTemporalConstructorOp.dateTime.apply profile [date, time]).mapError ScalarTemporalPrimitiveFault.toEvaluation
  | _, [source] => applyScalarTemporalTransform phase context partialRead? filtered operation source
  | _, _ => throw .calendarUnavailable

termination_by (sizeOf operation, 1)
decreasing_by
  all_goals simp_all
  all_goals apply Prod.Lex.right
  all_goals omega

private def readRecursiveScalarAtom (phase : Phase) (context : ScalarComputationContext)
    (partialRead? : Option (TemporalPartialReadContext model))
    (filtered : FilteredShiftAmountReader model)
    (atom : ScalarTemporalNumericAtom model) : Except ScalarTemporalEvaluationFault
      (Except NumericValidationUnavailable NumericArithmeticOutcome) := do
  match atom with
  | .numeric atom =>
      let some profile := ModelZone.ConcreteProfile.ofId? model.timeZoneId | throw .calendarUnavailable
      -- A covered aggregate amount walks its extent over the checked document as full validation
      -- does: the gate has made every member it reads relevant.
      let (context, partialRead?) ← match partialRead? with
        | some partialRead =>
            match ← partialAggregateAmountCovered context partialRead atom with
            | some false => return .error .nonRelevant
            | some true => pure ({ (partialRead.document.indexedComputationContextAt context.row) with
                world := context.world }, none)
            | none => pure (context, partialRead?)
        | none => pure (context, none)
      let result := atom.readArithmetic phase (scalarAmountReadContext context partialRead?)
        { innerEnv := context.row, outerEnv := context.row }
        (fun part source _ => do
          let result ← (evalScalarTemporalCore phase context partialRead? filtered source).mapError some
          (part.observeScalar profile result).mapError some)
        (fun unit left right _ _ => do
          let pair ← (readTemporalPair phase (fun first : Bool =>
            if first then evalScalarTemporalCore phase context partialRead? filtered left
            else evalScalarTemporalCore phase context partialRead? filtered right)
            scalarTemporalFormalCause? true false).mapError some
          match pair with
          | .error cause => pure (.error (.formal cause))
          | .ok (first, second) =>
              (observeScalarTemporalDifference profile unit first second NumericValidationUnavailable.formal .nonRelevant)
                |>.mapError (some ∘ ScalarTemporalPrimitiveFault.toEvaluation))
      match result with
      | .error none => pure (.error .nonRelevant)
      | .error (some fault) => throw fault
      | .ok value => pure value
  | .indexedPart selection part format => do
      let some field := selection.targetDeclaration.toTemporalField? | throw .calendarUnavailable
      let operand ← match partialRead? with
        | some partialRead => do
            match ← partialRead.selectedCell selection context.row with
            | none => return .error .nonRelevant
            | some .empty => pure CellObservation.empty
            | some (.unknown cause) | some (.poison cause) => pure (.unknown cause)
            | some (.value (cell, _)) => pure (observeCell .validation cell)
        | none => do
            let some addressed := context.addressed | throw .calendarUnavailable
            match ← (selection.selectEnvironmentWith phase context.semanticIndexColumnReader
                context.row context.read context.storedText).mapError (fun _ => .calendarUnavailable) with
            | .empty => pure CellObservation.empty
            | .unknown cause | .poison cause => pure (.unknown cause)
            | .value row => pure (observeCell phase (addressed.read row field.id))
      pure ((operand.asStoredTemporalNumericOperand field part format).toValidationArithmetic)
  | .ordinary amount => match partialRead? with
      | some partialRead => readPartialScalarTemporalAmount partialRead context.row amount
      | none => pure (readScalarTemporalAmount { read := context.read, storedText := context.storedText, world := context.world } phase amount)
  | .filtered source => filtered source
  | .projection part profile source => part.observeScalar profile (← evalScalarTemporalCore phase context partialRead? filtered source)
termination_by (sizeOf atom, 0)

private def readRecursiveScalarAmount (phase : Phase) (context : ScalarComputationContext)
    (partialRead? : Option (TemporalPartialReadContext model))
    (filtered : FilteredShiftAmountReader model)
    (amount : AuthoredNumericExpr (ScalarTemporalNumericAtom model)) : Except ScalarTemporalEvaluationFault
      (Except NumericValidationUnavailable NumericArithmeticOutcome) := do
  let resolved := amount.mapMSubterm fun atom _ => do
    let value ← (readRecursiveScalarAtom phase context partialRead? filtered atom).mapError Sum.inr
    match phase, value with
    | .computation, .error (.formal cause) => throw (Sum.inl cause)
    | _, value => pure value
  match resolved with
  | .error (.inl cause) => pure (.error (.formal cause))
  | .error (.inr fault) => throw fault
  | .ok expression => pure (expression.lowerForEvaluation.evalNumericOperationTree id)
termination_by (sizeOf amount, 0)

private def readRecursiveDateComponent (phase : Phase) (context : ScalarComputationContext)
    (partialRead? : Option (TemporalPartialReadContext model))
    (filtered : FilteredShiftAmountReader model)
    (component : ScalarDateComponent model) :
    StateT DateComponentRelevance (Except ScalarTemporalEvaluationFault) CheckedConstructedDateComponent := do
  match component with
  | .inl source => match partialRead? with
      | none => liftM (readScalarDateLeaf phase context source)
      | some partialRead =>
          match ← liftM (readPartialScalarDateLeaf context partialRead source) with
          | some value => pure value
          | none => set DateComponentRelevance.nonRelevant *> pure .empty
  | .inr source =>
      observeScalarDateComponent (← liftM (readRecursiveScalarAtom phase context partialRead? filtered source))
termination_by (sizeOf component, 0)

private def observeRecursiveDateComponents (phase : Phase) (context : ScalarComputationContext)
    (partialRead? : Option (TemporalPartialReadContext model))
    (filtered : FilteredShiftAmountReader model)
    (components : CheckedConstructedDateComponents model (ScalarDateComponent model)) :
    Except ScalarTemporalEvaluationFault (ConstructedDateObservation × DateComponentRelevance) :=
  (components.attach.evaluateComponentsWith
    (fun ⟨source, _⟩ => readRecursiveDateComponent phase context partialRead? filtered source) phase).run .relevant
termination_by (sizeOf components, 0)
decreasing_by
  all_goals apply Prod.Lex.left
  all_goals assumption

private def readRecursiveDateComponents (phase : Phase) (context : ScalarComputationContext)
    (partialRead? : Option (TemporalPartialReadContext model))
    (filtered : FilteredShiftAmountReader model)
    (components : CheckedConstructedDateComponents model (ScalarDateComponent model)) :
    Except ScalarTemporalEvaluationFault (SimpleComparisonOperand ScalarTemporalValue) := do
  let (observation, relevance) ← observeRecursiveDateComponents phase context partialRead? filtered components
  finishScalarDateComponents components observation relevance
termination_by (sizeOf components, 1)
decreasing_by
  all_goals apply Prod.Lex.right
  all_goals omega

private def readRecursiveTimeComponents (phase : Phase) (context : ScalarComputationContext)
    (partialRead? : Option (TemporalPartialReadContext model))
    (filtered : FilteredShiftAmountReader model)
    (components : TimeComponentPrefix (ScalarTimeComponent model)) :
    Except ScalarTemporalEvaluationFault TimeConstructionResult :=
  components.evaluateWithSubterm (fun component _ => do
    match _hComponent : component with
    | .inl source => match partialRead? with
        | some partialRead => readPartialScalarTimeLeaf context partialRead source
        | none => readScalarTimeLeaf phase context source
    | .inr source =>
        match ← readRecursiveScalarAtom phase context partialRead? filtered source with
        | .error (.formal cause) => pure (constructorComponentOfNumeric (.error (some cause)))
        | .error .nonRelevant => pure (constructorComponentOfNumeric (.error none))
        | .error _ => throw .calendarUnavailable
        | .ok value => pure (constructorComponentOfNumeric (.ok value))) phase
termination_by (sizeOf components, 0)
decreasing_by
  all_goals first | decreasing_tactic | (apply Prod.Lex.left; simp_all +arith <;> omega)

private def evalScalarTemporalCore (phase : Phase) (context : ScalarComputationContext)
    (partialRead? : Option (TemporalPartialReadContext model))
    (filtered : FilteredShiftAmountReader model)
    (expression : ScalarTemporalExpression model) :
    Except ScalarTemporalEvaluationFault (SimpleComparisonOperand ScalarTemporalValue) :=
  let reached (operand : SimpleComparisonOperand ScalarTemporalValue) :
      Except (Sum FormalCause ScalarTemporalEvaluationFault) (SimpleComparisonOperand ScalarTemporalValue) :=
    match phase, operand with
    | .computation, .unknown cause => .error (.inl cause)
    | _, operand => .ok operand
  let result := expression.evalWithResultSubterm
    (fun atom _ => do
      let operand ← (readScalarTemporalAtom model phase context partialRead? filtered atom).mapError Sum.inr
      reached operand)
    (fun operation _ operands => do
      reached (← (applyScalarTemporalOperation phase context partialRead? filtered operation operands).mapError Sum.inr))
  match result with
  | .ok operand => .ok operand
  | .error (.inl cause) => .ok (.unknown cause)
  | .error (.inr fault) => .error fault
termination_by (sizeOf expression, 0)
end

def CheckedConstructedDateComponents.evaluateScalarValidity
    (components : CheckedConstructedDateComponents model (ScalarDateComponent model))
    (phase : Phase) (context : ScalarComputationContext)
    (partialRead? : Option (TemporalPartialReadContext model) := none)
    (filtered : FilteredShiftAmountReader model := .unavailable) :
    Except ScalarTemporalEvaluationFault ConstructedDateObservation := do
  let (observation, relevance) ← observeRecursiveDateComponents phase context partialRead? filtered components
  finishScalarDateValidity components observation relevance

def ScalarTemporalNumericAtom.evalResult (atom : ScalarTemporalNumericAtom model) (phase : Phase)
    (context : FlatContext) (addressed : Option ComputationFillContext := none) (row : Env := [])
    (partialRead? : Option (TemporalPartialReadContext model) := none)
    (filtered : FilteredShiftAmountReader model := .unavailable) :
    Except ScalarTemporalEvaluationFault (Except NumericValidationUnavailable NumericArithmeticOutcome) :=
  readRecursiveScalarAtom phase
    { read := context.read, storedText := context.storedText, world := context.world, addressed, row } partialRead? filtered atom

namespace CheckedScalarTemporalExpression

def storedTextFields (expression : CheckedScalarTemporalExpression model) : List FieldId :=
  expression.core.storedTextFields

def fieldIds (expression : CheckedScalarTemporalExpression model) : List FieldId := expression.core.fieldIds

def bindingScopes (expression : CheckedScalarTemporalExpression model) : List (List RepeatableLevel) :=
  expression.core.bindingScopes

def boundFieldIds (expression : CheckedScalarTemporalExpression model) : List FieldId := expression.core.boundFieldIds

def requiresAddressed (expression : CheckedScalarTemporalExpression model) : Bool := expression.core.requiresAddressed

def referencesWith (expression : CheckedScalarTemporalExpression model) (field : FieldId)
    (filterReads : CorrelatedHaving → Bool) : Bool :=
  expression.core.referencesWith field filterReads

def referencesField (expression : CheckedScalarTemporalExpression model) (field : FieldId) : Bool :=
  expression.referencesWith field (·.referencesField field)

/-- Model-zone literal resolution belongs to execution, retaining value failure separately from
missingness and operand poison (the DateTime constant zone-split checkpoint, spec/09). -/
def evalResult (expression : CheckedScalarTemporalExpression model) (phase : Phase) (context : FlatContext)
    (addressed : Option ComputationFillContext := none) (row : Env := [])
    (partialRead? : Option (TemporalPartialReadContext model) := none)
    (filtered : FilteredShiftAmountReader model := .unavailable) :
    Except ScalarTemporalEvaluationFault (SimpleComparisonOperand ScalarTemporalValue) :=
  evalScalarTemporalCore phase
    { read := context.read, storedText := context.storedText, world := context.world, addressed, row } partialRead? filtered expression.core

end CheckedScalarTemporalExpression

namespace CheckedScalarTemporalComparison

def fieldIds (comparison : CheckedScalarTemporalComparison model) : List FieldId :=
  comparison.left.fieldIds ++ comparison.right.fieldIds

def bindingScopes (comparison : CheckedScalarTemporalComparison model) : List (List RepeatableLevel) :=
  comparison.left.bindingScopes ++ comparison.right.bindingScopes

def declarations (comparison : CheckedScalarTemporalComparison model) : List FlatFieldDecl :=
  comparison.fieldIds.filterMap fun field => (model.lookupUniqueId field).toOption

def referencesWith (comparison : CheckedScalarTemporalComparison model) (field : FieldId)
    (filterReads : CorrelatedHaving → Bool) : Bool :=
  comparison.left.referencesWith field filterReads || comparison.right.referencesWith field filterReads

def referencesField (comparison : CheckedScalarTemporalComparison model) (field : FieldId) : Bool :=
  comparison.referencesWith field (·.referencesField field)

/-- Mixed Date/DateTime ordering uses the Date's retained instant; same-family comparison
keeps its existing identity domain (KF386 and the comparison-guard grid, 2026-10-04). -/
private def readOperand (comparison : CheckedScalarTemporalComparison model) (phase : Phase)
    (context : FlatContext) (addressed : Option ComputationFillContext) (row : Env)
    (expression : CheckedScalarTemporalExpression model)
    (partialRead? : Option (TemporalPartialReadContext model) := none)
    (filtered : FilteredShiftAmountReader model := .unavailable) :
    Except ScalarTemporalEvaluationFault (SimpleComparisonOperand ScalarTemporalValue) := do
  let operand ← expression.evalResult phase context addressed row partialRead? filtered
  match comparison.comparisonZone?, operand with
  | _, .value .noValue _ => pure .notEvaluated
  | some _, .value (.date date) given => pure (.value (.instant date.instant) given)
  | _, _ => pure operand

/-- Temporal guards use the shared ordered computation comparison, preserving label failure as a
runtime effect and aborting on a reached operand poison (comparison-guard grid, 2026-10-04). -/
def evalComputation (comparison : CheckedScalarTemporalComparison model)
    (context : FlatContext) (addressed : Option ComputationFillContext := none) (row : Env := [])
    (filtered : FilteredShiftAmountReader model := .unavailable) : Except ScalarTemporalEvaluationFault ComputationConditionResult :=
  evalComputationComparisonExcept (ScalarTemporalValue.holds comparison.operator)
    (comparison.readOperand .computation context addressed row comparison.left (filtered := filtered))
    (fun _ => comparison.readOperand .computation context addressed row comparison.right (filtered := filtered))

/-- Retain runtime label failure outside the comparison verdict; the enclosing rule owns its
value-error projection (temporal review grid, 2026-10-03). -/
def evalResult (comparison : CheckedScalarTemporalComparison model) (phase : Phase)
    (context : FlatContext) (addressed : Option ComputationFillContext := none) (row : Env := [])
    (partialRead? : Option (TemporalPartialReadContext model) := none)
    (filtered : FilteredShiftAmountReader model := .unavailable) : Except ScalarTemporalEvaluationFault Verdict := do
  match phase with
  | .computation => pure (match ← comparison.evalComputation context addressed row filtered with
      | .holds => .fired .value
      | .notTrue => .notFired
      | .poison _ => .unknown)
  | .validation =>
      let left ← comparison.readOperand phase context addressed row comparison.left partialRead? filtered
      let right ← comparison.readOperand phase context addressed row comparison.right partialRead? filtered
      match left, right with
      | .value .nonRelevant _, _ | _, .value .nonRelevant _ => pure .unknown
      | _, _ => pure (evalSymmetricComparison (ScalarTemporalValue.holds comparison.operator) left right)

def evalAt (comparison : CheckedScalarTemporalComparison model) (phase : Phase)
    (context : FlatContext) (addressed : Option ComputationFillContext := none) (row : Env := [])
    (filtered : FilteredShiftAmountReader model := .unavailable) : Verdict :=
  match comparison.evalResult phase context addressed row (filtered := filtered) with
  | .ok verdict => verdict
  | .error .dateTimeLabelUnresolved | .error .componentNumberInvalid => .fired .value
  | .error .calendarUnavailable | .error .indexedOperandNotSupported | .error (.addressing _) => .unknown

def eval (comparison : CheckedScalarTemporalComparison model) (context : FlatContext) (addressed : Option ComputationFillContext := none) (row : Env := []) : Verdict :=
  comparison.evalAt .validation context addressed row

end CheckedScalarTemporalComparison

end A12Kernel
