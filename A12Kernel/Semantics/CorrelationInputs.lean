import A12Kernel.Semantics.HavingNumberAggregate
import A12Kernel.Semantics.HavingTemporalExpression

/-! Correlated numeric atoms and phase-specific checked reads. -/

namespace A12Kernel

/-- Clock and model constants carry no row origin, so arithmetic cannot make them satisfy a filter reference requirement (spec/07 §3). Field and repetition atoms retain their own origins. -/
inductive HavingNumericAtom where
  | aggregate (op : NumericAggregateOp) (slots : List (HavingFieldListSlot HavingNumberRef))
  | dateDifference (unit : DateDifferenceUnit) (left right : ResolvedDateDifferenceOperand HavingTemporalRef)
  | dayDifference (profile : ModelZone.ConcreteProfile) (left right : ResolvedDateDifferenceOperand HavingTemporalRef)
  | dateTimeDifference (unit : DateTimeSubdayUnit) (left right : FlatTemporalOperand HavingTemporalRef)
  | baseYear (year : Int)
  | baseYearDatePart (year : Int) (source : BaseYearDateSource) (part : DateNumericPart)
  | clockPart (source : HavingClockSource) (profile : ModelZone.ConcreteProfile) (part : TemporalNumericPart)
  | fieldValueAsNumber (origin : HavingOrigin) (source : ResolvedFieldValueAsNumberSource)
  | field (reference : HavingNumberRef)
  | stringLength (origin : HavingOrigin) (field : FlatStringField)
  | stringRange (origin : HavingOrigin) (source : FlatStringField) (start finish : Nat)
  | dateRangeBoundPart (origin : HavingOrigin) (source : FlatDateRangeField) (bound : DateRangeBound) (part : DateNumericPart)
  | temporalExpressionPart (part : TemporalNumericPart) (source : HavingTemporalExpression)
  | temporalPart (origin : HavingOrigin) (source : FlatTemporalField) (part : TemporalNumericPart)
  | repetition (reference : HavingRepetitionRef)
  deriving Repr, DecidableEq

def HavingNumericAtom.origins : HavingNumericAtom → List HavingOrigin
  | .temporalExpressionPart _ source => source.references.map (·.origin)
  | .aggregate _ slots => (slots.flatMap (·.references)).map (·.origin)
  | .dateDifference _ left right | .dayDifference _ left right => (left.fields ++ right.fields).map (·.origin)
  | .dateTimeDifference _ left right => (left.fieldValues ++ right.fieldValues).map (·.origin)
  | .baseYear _ | .baseYearDatePart _ _ _ | .clockPart _ _ _ => []
  | .field reference => [reference.origin]
  | .dateRangeBoundPart origin _ _ _ | .fieldValueAsNumber origin _ | .stringLength origin _
      | .stringRange origin _ _ _ | .temporalPart origin _ _ => [origin]
  | .repetition reference => [reference.origin]

/-- Preserve each read's own origin inside a multi-source numeric atom (spec/07 §3). -/
def HavingNumericAtom.fieldOrigins : HavingNumericAtom → List (HavingOrigin × FieldId)
  | .temporalExpressionPart _ source => source.references.map (fun ref => (ref.origin, ref.fieldId))
  | .aggregate _ slots => (slots.flatMap (·.references)).map (fun reference => (reference.origin, reference.field.id))
  | .dateDifference _ left right | .dayDifference _ left right => (left.fields ++ right.fields).map (fun reference => (reference.origin, reference.field.id))
  | .dateTimeDifference _ left right => (left.fieldValues ++ right.fieldValues).map (fun reference => (reference.origin, reference.field.id))
  | .baseYear _ | .baseYearDatePart _ _ _ | .clockPart _ _ _ | .repetition _ => []
  | .dateRangeBoundPart origin source _ _ => [(origin, source.id)]
  | .fieldValueAsNumber origin source => [(origin, source.fieldId)]
  | .field reference => [(reference.origin, reference.field.id)]
  | .stringLength origin source | .stringRange origin source _ _ => [(origin, source.id)]
  | .temporalPart origin source _ => [(origin, source.id)]

def HavingNumericAtom.summary : HavingNumericAtom → NumericScaleSummary
  | .temporalExpressionPart _ _ => .field 0
  | .aggregate .distinctCount _ => .field 0
  | .aggregate _ slots => (slots.flatMap (·.references)).foldl (fun summary reference => summary.union (.field reference.field.info.scale)) (.field 0)
  | .dateDifference _ _ _ | .dayDifference _ _ _ | .dateTimeDifference _ _ _ => .field 0
  | .baseYear _ | .baseYearDatePart _ _ _ | .clockPart _ _ _ => .field 0
  | .fieldValueAsNumber _ source => .field source.scale
  | .field reference => .field reference.field.info.scale
  | .dateRangeBoundPart _ _ _ _ | .repetition _ | .stringLength _ _ | .stringRange _ _ _ _ | .temporalPart _ _ _ => .field 0

/-- Resolve one numeric filter reference through the selected environment and caller-selected phase. Empty-to-zero is local to numeric comparison; formal invalidity retains its cause for the consuming phase projection. -/
def HavingNumberRef.resolveInAt (reference : HavingNumberRef) (phase : Phase)
    (context : CorrelationContext) (frame : CorrelationFrame) :
    CorrelatedNumberOperand :=
  let rowContext : FlatContext :=
    { read := context.read (frame.envAt reference.origin) }
  match rowContext.resolveNumberComparisonOperandAt phase reference.field with
  | .value amount _ => .value amount
  | .unknown cause => .unknown cause

/-- Resolve the same numeric reference without collapsing a structural addressed-read failure into a formal cell observation. -/
def HavingNumberRef.resolveInAtResolving (reference : HavingNumberRef)
    (phase : Phase) (context : ResolvingCorrelationContext Error)
    (frame : CorrelationFrame) : Except Error CorrelatedNumberOperand := do
  let cell ← context.read (frame.envAt reference.origin) reference.field.id
  let rowContext : FlatContext := { read := fun _ => cell }
  pure (match rowContext.resolveNumberComparisonOperandAt phase reference.field with
    | .value amount _ => .value amount
    | .unknown cause => .unknown cause)

/-- Resolve text through the selected environment and phase using its owning domain's observation
    projection, preserving unavailable values and formal invalidity. -/
def HavingStringRef.resolveInAt (reference : HavingStringRef) (phase : Phase)
    (context : CorrelationContext) (frame : CorrelationFrame) :
    SimpleComparisonOperand String :=
  let rowContext : FlatContext :=
    { read := context.read (frame.envAt reference.origin) }
  match reference.operand with
  | .string field => rowContext.resolveStringComparisonOperandAt phase field
  | .enumeration operand => operand.projection.resolveOperand (rowContext.observeAt phase operand.field.id)

/-- Resolve the same text reference without collapsing a structural addressed-read failure into a formal cell observation. -/
def HavingStringRef.resolveInAtResolving (reference : HavingStringRef)
    (phase : Phase) (context : ResolvingCorrelationContext Error)
    (frame : CorrelationFrame) :
    Except Error (SimpleComparisonOperand String) := do
  let cell ← context.read (frame.envAt reference.origin) reference.field.id
  let rowContext : FlatContext := { read := fun _ => cell }
  pure (reference.resolveInAt phase { read := fun _ => rowContext.read } frame)

/-- Observe one presence reference's cell at a chosen phase. Presence needs the observation itself,
    not a comparison operand, so it reads the phase view directly. -/
def HavingPresenceRef.observeInAt (reference : HavingPresenceRef) (phase : Phase)
    (context : CorrelationContext) (frame : CorrelationFrame) : CellObservation :=
  let rowContext : FlatContext :=
    { read := context.read (frame.envAt reference.origin) }
  rowContext.observeAt phase reference.field

/-- Observe the same presence reference without collapsing a structural addressed-read failure. -/
def HavingPresenceRef.observeInAtResolving (reference : HavingPresenceRef)
    (phase : Phase) (context : ResolvingCorrelationContext Error)
    (frame : CorrelationFrame) : Except Error CellObservation := do
  let cell ← context.read (frame.envAt reference.origin) reference.field
  pure (observeCell phase cell)

/-- Both presence polarities delegate to the shared validation observation consumers, so this leaf
    adds no second account of what "filled" means. Neither polarity fires on a formally unavailable
    cell, which is why they are complements only over clean cells. -/
def HavingPresencePolarity.evalObservation :
    HavingPresencePolarity → CellObservation → Verdict
  | .filled => CellObservation.evalValidationFilled
  | .notFilled => CellObservation.evalValidationNotFilled

/-- Resolve one repetition reference through the structural addressed channel. -/
def CorrelationFrame.rowAtResolving (frame : CorrelationFrame)
    (context : ResolvingCorrelationContext Error)
    (reference : HavingRepetitionRef) : Except Error RowIndex :=
  match reference.source with
  | .repeatable level =>
      (frame.envAt reference.origin).bindingAt level |>.mapError context.bindingError
  | .fixed _ => .ok 1

/-- Validation specialization retained for established filter consumers. -/
def HavingNumberRef.resolveIn (reference : HavingNumberRef)
    (context : CorrelationContext) (frame : CorrelationFrame) :
    CorrelatedNumberOperand :=
  reference.resolveInAt .validation context frame

private def malformedCorrelationCell : CheckedCell :=
  { rawPresent := true, parsed := none, findings := [.malformed] }

def SingleGroupValidationContext.asCorrelationContext
    (context : SingleGroupValidationContext) : CorrelationContext where
  read env field :=
    match env.uniqueRowAt? context.group with
    | some row => context.read row field
    | none => malformedCorrelationCell

/-- Backwards-compatible one-group numeric resolution. -/
def HavingNumberRef.resolve (reference : HavingNumberRef)
    (context : SingleGroupValidationContext) (frame : SingleGroupFilterFrame) :
    CorrelatedNumberOperand :=
  reference.resolveIn context.asCorrelationContext (frame.toCorrelationFrame context)

private def havingArithmetic : NumericOperand → Except Unit NumericArithmeticOutcome
  | .value amount fillability => .ok (.value amount fillability)
  | .unknown _ => .error ()

private def readHavingSubdayDifference (phase : Phase)
    (read : Env → FieldId → Except Error CheckedCell) (frame : CorrelationFrame)
    (world : Option World) (unavailable : Error)
    (unit : DateTimeSubdayUnit) (left right : FlatTemporalOperand HavingTemporalRef) : Except Error NumericOperand := do
  let observe (reference : HavingTemporalRef) := observeCell phase <$> read (frame.envAt reference.origin) reference.field.id
  let first ← left.readDateTimeDifferenceOperand observe world unavailable unavailable
  let second ← right.readDateTimeDifferenceOperand observe world unavailable unavailable
  pure (DateTimeDifferenceOperand.evaluate unit first second)

private def readHavingCalendarDifference (phase : Phase)
    (read : Env → FieldId → Except Error CheckedCell) (frame : CorrelationFrame)
    (readOperand : (HavingTemporalRef → Except Error CellObservation) →
      ResolvedDateDifferenceOperand HavingTemporalRef → Except Error Operand)
    (evaluate : Operand → Operand → Except Unit NumericOperand)
    (left right : ResolvedDateDifferenceOperand HavingTemporalRef) : Except Error (Except Unit NumericOperand) := do
  let observe reference := observeCell phase <$> read (frame.envAt reference.origin) reference.field.id
  let first ← readOperand observe left
  let second ← readOperand observe right
  pure (evaluate first second)

private def readHavingToday (world : Option World) (unavailable : Error)
    (profile : ModelZone.ConcreteProfile) : Except Error DateParts :=
  match ResolvedDateDifferenceOperand.todayParts? profile world with
  | some parts => pure parts
  | none => throw unavailable

private def readHavingClockPart (world : Option World) (unavailable : Error)
    (source : HavingClockSource) (profile : ModelZone.ConcreteProfile) (part : TemporalNumericPart) : Except Error Rat :=
  match source.numericPart? profile world part with
  | some amount => pure amount
  | none => throw unavailable

private def readHavingDateOperand (world : Option World) (unavailable : Error)
    (read : HavingTemporalRef → Except Error CellObservation) :
    ResolvedDateDifferenceOperand HavingTemporalRef → Except Error DateDifferenceOperand :=
  ResolvedDateDifferenceOperand.readDateOperand read
    (fun profile => DateDifferenceOperand.value <$> readHavingToday world unavailable profile)

private def readHavingDayOperand (profile : ModelZone.ConcreteProfile)
    (world : Option World) (unavailable : Error) (read : HavingTemporalRef → Except Error CellObservation) :
    ResolvedDateDifferenceOperand HavingTemporalRef → Except Error CalendarDayDifferenceOperand :=
  ResolvedDateDifferenceOperand.readDayOperand profile read
    (fun sourceProfile => CalendarDayDifferenceOperand.ofParts sourceProfile <$> readHavingToday world unavailable sourceProfile)

def HavingNumericAtom.readValidation (context : CorrelationContext) (frame : CorrelationFrame) :
    HavingNumericAtom → Except Unit NumericArithmeticOutcome
  | .temporalExpressionPart part source =>
      ((source.readNumeric part .validation context.asResolving frame (fun _ => ()) ()).mapError (fun _ => ())).bind id
  | .dateDifference unit left right =>
      (readHavingCalendarDifference .validation (fun env field => .ok (context.read env field)) frame
        (readHavingDateOperand context.world ()) (DateDifferenceOperand.evaluate unit) left right).bind (fun result => result.bind havingArithmetic)
  | .dayDifference profile left right =>
      (readHavingCalendarDifference .validation (fun env field => .ok (context.read env field)) frame
        (readHavingDayOperand profile context.world ()) (CalendarDayDifferenceOperand.evaluate profile) left right).bind (fun result => result.bind havingArithmetic)
  | .aggregate op slots =>
      match HavingNumberAggregate.evaluate .validation context.asResolving frame op slots with
      | .ok operand => havingArithmetic operand
      | .error _ => .error ()
  | .dateTimeDifference unit left right =>
      (readHavingSubdayDifference .validation (fun env field => .ok (context.read env field)) frame
        context.world () unit left right).bind havingArithmetic
  | .dateRangeBoundPart origin source bound part =>
      havingArithmetic ((observeCell .validation (context.read (frame.envAt origin) source.id)).asDateRangeBoundNumericOperand bound part)
  | .baseYear year => .ok (.value year .fixed)
  | .baseYearDatePart year source part => .ok (.value (baseYearDateSourceNumericPart year source part) .fixed)
  | .clockPart source profile part => (.value · .fixed) <$> readHavingClockPart context.world () source profile part
  | .fieldValueAsNumber origin source =>
      havingArithmetic (source.observeOperand (observeCell .validation (context.read (frame.envAt origin) source.fieldId)))
  | .stringLength origin source =>
      havingArithmetic ((observeCell .validation (context.read (frame.envAt origin) source.id)).asStringLengthOperand)
  | .stringRange origin source start finish =>
      havingArithmetic ((observeCell .validation (context.read (frame.envAt origin) source.id)).asStringRangeOperand start finish)
  | .temporalPart origin source part =>
      havingArithmetic ((observeCell .validation (context.read (frame.envAt origin) source.id)).asTemporalNumericOperand source part.project?)
  | .field reference =>
      match reference.resolveIn context frame with
      | .value amount => .ok (.value amount .fixed)
      | .unknown _ => .error ()
  | .repetition reference =>
      match frame.rowAt? reference with
      | some row => .ok (.value row .fixed)
      | none => .error ()

def HavingNumericAtom.readValidationResolving (context : ResolvingCorrelationContext Error)
    (frame : CorrelationFrame) :
    HavingNumericAtom → Except Error (Except Unit NumericArithmeticOutcome)
  | .temporalExpressionPart part source => source.readNumeric part .validation context frame (fun _ => ()) ()
  | .dateDifference unit left right => do
      pure ((← readHavingCalendarDifference .validation context.read frame (readHavingDateOperand context.world context.unsupportedDateCalendar) (DateDifferenceOperand.evaluate unit) left right).bind havingArithmetic)
  | .dayDifference profile left right => do
      pure ((← readHavingCalendarDifference .validation context.read frame (readHavingDayOperand profile context.world context.unsupportedDateCalendar) (CalendarDayDifferenceOperand.evaluate profile) left right).bind havingArithmetic)
  | .aggregate op slots => do
      pure (havingArithmetic (← HavingNumberAggregate.evaluate .validation context frame op slots))
  | .dateTimeDifference unit left right => do
      pure (havingArithmetic (← readHavingSubdayDifference .validation context.read frame context.world context.unsupportedDateCalendar unit left right))
  | .dateRangeBoundPart origin source bound part => do
      let cell ← context.read (frame.envAt origin) source.id
      pure (havingArithmetic ((observeCell .validation cell).asDateRangeBoundNumericOperand bound part))
  | .baseYear year => pure (.ok (.value year .fixed))
  | .baseYearDatePart year source part => pure (.ok (.value (baseYearDateSourceNumericPart year source part) .fixed))
  | .clockPart source profile part => do
      pure (.ok (.value (← readHavingClockPart context.world context.unsupportedDateCalendar source profile part) .fixed))
  | .fieldValueAsNumber origin source => do
      let cell ← context.read (frame.envAt origin) source.fieldId
      pure (havingArithmetic (source.observeOperand (observeCell .validation cell)))
  | .stringLength origin source => do
      let cell ← context.read (frame.envAt origin) source.id
      pure (havingArithmetic ((observeCell .validation cell).asStringLengthOperand))
  | .stringRange origin source start finish => do
      let cell ← context.read (frame.envAt origin) source.id
      pure (havingArithmetic ((observeCell .validation cell).asStringRangeOperand start finish))
  | .temporalPart origin source part => do
      let cell ← context.read (frame.envAt origin) source.id
      pure (havingArithmetic ((observeCell .validation cell).asTemporalNumericOperand source part.project?))
  | .field reference => do
      pure (match ← reference.resolveInAtResolving .validation context frame with
        | .value amount => .ok (.value amount .fixed)
        | .unknown _ => .error ())
  | .repetition reference => do
      pure (.ok (.value (← frame.rowAtResolving context reference) .fixed))

def HavingNumericAtom.readComputationResolving (context : ResolvingCorrelationContext Error)
    (frame : CorrelationFrame) : HavingNumericAtom → Except Error NumericComputationResult
  | .temporalExpressionPart part source => do
      let result ← source.readNumeric part .computation context frame NumericComputationResult.poison .domainFailure
      pure (match result with
        | .error result => result
        | .ok (.value amount _) => .value amount
        | .ok .notEvaluated => .domainFailure)
  | .dateDifference unit left right => do
      let result ← readHavingCalendarDifference .computation context.read frame (readHavingDateOperand context.world context.unsupportedDateCalendar) (DateDifferenceOperand.evaluate unit) left right
      (result.map NumericOperand.toComputationResult).mapError fun _ => context.unsupportedDateCalendar
  | .dayDifference profile left right => do
      let result ← readHavingCalendarDifference .computation context.read frame (readHavingDayOperand profile context.world context.unsupportedDateCalendar) (CalendarDayDifferenceOperand.evaluate profile) left right
      (result.map NumericOperand.toComputationResult).mapError fun _ => context.unsupportedDateCalendar
  | .aggregate op slots => do
      pure ((← HavingNumberAggregate.evaluate .computation context frame op slots).toComputationResult)
  | .dateTimeDifference unit left right => do
      pure ((← readHavingSubdayDifference .computation context.read frame context.world context.unsupportedDateCalendar unit left right).toComputationResult)
  | .dateRangeBoundPart origin source bound part => do
      let cell ← context.read (frame.envAt origin) source.id
      pure (((observeCell .computation cell).asDateRangeBoundNumericOperand bound part).toComputationResult)
  | .baseYear year => pure (.value year)
  | .baseYearDatePart year source part => pure (.value (baseYearDateSourceNumericPart year source part))
  | .clockPart source profile part =>
      .value <$> readHavingClockPart context.world context.unsupportedDateCalendar source profile part
  | .fieldValueAsNumber origin source => do
      let cell ← context.read (frame.envAt origin) source.fieldId
      pure ((source.observeOperand (observeCell .computation cell)).toComputationResult)
  | .stringLength origin source => do
      let cell ← context.read (frame.envAt origin) source.id
      pure ((observeCell .computation cell).asStringLengthOperand.toComputationResult)
  | .stringRange origin source start finish => do
      let cell ← context.read (frame.envAt origin) source.id
      pure (((observeCell .computation cell).asStringRangeOperand start finish).toComputationResult)
  | .temporalPart origin source part => do
      let cell ← context.read (frame.envAt origin) source.id
      pure (((observeCell .computation cell).asTemporalNumericOperand source part.project?).toComputationResult)
  | .field reference => do
      pure (match ← reference.resolveInAtResolving .computation context frame with
        | .value amount => .value amount
        | .unknown cause => .poison cause)
  | .repetition reference => do
      pure (.value (← frame.rowAtResolving context reference))

/-- Pure cell readers retain caller-owned group and clock capabilities; structural faults stay
outside numeric poison, including an unavailable aggregate extent (spec/07 §5). -/
def HavingNumericAtom.readComputationIn (context : CorrelationContext)
    (frame : CorrelationFrame) : HavingNumericAtom → Except CorrelationRuntimeFault NumericComputationResult
  | .repetition reference => pure (match frame.rowAt? reference with
      | some row => .value row
      | none => .domainFailure)
  | atom => atom.readComputationResolving context.asResolving frame

/-- Compatibility projection for scalar clients that observe only success versus support failure. -/
def HavingNumericAtom.readComputation (context : CorrelationContext)
    (frame : CorrelationFrame) (atom : HavingNumericAtom) : Except Unit NumericComputationResult :=
  (atom.readComputationIn context frame).mapError fun _ => ()

end A12Kernel
