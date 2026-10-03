import A12Kernel.Semantics.TemporalExpression
import A12Kernel.Elaboration.TemporalExtremumStream
import A12Kernel.Elaboration.Flat.FieldValueRead
import A12Kernel.Elaboration.ValueAsDateTimeWorldComponents

/-! # Checked scalar temporal expressions

Fields, clock values and typed literals share an expression tree with extrema, complete-DateTime
projections and elapsed shifts. Evaluation retains the date/yearless/time/instant domains and
classified missingness. Calendar shifts and constructed legacy-calendar Dates need their retained
instant and calendar basis and do not enter this scalar projection boundary (spec/05 §2).
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
  | timeConstruction (components : SurfaceTimeComponents)
  | dateFromDateTime (source : SurfaceScalarTemporalExpression)
  | timeFromDateTime (source : SurfaceScalarTemporalExpression)
  | subdayShift (unit : DateTimeSubdayUnit) (source : SurfaceScalarTemporalExpression)
      (amount : AuthoredNumericExpr SurfaceNumericAtom)

/-- Temporal source slots exclude the grouped comparison and extrema productions; each nested
operation checks its own slot (spec/12 §3, grammar `datumAngabe`/`datumAngabe2`). -/
def SurfaceScalarTemporalExpression.admittedSourceSlot : SurfaceScalarTemporalExpression → Bool
  | .group _ | .extremum _ _ | .combine _ _ _ => false
  | .field _ | .now | .today | .dateLiteral _ | .timeLiteral _ | .dateTimeLiteral _
  | .timeConstruction _ | .dateFromDateTime _ | .timeFromDateTime _ | .subdayShift _ _ _ => true

inductive ScalarTemporalExpressionError where
  | model (error : ResolveError)
  | read (error : ResolveError)
  | extremum (error : TemporalExtremumOperandElabError)
  | amount (error : TemporalShiftAmountElabError)
  | timeComponents (error : TimeComponentsElabError)
  | nonTemporal (path : List String)
  | unsupportedSource
  | incompatibleFormats
  deriving Repr

inductive ScalarTemporalValue where
  | date (value : FullDate)
  | yearless (value : MonthDayValue)
  | time (value : TimeOfDay)
  | instant (value : Instant)
  deriving Repr, DecidableEq

namespace ScalarTemporalValue

def select (operator : TemporalExtremumOp) : ScalarTemporalValue → ScalarTemporalValue → ScalarTemporalValue
  | .date left, .date right => .date (operator.select left right)
  | .yearless left, .yearless right => .yearless (operator.selectMonthDay left right)
  | .time left, .time right => .time (operator.selectTime left right)
  | .instant left, .instant right => .instant (operator.selectInstant left right)
  | left, _ => left

def holds (operator : TemporalComparisonOp) : ScalarTemporalValue → ScalarTemporalValue → Bool
  | .date left, .date right => operator.holds left right
  | .yearless left, .yearless right => operator.holdsMonthDay left right
  | .time left, .time right => operator.holdsTime left right
  | .instant left, .instant right => operator.holdsInstant left right
  | _, _ => false

end ScalarTemporalValue

inductive ScalarTemporalAtom (model : FlatModel) where
  | field (source : FlatTemporalField)
  | fixed (value : ScalarTemporalValue)
  | now
  | today (profile : ModelZone.ConcreteProfile)
  | dateTimeLiteral (profile : ModelZone.ConcreteProfile) (value : LocalDateTime)
  | timeConstruction (components : CheckedTimeComponents model)

inductive ScalarTemporalEvaluationFault where
  | dateTimeLabelUnresolved
  deriving Repr, DecidableEq

inductive ScalarTemporalTransform (model : FlatModel) where
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
  modelWellFormed : model.validate.isOk = true

private def scalarProfile (model : FlatModel) :
    Except ScalarTemporalExpressionError ModelZone.ConcreteProfile :=
  match ModelZone.ConcreteProfile.ofId? model.timeZoneId with
  | some profile => pure profile
  | none => throw .unsupportedSource

private def resolveScalarTemporalExpression (model : FlatModel) (rowGroup : GroupPath) :
    SurfaceScalarTemporalExpression → Except ScalarTemporalExpressionError
      (ScalarTemporalExpression model × TemporalComponents)
  | .field reference => do
      let declaration ← (model.resolveFieldValueRead rowGroup reference).mapError .read
      let some field := declaration.toTemporalField? | throw (.nonTemporal declaration.path)
      if declaration.toTemporalTargetPolicy?.any (·.partialMode != .full) then
        throw .unsupportedSource
      pure (.atom (.field field), field.components.withBaseYear model.hasBaseYear)
  | .group source => resolveScalarTemporalExpression model rowGroup source
  | .extremum operator operands => do
      let source ← (TemporalExtremumOperands.elaborate model rowGroup operands).mapError .extremum
      let fields ← source.shape.operands.mapM fun
        | .field declaration _ => do
            if !declaration.repeatableScope.isEmpty then throw .unsupportedSource
            let some field := declaration.toTemporalField? | throw (.nonTemporal declaration.path)
            pure (TemporalExpressionOf.atom (.field field))
        | _ => throw .unsupportedSource
      let first :: rest := fields | throw .unsupportedSource
      pure (.extremum operator first rest, source.components)
  | .combine operator left right => do
      let (left, leftComponents) ← resolveScalarTemporalExpression model rowGroup left
      let (right, rightComponents) ← resolveScalarTemporalExpression model rowGroup right
      if leftComponents != rightComponents then throw .incompatibleFormats
      pure (.extremum operator left [right], leftComponents)
  | .now => pure (.atom .now, TemporalComponents.now)
  | .today => do pure (.atom (.today (← scalarProfile model)), TemporalComponents.fullDate)
  | .dateLiteral value => pure (.atom (.fixed (.date value)), TemporalComponents.fullDate)
  | .timeLiteral value => pure (.atom (.fixed (.time value)), TemporalComponents.time)
  | .dateTimeLiteral value => do
      let profile ← scalarProfile model
      pure (.atom (.dateTimeLiteral profile value), TemporalComponents.now)
  | .timeConstruction source => do
      let components ← (elaborateTimeComponents model source).mapError .timeComponents
      pure (.atom (.timeConstruction components), TemporalComponents.time)
  | .dateFromDateTime source => do
      if !source.admittedSourceSlot then throw .unsupportedSource
      let (source, components) ← resolveScalarTemporalExpression model rowGroup source
      if !components.isFullDateTime then throw .incompatibleFormats
      pure (.transform (.dateFromDateTime (← scalarProfile model)) source, TemporalComponents.fullDate)
  | .timeFromDateTime source => do
      if !source.admittedSourceSlot then throw .unsupportedSource
      let (source, components) ← resolveScalarTemporalExpression model rowGroup source
      if !components.isFullDateTime then throw .incompatibleFormats
      pure (.transform (.timeFromDateTime (← scalarProfile model)) source, TemporalComponents.time)
  | .subdayShift unit source amount => do
      if !source.admittedSourceSlot then throw .unsupportedSource
      let (source, components) ← resolveScalarTemporalExpression model rowGroup source
      if !unit.admittedBy components || !components.isFullDateTime then throw .incompatibleFormats
      let profile ← scalarProfile model
      let amount ← (elaborateTemporalExpressionShiftAmount model rowGroup amount).mapError .amount
      pure (.transform (.subdayShift profile unit amount) source, components)

def elaborateScalarTemporalExpression (model : FlatModel) (rowGroup : GroupPath)
    (surface : SurfaceScalarTemporalExpression) :
    Except ScalarTemporalExpressionError (CheckedScalarTemporalExpression model) := do
  match h : model.validate with
  | .error error => throw (.model error)
  | .ok () =>
      let (core, components) ← resolveScalarTemporalExpression model rowGroup surface
      pure { core, components, modelWellFormed := by rw [h]; rfl }

private def temporalConstant : SurfaceScalarTemporalExpression → Bool
  | .now | .today | .dateLiteral _ | .timeLiteral _ | .dateTimeLiteral _ => true
  | .group source => temporalConstant source
  | _ => false

private def ungroupedClock : SurfaceScalarTemporalExpression → Bool
  | .now | .today => true
  | _ => false

/-- Mixed date/instant ordering retains its separate direct comparison boundary. -/
def elaborateScalarTemporalComparison (model : FlatModel) (rowGroup : GroupPath)
    (operator : TemporalComparisonOp) (left right : SurfaceScalarTemporalExpression) :
    Except ScalarTemporalExpressionError (CheckedScalarTemporalComparison model) := do
  if temporalConstant left && temporalConstant right &&
      ungroupedClock left == ungroupedClock right then throw .unsupportedSource
  let left ← elaborateScalarTemporalExpression model rowGroup left
  let right ← elaborateScalarTemporalExpression model rowGroup right
  if !operator.admitsFormats model.hasBaseYear left.components right.components then
    throw .incompatibleFormats
  if left.components.hasTime != right.components.hasTime then throw .unsupportedSource
  if left.components.hasTime then
    if !(left.components == TemporalComponents.now && right.components == TemporalComponents.now) &&
        !(left.components == TemporalComponents.time && right.components == TemporalComponents.time) then
      throw .unsupportedSource
  pure { left, right, operator, modelWellFormed := left.modelWellFormed }

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

private def readScalarTemporalAtom (model : FlatModel) (phase : Phase) (context : FlatContext)
    (atom : ScalarTemporalAtom model) :
    Except ScalarTemporalEvaluationFault (SimpleComparisonOperand ScalarTemporalValue) := do
  match atom with
  | .dateTimeLiteral profile value =>
      match profile.resolveLocal? value with
      | some instant => pure (.value (.instant instant) true)
      | none => throw .dateTimeLabelUnresolved
  | .fixed value => pure (.value value true)
  | .now => pure (match context.world with
      | some world => .value (.instant world.now) true
      | none => .unknown .malformed)
  | .today profile => pure (match context.world.bind (fun world => profile.localDate? world.now) with
      | some date => .value (.date date) true
      | none => .unknown .malformed)
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
      | .ok _ => .notEvaluated
      | .error _ => .unknown .malformed)
  | .field field =>
      let observation := observeCell phase (context.read field.id)
      let components := field.components.withBaseYear model.hasBaseYear
      pure (if components == TemporalComponents.now then
        liftScalarTemporal .instant observation.asDateTimeExtremumOperand
      else if components == TemporalComponents.time then
        liftScalarTemporal .time observation.asTimeExtremumOperand
      else if components.year then
        liftScalarTemporal .date
          (observation.asMaskedDateExtremumOperand field.components model.baseYear)
      else liftScalarTemporal .yearless (observation.asYearlessDateExtremumOperand field.components))

private def applyScalarTemporalTransform (phase : Phase) (context : FlatContext)
    (operation : ScalarTemporalTransform model)
    (source : SimpleComparisonOperand ScalarTemporalValue) :
    SimpleComparisonOperand ScalarTemporalValue :=
  match source with
  | .unknown cause => .unknown cause
  | source => match operation with
      | .dateFromDateTime profile => match source with
          | .value (.instant instant) given => match profile.localDate? instant with
              | some date => .value (.date date) given
              | none => .unknown .malformed
          | .notEvaluated => .notEvaluated
          | _ => .unknown .malformed
      | .timeFromDateTime profile => match source with
          | .value (.instant instant) given => match profile.localDateTime? instant with
              | some value => .value (.time value.time) given
              | none => .unknown .malformed
          | .notEvaluated => .notEvaluated
          | _ => .unknown .malformed
      | .subdayShift profile unit amount =>
          let reached : Option ValueAsDateTimeResult := match source with
            | .notEvaluated => some (.noValue true)
            | .value (.instant instant) given =>
                (profile.localDateTime? instant).map fun localDateTime => .value localDateTime instant (!given)
            | _ => none
          match reached with
          | none => .unknown .malformed
          | some reached => match readScalarTemporalAmount context phase amount with
              | .error (.formal cause) => .unknown cause
              | .error _ => .unknown .malformed
              | .ok amount => match reached.applyShiftedAmount profile unit amount with
                  | .ok (.value _ instant notGiven) => .value (.instant instant) (!notGiven)
                  | .ok (.unavailable cause) => .unknown cause
                  | .ok _ => .notEvaluated
                  | .error _ => .unknown .malformed

namespace CheckedScalarTemporalExpression

def fieldIds (expression : CheckedScalarTemporalExpression model) : List FieldId :=
  expression.core.dependencies
    (fun | .field source => [source.id]
         | .timeConstruction components => components.toWorld.fieldDependencies
         | _ => [])
    (fun | .subdayShift _ _ amount => amount.fieldDependencies | _ => [])

def referencesField (expression : CheckedScalarTemporalExpression model) (field : FieldId) : Bool :=
  expression.fieldIds.contains field

/-- Model-zone literal resolution belongs to execution, retaining value failure separately from
missingness and operand poison (the DateTime constant zone-split checkpoint, spec/09). -/
def evalResult (expression : CheckedScalarTemporalExpression model) (phase : Phase) (context : FlatContext) :
    Except ScalarTemporalEvaluationFault (SimpleComparisonOperand ScalarTemporalValue) :=
  expression.core.evalWithResult ScalarTemporalValue.select
    (readScalarTemporalAtom model phase context)
    (fun operation source => pure (applyScalarTemporalTransform phase context operation source))

/-- The comparison projection suppresses runtime value failures; computations retain `evalResult`. -/
def eval (expression : CheckedScalarTemporalExpression model) (phase : Phase) (context : FlatContext) :
    SimpleComparisonOperand ScalarTemporalValue :=
  match expression.evalResult phase context with
  | .ok result => result
  | .error _ => .unknown .malformed

end CheckedScalarTemporalExpression

namespace CheckedScalarTemporalComparison

def fieldIds (comparison : CheckedScalarTemporalComparison model) : List FieldId :=
  comparison.left.fieldIds ++ comparison.right.fieldIds

def referencesField (comparison : CheckedScalarTemporalComparison model) (field : FieldId) : Bool :=
  comparison.fieldIds.contains field

def evalAt (comparison : CheckedScalarTemporalComparison model) (phase : Phase)
    (context : FlatContext) : Verdict :=
  evalSymmetricComparison (ScalarTemporalValue.holds comparison.operator)
    (comparison.left.eval phase context) (comparison.right.eval phase context)

def eval (comparison : CheckedScalarTemporalComparison model) (context : FlatContext) : Verdict :=
  comparison.evalAt .validation context

end CheckedScalarTemporalComparison

end A12Kernel
