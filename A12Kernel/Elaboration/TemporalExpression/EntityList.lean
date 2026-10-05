import A12Kernel.Elaboration.TemporalExpression.Types
import A12Kernel.Semantics.ComputationCondition

namespace A12Kernel

private def liftScalarTemporal (wrap : α → ScalarTemporalValue) :
    SimpleComparisonOperand α → SimpleComparisonOperand ScalarTemporalValue
  | .value value given => .value (wrap value) given
  | .notEvaluated => .notEvaluated
  | .unknown cause => .unknown cause

/-- Preserve each declaration's precision before model Base Year completion (LF163). Both direct
and expanded operands use this projection, so a row-set cannot borrow another field's components. -/
def projectScalarTemporalObservation (model : FlatModel) (field : FlatTemporalField)
    (observation : CellObservation) : SimpleComparisonOperand ScalarTemporalValue :=
  let components := if field.components.hasDate then field.components.withBaseYear model.hasBaseYear else field.components
  if components == TemporalComponents.now then
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
    | _, _ => .unknown .malformed

def readScalarTemporalField (model : FlatModel) (phase : Phase) (field : FlatTemporalField)
    (cell : CheckedCell) : SimpleComparisonOperand ScalarTemporalValue :=
  projectScalarTemporalObservation model field (observeCell phase cell)

namespace CheckedTemporalExtremumOperands

/-- Scheduling includes filter reads even when every candidate is excluded. -/
def fieldIds (source : CheckedTemporalExtremumOperands model) : List FieldId :=
  (source.shape.operands.flatMap (·.expansionDeclarations)).map (·.id) ++
    source.filters.flatMap (fun filter => filter.toList.flatMap (·.fieldIds))

def bindingScopes (source : CheckedTemporalExtremumOperands model) : List (List RepeatableLevel) :=
  source.shape.operands.map (·.bindingScope) ++
    (if source.filters.any Option.isSome then [source.filterBindingScope] else [])

private def addressed (context : ScalarComputationContext) :
    Except ScalarTemporalEvaluationFault ComputationFillContext :=
  match context.addressed with
  | some value => pure value
  | none => throw .calendarUnavailable

private def readField (model : FlatModel) (phase : Phase) (declaration : FlatFieldDecl) (cell : CheckedCell) :
    Except ScalarTemporalEvaluationFault (SimpleComparisonOperand ScalarTemporalValue) := do
  let some field := declaration.toTemporalField? | throw .calendarUnavailable
  pure (readScalarTemporalField model phase field cell)

private def readGroup (phase : Phase) (context : ScalarComputationContext)
    (source : CheckedEntityGroupSource model) (declarations : List FlatFieldDecl) :
    Except ScalarTemporalEvaluationFault (ResolvedTemporalAggregateSide ScalarTemporalValue) := do
  let contextRead ← addressed context
  let tail ← (model.groupOperandUninstantiatedTail contextRead.document context.row
    source.boundLevelCount (declarations.map (·.repeatableScope))).mapError (fun _ => .calendarUnavailable)
  let mut values := []
  for declaration in declarations do
    let rows ← (model.groupOperandEnvironments contextRead.document context.row
      source.boundLevelCount declaration.repeatableScope).mapError (fun _ => .calendarUnavailable)
    for row in rows do
      let value ← readField model phase declaration (contextRead.read row declaration.id)
      values := value :: values
      if phase == .computation then
        if let .unknown _ := value then
          return { operands := values.reverse, hasUninstantiatedTail := tail, hasHaving := false }
  pure { operands := values.reverse, hasUninstantiatedTail := tail, hasHaving := false }

private def readStar (phase : Phase) (context : ScalarComputationContext)
    (source : CheckedStarFieldPath model) (filter : Option CorrelatedHaving) :
    Except ScalarTemporalEvaluationFault (ResolvedTemporalAggregateSide ScalarTemporalValue) := do
  let contextRead ← addressed context
  let resolved ← (source.path.resolveInCapacity contextRead.document context.row).mapError (fun _ => .calendarUnavailable)
  let read := fun row => readField model phase source.declaration (contextRead.read row source.declaration.id)
  let correlation : ResolvingCorrelationContext ScalarTemporalEvaluationFault := {
    read := fun row field => pure (contextRead.read row field)
    unsupportedDateCalendar := .calendarUnavailable
    bindingError := fun _ => .calendarUnavailable }
  let values ← match filter, phase with
    | none, _ => resolved.environments.mapM read
    | some filter, .validation => do
        let rows ← filter.selectEnvironmentsResolving correlation context.row resolved.environments
        rows.mapM read
    | some filter, .computation => do
        let result ← filter.scanComputationResolving correlation context.row
          (fun values row => do
            let value ← read row
            pure (match value with
              | .unknown cause => .inr cause
              | value => .inl (value :: values))) resolved.environments []
        pure (match result with
          | .exhausted values => values.reverse
          | .terminated cause | .poison cause => [.unknown cause])
  pure { operands := values, hasUninstantiatedTail := resolved.domain.hasOpenTail, hasHaving := filter.isSome }

private def readOperand (phase : Phase) (context : ScalarComputationContext)
    (filter : Option CorrelatedHaving) : ResolvedFieldEntityOperand model →
    Except ScalarTemporalEvaluationFault (ResolvedTemporalAggregateSide ScalarTemporalValue)
  | .indexed _ => throw .indexedOperandNotSupported
  | .field declaration _ => do
      pure { operands := [← readField model phase declaration (context.read declaration.id)]
             hasUninstantiatedTail := false, hasHaving := false }
  | .star source => readStar phase context source none
  | .starHaving source _ => do
      let some filter := filter | throw .calendarUnavailable
      readStar phase context source (some filter)
  | .group source => readGroup phase context (.fixed (model := model) source) (model.groupSubtreeFields source.path)
  | .starredGroup source => readGroup phase context (.starred source) (model.groupSubtreeFields source.group.path)
  | .starredGroupPresence source => readGroup phase context (.starredPresence source) (model.groupSubtreeFields source.groupPath)

/-- Computation stops at the first reached poison. Filter lookahead stays owned by the shared
Having scanner; validation keeps its eager candidate selection (spec/05 and spec/09). -/
def evalScalar (source : CheckedTemporalExtremumOperands model) (operator : TemporalExtremumOp)
    (phase : Phase) (context : ScalarComputationContext) :
    Except ScalarTemporalEvaluationFault (SimpleComparisonOperand ScalarTemporalValue) := do
  let mut values := []
  let mut tail := false
  let mut hasHaving := false
  for (operand, filter) in source.shape.operands.zip source.filters do
    let next ← readOperand phase context filter operand
    if phase == .computation then
      for value in next.operands do
        if let .unknown cause := value then return .unknown cause
    values := next.operands.reverse ++ values
    tail := tail || next.hasUninstantiatedTail
    hasHaving := hasHaving || next.hasHaving
  pure (evalTemporalExtremumAggregate (ScalarTemporalValue.select operator)
    { operands := values.reverse, hasUninstantiatedTail := tail, hasHaving })

end CheckedTemporalExtremumOperands
end A12Kernel
