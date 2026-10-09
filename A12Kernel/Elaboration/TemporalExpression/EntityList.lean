import A12Kernel.Elaboration.TemporalExpression.ReadContext
import A12Kernel.Semantics.ComputationCondition

namespace A12Kernel

def projectScalarTemporalObservation (model : FlatModel) (field : FlatTemporalField)
    (observation : CellObservation) : SimpleComparisonOperand ScalarTemporalValue :=
  projectScalarTemporalObservationWith model.baseYear (ModelZone.ConcreteProfile.ofId? model.timeZoneId) field observation

def readScalarTemporalField (model : FlatModel) (phase : Phase) (field : FlatTemporalField)
    (cell : CheckedCell) : SimpleComparisonOperand ScalarTemporalValue :=
  projectScalarTemporalObservation model field (observeCell phase cell)

namespace CheckedTemporalExtremumOperands

/-- Payload and selector reads remain ordinary dependencies regardless of filter group protection. -/
def operandFieldIds (source : CheckedTemporalExtremumOperands model) : List FieldId :=
  source.shape.operands.flatMap (fun operand => match operand with
    | .indexed selected => (model.fields.filter (fun field => selected.referencesField field.id)).map (·.id)
    | .keyed selected => (model.fields.filter (fun field => selected.referencesField field.id)).map (·.id)
    | operand => operand.expansionDeclarations.map (·.id))

/-- Complete references retain filter members even when a dependency query exempts them. -/
def fieldIds (source : CheckedTemporalExtremumOperands model) : List FieldId :=
  source.operandFieldIds ++ source.filters.flatMap (fun filter => filter.toList.flatMap (·.fieldIds))

def referencesWith (source : CheckedTemporalExtremumOperands model) (field : FieldId)
    (filterReads : CorrelatedHaving → Bool) : Bool :=
  source.operandFieldIds.contains field || source.filters.any (·.any filterReads)

def bindingScopes (source : CheckedTemporalExtremumOperands model) : List (List RepeatableLevel) :=
  source.shape.operands.flatMap (·.bindingScopes) ++
    source.filters.flatMap (fun filter => filter.toList.flatMap fun having =>
      (CorrelatedHaving.outerIterationScopes model having).filterMap id)

/-- Index and star selection own their free row levels; another operand's binding must not
turn their payload dependencies into ordinary current-row reads. Dynamic keys still read at the caller’s row (spec/08 §4). -/
def boundFieldIds (source : CheckedTemporalExtremumOperands model) : List FieldId :=
  source.shape.operands.flatMap (fun operand => match operand with
    | .indexed selected => match selected.key with | .field field => [field.id] | .literal .. => []
    | .keyed selected => match selected.selection.key with | .field field => [field.id] | .literal .. => []
    | operand => (operand.expansionDeclarations.filter fun field =>
        field.repeatableScope.isPrefixOf operand.bindingScope).map (·.id)) ++
    (source.filters.flatMap (fun filter => filter.toList.flatMap (·.fieldIds))).filter fun field =>
      (model.fieldRepeatableScope field).isPrefixOf source.filterBindingScope

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
  let fieldRead := if filter.isSome then model.filterRead contextRead.document contextRead.read else contextRead.read
  let candidates ← if filter.isSome then
      (model.filterEnvironments source.path (contextRead.document.filterRows.getD contextRead.document.instantiatedRows) context.row true).mapError
        (ScalarTemporalEvaluationFault.addressing ∘ CheckedAddressingError.addressing)
    else pure resolved.environments
  let read := fun row => readField model phase source.declaration (fieldRead row source.declaration.id)
  let groups := model.correlationGroupsWithRead contextRead.document (fun row field => pure (fieldRead row field))
  let correlation : ResolvingCorrelationContext ScalarTemporalEvaluationFault := {
    read := fun row field => pure (fieldRead row field)
    storedText := contextRead.storedText
    numberText := contextRead.numberText
    world := context.world
    stringExpressionUnavailable := .addressing (.addressing .stringExpressionUnavailable)
    unsupportedDateCalendar := .calendarUnavailable
    temporalValueFailure := .dateTimeLabelUnresolved
    worldUnavailable := .addressing .worldUnavailable
    typeValidityValueFailure := .addressing .typeValidityValueFailure
    storedTextUnavailable := fun field => .addressing (.addressing (.storedTextUnavailable field))
    groupUnavailable := ScalarTemporalEvaluationFault.addressing ∘ CheckedAddressingError.checkedDocumentRequired
    groups := some {
      groupExtent? := groups.groupExtent?.map fun extent path row selection =>
        (extent path row selection).mapError .addressing
      fieldExtent path row depth field := (groups.fieldExtent path row depth field).mapError .addressing
      validation row reference := (groups.validation row reference).mapError .addressing
      computation row source := (groups.computation row source).mapError .addressing }
    bindingError := fun _ => .calendarUnavailable }
  let values ← match filter, phase with
    | none, _ => resolved.environments.mapM read
    | some filter, .validation => do
        let rows ← filter.selectEnvironmentsResolving correlation context.row candidates
        rows.mapM read
    | some filter, .computation => do
        let result ← filter.scanComputationResolving correlation context.row
          (fun values row => do
            let value ← read row
            pure (match value with
              | .unknown cause => .inr cause
              | value => .inl (value :: values))) candidates []
        pure (match result with
          | .exhausted values => values.reverse
          | .terminated cause | .poison cause => [.unknown cause])
  pure { operands := values, hasUninstantiatedTail := resolved.domain.hasOpenTail, hasHaving := filter.isSome }

private def readOperand (phase : Phase) (context : ScalarComputationContext)
    (filter : Option CorrelatedHaving) : ResolvedFieldEntityOperand model →
    Except ScalarTemporalEvaluationFault (ResolvedTemporalAggregateSide ScalarTemporalValue)
  | source@(.indexed _) | source@(.keyed _) =>
      (TemporalExtremumStream.selectedSide source phase context (fun declaration observation => do
        let some field := declaration.toTemporalField? | throw (.addressing (.unsupportedGroupOperand declaration.groupPath))
        pure (projectScalarTemporalObservation model field observation))).mapError (fun _ => .calendarUnavailable)
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

private def readPartialOperand (partialRead : TemporalPartialReadContext model) (outer : Env) :
    ResolvedFieldEntityOperand model → Except ScalarTemporalEvaluationFault
      (ResolvedTemporalAggregateSide ScalarTemporalValue) := fun operand => do
  let document := partialRead.document
  let scope := partialRead.effectiveScope
  let ordinary := fun (declarations : List FlatFieldDecl) (bound : Nat) => do
    if !declarations.all (fun declaration => scope.coversAggregateExtent model declaration.path
        (declaration.repeatableScope.take bound) (declaration.repeatableScope.drop bound) outer) then
      return none
    let (addresses, tail) ← model.groupOperandReads document.source.toDocument outer bound declarations
      (·.repeatableScope) |>.mapError (ScalarTemporalEvaluationFault.addressing ∘ CheckedAddressingError.addressing)
    pure (some (.value (addresses, tail)) : Option (CellObservation (List (FlatFieldDecl × Env) × Bool)))
  let extent ← match operand with
    | .indexed source => (resolvePartialSelectedAddresses (.inl source) document scope outer partialRead.read
        (fun declaration bound reopened row => scope.coversAggregateExtent model declaration.path bound reopened row)).mapError .addressing
    | .keyed source => (resolvePartialSelectedAddresses (.inr source) document scope outer partialRead.read
        (fun declaration bound reopened row => scope.coversAggregateExtent model declaration.path bound reopened row)).mapError .addressing
    | .field declaration _ => ordinary [declaration] declaration.repeatableScope.length
    | .star source => ordinary [source.declaration] source.path.firstStar
    | .group source => ordinary (model.groupSubtreeFields source.path) (CheckedEntityGroupSource.fixed (model := model) source).boundLevelCount
    | .starredGroup source => ordinary (model.groupSubtreeFields source.group.path) (CheckedEntityGroupSource.starred source).boundLevelCount
    | .starredGroupPresence source => ordinary (model.groupSubtreeFields source.groupPath) (CheckedEntityGroupSource.starredPresence source).boundLevelCount
    | .starHaving _ _ => throw .indexedOperandNotSupported
  match extent with
  | none => pure { operands := [.value .nonRelevant true], hasUninstantiatedTail := false, hasHaving := false }
  | some .empty => pure { operands := [.notEvaluated], hasUninstantiatedTail := false, hasHaving := false }
  | some (.unknown cause) | some (.poison cause) =>
      pure { operands := [.unknown cause], hasUninstantiatedTail := false, hasHaving := false }
  | some (.value (addresses, tail)) =>
      let operands ← addresses.mapM fun (declaration, row) => do
        match ← partialRead.readCell row declaration.id with
        | none => pure (.value .nonRelevant true)
        | some cell => readField model .validation declaration cell
      -- A missing scalar still occupies an authored slot; an empty selected lower-star does not
      -- (partial-temporal fallback grid, 2026-10-07; spec/05 temporal extrema).
      let operands := match operand with
        | .indexed _ => if addresses.isEmpty then [.notEvaluated] else operands
        | _ => operands
      pure { operands, hasUninstantiatedTail := tail, hasHaving := false }

/-- Computation stops at the first reached poison. Filter lookahead stays owned by the shared
Having scanner; validation keeps its eager candidate selection (spec/05 and spec/09). -/
def evalScalar (source : CheckedTemporalExtremumOperands model) (operator : TemporalExtremumOp)
    (phase : Phase) (context : ScalarComputationContext)
    (partialRead? : Option (TemporalPartialReadContext model) := none) :
    Except ScalarTemporalEvaluationFault (SimpleComparisonOperand ScalarTemporalValue) := do
  let mut values := []
  let mut tail := false
  let mut hasHaving := false
  for (operand, filter) in source.shape.operands.zip source.filters do
    let next ← match partialRead? with
      | none => readOperand phase context filter operand
      | some partialRead => readPartialOperand partialRead context.row operand
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
