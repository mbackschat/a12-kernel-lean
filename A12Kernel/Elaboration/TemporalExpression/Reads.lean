import A12Kernel.Elaboration.TemporalExpression.EntityList
import A12Kernel.Elaboration.TemporalExpression.DateComponents

namespace A12Kernel

def liftScalarTemporal (wrap : α → ScalarTemporalValue) :
    SimpleComparisonOperand α → SimpleComparisonOperand ScalarTemporalValue
  | .value value given => .value (wrap value) given
  | .notEvaluated => .notEvaluated
  | .unknown cause => .unknown cause

def readScalarTemporalAmount (context : FlatContext) (phase : Phase) :
    CheckedTemporalShiftAmount model → Except NumericValidationUnavailable NumericArithmeticOutcome
  | .literal value => .ok (.value value .fixed)
  | .field source _ =>
      (context.resolveNumberComparisonOperandAt phase source).toValidationArithmetic
  | .expression checked _ => checked.evalWith fun
      | .field source => (context.resolveNumberComparisonOperandAt phase source).toValidationArithmetic
      | _ => .error .groupState

/-- Direct amount reads keep partial unavailability outside the cell's formal findings;
`FirstFilledValue` can therefore hide an unread suffix (spec/05 selection and spec/10 relevance). -/
def scalarAmountReadContext (context : ScalarComputationContext)
    (partialRead? : Option (TemporalPartialReadContext model)) :
    ResolvingCorrelationContext (Option ScalarTemporalEvaluationFault) := {
  read := fun _ field => match partialRead? with
    | none => pure (context.read field)
    | some partialRead => do
        match ← (partialRead.readCell context.row field).mapError some with
        | some cell => pure cell
        | none => throw none
  storedText := fun _ => context.storedText
  numberText := fun _ => context.numberText
  world := context.world
  bindingError := fun error => some (.addressing (.environment error))
  stringExpressionUnavailable := some (.addressing (.addressing .stringExpressionUnavailable))
  unsupportedDateCalendar := some .calendarUnavailable
  temporalValueFailure := some .dateTimeLabelUnresolved
  worldUnavailable := some (.addressing .worldUnavailable)
  typeValidityValueFailure := some (.addressing .typeValidityValueFailure)
  groupUnavailable := fun path => some (.addressing (.checkedDocumentRequired path))
  storedTextUnavailable := fun field => some (.addressing (.addressing (.storedTextUnavailable field))) }

def resolvedScalarDate (profile : ModelZone.ConcreteProfile) (date : FullDate) :
    Option DateValue := do
  let instant ← profile.resolveLocal? {
    date, time := { hour := 0, minute := 0, second := 0, valid := by decide } }
  pure { instant, parts := date.civil.parts, basis := .storedGregorian }

def readScalarValueAsDate (phase : Phase) (source : CheckedZonedValueAsDateSource model)
    (cell : CheckedCell) (stored : Option String) :
    Except ScalarTemporalEvaluationFault (SimpleComparisonOperand ScalarTemporalValue) := do
  let checked := source.toCheckedValueAsDateSource.checkSourceText {
    rawPresent := cell.rawPresent, parsed := stored, findings := cell.findings }
  match source.toCheckedValueAsDateSource.observe phase checked with
  | .empty => pure .notEvaluated
  | .unavailable cause => pure (.unknown cause)
  | .nonRelevant => pure (.value .nonRelevant true)
  | .date date =>
      let some value := resolvedScalarDate source.profile date | throw .calendarUnavailable
      pure (.value (.date value) true)

def readScalarTimeComponent (context : FlatContext) (phase : Phase)
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

def readScalarTimeLeaf (phase : Phase) (context : ScalarComputationContext)
    (component : Sum (CheckedTimeComponent model) (CheckedIndexedTimeComponent model)) :
    Except ScalarTemporalEvaluationFault TimeConstructionComponent := do
  let classify (source : CheckedTimeComponent model) (fields : FlatContext) :=
    match readScalarTimeComponent fields phase source with
    | .ok value => pure value
    | .error (.stringNotConvertible _ _) => throw ScalarTemporalEvaluationFault.componentNumberInvalid
    | .error _ => pure (.unavailable .malformed)
  match component with
  | .inl source => classify source { read := context.read, storedText := context.storedText, world := context.world }
  | .inr source =>
      let some addressed := context.addressed | throw .calendarUnavailable
      match ← (source.selection.selectEnvironmentWith phase context.semanticIndexColumnReader
          context.row context.read context.storedText).mapError (fun _ => .calendarUnavailable) with
      | .empty => pure .empty
      | .unknown cause | .poison cause => pure (.unavailable cause)
      | .value row => classify source.source {
          read := addressed.read row, storedText := addressed.storedText row, world := context.world }

def readScalarRangeBound (phase : Phase) (profile : ModelZone.ConcreteProfile)
    (source : CheckedDateRangeBoundOperand model) (readCell : FieldId → CheckedCell) :
    Except ScalarTemporalEvaluationFault (SimpleComparisonOperand ScalarTemporalValue) := do
  let (field, bound, yearless) := match source with
    | .exact source => (source.source.id, source.bound, false)
    | .yearless source => (source.source.id, source.bound, true)
  (projectScalarRangeBoundObservation profile yearless bound (observeCell phase (readCell field))).mapError
    ScalarTemporalPrimitiveFault.toEvaluation

def readPartialScalarTemporalAmount (partialRead : TemporalPartialReadContext model) (row : Env)
    (amount : CheckedTemporalShiftAmount model) : Except ScalarTemporalEvaluationFault
      (Except NumericValidationUnavailable NumericArithmeticOutcome) := do
  let readNumber := fun source => do
    match ← partialRead.readCell row source.id with
    | none => pure (.error .nonRelevant)
    | some cell => pure (({ read := fun _ => cell } : FlatContext).resolveNumberComparisonOperand source).toValidationArithmetic
  match amount with
  | .literal value => pure (.ok (.value value .fixed))
  | .field source _ => readNumber source
  | .expression checked _ =>
      let resolved ← checked.core.mapM fun
        | .field source => readNumber source
        | _ => pure (.error .groupState)
      pure (resolved.lowerForEvaluation.evalNumericOperationTree id)

def readPartialScalarTimeComponent (context : ScalarComputationContext)
    (partialRead : TemporalPartialReadContext model) (source : CheckedTimeComponent model) :
    Except ScalarTemporalEvaluationFault TimeConstructionComponent := do
  match source with
  | .constant value => pure (.value value)
  | .shiftedExtractor checked =>
      let shifted := checked.source
      let cell? ← partialRead.readCell context.row shifted.source.id
      let observation? := cell?.map (observeCell .validation)
      match observation? with
      | some (.unknown cause) | some (.poison cause) => return .unavailable cause
      | some (.value (.temporal (.dateTime ..))) | some .empty | none => pure ()
      | _ => return .unavailable .malformed
      let amount ← readPartialScalarTemporalAmount partialRead context.row shifted.amount
      match amount with
      | .error (.formal cause) => return .unavailable cause
      | .error .nonRelevant => return .nonRelevant
      | _ => pure ()
      let some observation := observation? | return .nonRelevant
      match ValueAsDateTimeResult.evaluateShiftedDateTimeObservation shifted.profile shifted.unit shifted.source.id
          observation (fun _ => pure amount) TimeComponentsFault.shifted with
      | .ok result => pure (result.asTimeOperand.extractComponent checked.part)
      | .error _ => pure (.unavailable .malformed)
  | _ =>
      let some field := source.fieldDependencies.head? | throw .calendarUnavailable
      let some cell ← partialRead.readCell context.row field | return .nonRelevant
      match readScalarTimeComponent { read := fun _ => cell } .validation source with
      | .ok value => pure value
      | .error (.stringNotConvertible _ _) => throw .componentNumberInvalid
      | .error _ => pure (.unavailable .malformed)

def readPartialScalarTimeLeaf (context : ScalarComputationContext)
    (partialRead : TemporalPartialReadContext model)
    (component : Sum (CheckedTimeComponent model) (CheckedIndexedTimeComponent model)) :
    Except ScalarTemporalEvaluationFault TimeConstructionComponent := do
  match component with
  | .inl source => readPartialScalarTimeComponent context partialRead source
  | .inr source =>
      match ← partialRead.selectedCell source.selection context.row with
      | none => pure .nonRelevant
      | some .empty => pure .empty
      | some (.unknown cause) | some (.poison cause) => pure (.unavailable cause)
      | some (.value (cell, _)) =>
          match readScalarTimeComponent { read := fun _ => cell } .validation source.source with
          | .ok value => pure value
          | .error (.stringNotConvertible _ _) => throw .componentNumberInvalid
          | .error _ => pure (.unavailable .malformed)

/-- Only reads differ in partial evaluation; recursive applications still use the shared tree
and retain non-relevance independently of empty payload (spec/10 §5). -/
def readPartialScalarTemporalAtom (context : ScalarComputationContext)
    (partialRead : TemporalPartialReadContext model) : ScalarTemporalAtom model →
      Option (Except ScalarTemporalEvaluationFault (SimpleComparisonOperand ScalarTemporalValue))
  | .field field => some do
      let some cell ← partialRead.readCell context.row field.id | return .value .nonRelevant true
      pure (readScalarTemporalField model .validation field cell)
  | .indexed source => some do
      let some field := source.targetDeclaration.toTemporalField? | throw .calendarUnavailable
      let observation ← source.observePartialDocument partialRead.document partialRead.scope context.row partialRead.read
        |>.mapError .addressing
      pure (observation.map (projectScalarTemporalObservation model field) |>.getD (.value .nonRelevant true))
  | .valueAsDate source => some do
      let field := source.source.target.id
      let some cell ← partialRead.readCell context.row field | return .value .nonRelevant true
      readScalarValueAsDate .validation source cell (← partialRead.storedText context.row field cell)
  | .indexedValueAsDate source => some do
      match ← partialRead.selectedCell source.selection context.row with
      | none => pure (.value .nonRelevant true)
      | some .empty => pure .notEvaluated
      | some (.unknown cause) | some (.poison cause) => pure (.unknown cause)
      | some (.value (cell, stored)) => readScalarValueAsDate .validation source.source cell stored
  | .rangeBound profile source => some do
      let field := match source with | .exact source => source.source.id | .yearless source => source.source.id
      let some cell ← partialRead.readCell context.row field | return .value .nonRelevant true
      readScalarRangeBound .validation profile source (fun _ => cell)
  | .entityExtremum operator source => some (source.evalScalar operator .validation context (some partialRead))
  | _ => none

end A12Kernel
