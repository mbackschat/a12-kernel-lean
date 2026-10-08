import A12Kernel.Semantics.HavingTemporalTypes
import A12Kernel.Semantics.ScalarTemporalDifference

namespace A12Kernel

inductive HavingTemporalReadSource where
  | presence (field : FieldId)
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
  | .presence field => field
  | .temporal field => field.id
  | .range field _ => field.id
  | .number field => field.id
  | .string field => field.id

private def readTimeComponent (origin : HavingOrigin) (source : ResolvedTimeConstructionSource) (profile : ModelZone.ConcreteProfile)
    (phase : Phase) (context : ResolvingCorrelationContext Error) (frame : CorrelationFrame) :
    Except Error TimeConstructionComponent := do
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
        pure (.value (part.extract label.time).num)



namespace HavingTemporalExpression

mutual
private def coreReferenceSlots : HavingTemporalCore → List (HavingFieldListSlot HavingTemporalExpressionRef)
  | .atom atom => atomReferenceSlots atom
  | .apply _ first rest => coreReferenceSlots first ++ rest.flatMap coreReferenceSlots
private def atomReferenceSlots : HavingTemporalAtom → List (HavingFieldListSlot HavingTemporalExpressionRef)
  | .selection _ slots => slots.map (·.map fun reference => { origin := reference.origin, source := .temporal reference.field })
  | .shift _ source amount => coreReferenceSlots source ++ amountReferenceSlots amount
  | .partialDate source => [.direct { origin := source.reference.origin, source := .temporal source.reference.field }]
  | .field reference => [.direct { origin := reference.origin, source := .temporal reference.field }]
  | .rangeBound origin field components _ => [.direct { origin, source := .range field components }]
  | .dateConstruction components => dateReferenceSlots components
  | .timeConstruction components => timeReferenceSlots components
  | _ => []
private def amountReferenceSlots (amount : HavingTemporalAmount) : List (HavingFieldListSlot HavingTemporalExpressionRef) :=
  amount.flatMapAtomsSubterm fun atom _ => match atom with
    | .temporalExpressionPart _ source => coreReferenceSlots source
    | .temporalDifference _ left right => coreReferenceSlots left ++ coreReferenceSlots right
    | atom => (atom.presenceSlotsWith (fun _ _ => [])).map
        (·.map fun reference => { origin := reference.origin, source := .presence reference.field })
decreasing_by all_goals first | decreasing_tactic | omega | (simp_all +arith; omega)
private def dateComponentReferenceSlots : HavingDateComponent → List (HavingFieldListSlot HavingTemporalExpressionRef)
  | .expression _ source => coreReferenceSlots source
  | .direct origin component => (show Option HavingTemporalExpressionRef from match component with
      | .numberField field => some { origin, source := .number field }
      | .stringField field => some { origin, source := .string field }
      | .dateYearField field | .extractor field _ _ => some { origin, source := .temporal field }
      | _ => none).toList.map HavingFieldListSlot.direct
private def timeComponentReferenceSlots : HavingTimeComponent → List (HavingFieldListSlot HavingTemporalExpressionRef)
  | .expression _ source => coreReferenceSlots source
  | .direct origin component => (show Option HavingTemporalExpressionRef from match component with
      | .number field => some { origin, source := .number field }
      | .string field => some { origin, source := .string field }
      | .extractor field _ => some { origin, source := .temporal field }
      | _ => none).toList.map HavingFieldListSlot.direct
private def dateReferenceSlots : HavingDateComponents → List (HavingFieldListSlot HavingTemporalExpressionRef)
  | ⟨day, month, year, _⟩ => dateComponentReferenceSlots day ++ dateComponentReferenceSlots month ++ match year with
      | .complete year => dateComponentReferenceSlots year
      | .baseYear _ => []
      | .centuryAndShortYear century shortYear => dateComponentReferenceSlots century ++ dateComponentReferenceSlots shortYear
private def timeReferenceSlots : HavingTimeComponents → List (HavingFieldListSlot HavingTemporalExpressionRef)
  | .empty => []
  | .hour hour => timeComponentReferenceSlots hour
  | .minute hour minute => timeComponentReferenceSlots hour ++ timeComponentReferenceSlots minute
  | .second hour minute second => timeComponentReferenceSlots hour ++ timeComponentReferenceSlots minute ++ timeComponentReferenceSlots second
end

def referenceSlots (source : HavingTemporalExpression) : List (HavingFieldListSlot HavingTemporalExpressionRef) :=
  coreReferenceSlots source.core

def references (source : HavingTemporalExpression) : List HavingTemporalExpressionRef :=
  source.referenceSlots.flatMap (·.references)

def presenceSlots (source : HavingTemporalExpression) : List (HavingFieldListSlot HavingPresenceRef) :=
  source.referenceSlots.map (·.map fun reference => { origin := reference.origin, field := reference.fieldId })

/-- Group reads retain an origin even when their declared field expansion is empty (spec/07 §5). -/
def groupCountOperands (source : HavingTemporalExpression) : List HavingGroupCountOperand :=
  (HavingTemporalCore.allAtoms source.core).flatMap fun
    | .shift _ _ amount => amount.atoms.flatMap fun
        | .groupCount operands => operands
        | _ => []
    | _ => []

def repetitionReferences (source : HavingTemporalExpression) : List HavingRepetitionRef :=
  (HavingTemporalCore.allAtoms source.core).flatMap fun
    | .shift _ _ amount => amount.atoms.flatMap fun
        | .repetition reference => [reference]
        | _ => []
    | _ => []

def origins (source : HavingTemporalExpression) : List HavingOrigin :=
  source.references.map (·.origin) ++ source.groupCountOperands.map (·.origin) ++
    source.repetitionReferences.map (·.origin)

/-- Checked core constructors retain the same source-slot boundary as authored elaboration
(spec/05 §§3,6); a hand-built tree cannot carry a value-expression selector here. -/
def coreAdmittedSourceSlot (source : HavingTemporalCore) (withPartialDate : Bool := false) : Bool :=
  match source with
  | .atom (.partialDate _) => withPartialDate
  | .atom (.selection _ _) | .apply (.extremum _) _ _ => false
  | _ => true

def admittedSourceSlot (source : HavingTemporalExpression) (withPartialDate : Bool := false) : Bool :=
  !source.grouped && coreAdmittedSourceSlot source.core withPartialDate

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
      | .shift unit source amount => do
          if !coreAdmittedSourceSlot source true then none else pure ()
          let components ← componentsWith baseYear source
          if !(match unit with
            | .days => components.day
            | .months => components.month && !components.hasTime
            | .years => components.year && !components.hasTime
            | .hours | .minutes | .seconds => components.isFullDateTime) then none else pure ()
          if !amount.isAdmittedResolvedNumericOperation || amount.numericOperationAuthoringCheck != .accepted then none
          else some components
      | .partialDate _ | .today | .baseYearBound _ | .dateConstruction _ => some TemporalComponents.fullDate
  | .apply (.constructor .dateTime) date [time] => do
      if !coreAdmittedSourceSlot date true || !coreAdmittedSourceSlot time then none else pure ()
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

mutual
private def readAtom (profile : ModelZone.ConcreteProfile) (baseYear : Option Int) (phase : Phase)
    (context : ResolvingCorrelationContext Error) (frame : CorrelationFrame) :
    HavingTemporalAtom → Except Error (SimpleComparisonOperand ScalarTemporalValue)
  | .selection kind slots => kind.evaluate baseYear profile phase context frame slots
  | .shift unit source amount => do
      let source ← evaluateCore profile baseYear phase context frame source
      if phase == .computation then
        if let .unknown _ := source then return source
      let amount ← readAmount profile baseYear phase context frame amount
      (applyScalarTemporalShift source amount (shiftScalarTemporalValue profile unit)).mapError fun _ => context.unsupportedDateCalendar
  | .partialDate source => do
      let reference := source.reference
      let cell ← context.read (frame.envAt reference.origin) reference.field.id
      match observeCell phase cell with
      | .value (.partialDate text) =>
          match classifyPartialDateStored source.format source.mode source.youngerThan1900Check text with
          | .presentEmpty => pure .notEvaluated
          | .rejected cause => pure (.unknown cause.toFormalCause)
          | .admitted value => match value.value.resolve source.endpoint with
              | .nonRelevant => pure (.value .nonRelevant true)
              | .date date =>
                  let some instant := profile.resolveLocal? { date, time := { hour := 0, minute := 0, second := 0, valid := by decide } }
                    | throw context.unsupportedDateCalendar
                  pure (.value (.date { instant, parts := date.civil.parts, basis := .storedGregorian }) true)
      | observation => pure (projectScalarTemporalObservationWith baseYear (some profile) reference.field observation)
  | .field reference => do
      let cell ← context.read (frame.envAt reference.origin) reference.field.id
      pure (projectScalarTemporalObservationWith baseYear (some profile)
        reference.field (observeCell phase cell))
  | .rangeBound origin field components bound => do
      let cell ← context.read (frame.envAt origin) field.id
      (projectScalarRangeBoundObservation profile (!components.year && baseYear.isNone)
        bound (observeCell phase cell)).mapError fun _ => context.unsupportedDateCalendar
  | .timeConstruction components => do
      pure (← readTimeComponents profile baseYear phase context frame components).asScalarTemporalOperand
  | .dateConstruction components => do
      let (observation, relevance) ← observeDateComponents profile baseYear phase context frame components
      match observation with
      | .unavailable cause => pure (.unknown cause)
      | _ =>
          if relevance == .nonRelevant then pure (.value .nonRelevant true)
          else pure (components.finishValue observation).asScalarTemporalOperand
  | .timeLiteral value => pure (.value (.time value) true)
  | .dateTimeLiteral value => do
      let some instant := profile.resolveLocal? value | throw context.temporalValueFailure
      pure (.value (.instant instant) true)
  | .dateLiteral value yearPresent => do
      let some date := profile.resolveCompletedDateParts? value.civil.parts | throw context.temporalValueFailure
      pure (.value (if yearPresent || baseYear.isSome then .date date
        else .yearless date { month := date.parts.month, day := date.parts.day }) true)
  | .baseYearBound bound => do
      let some year := baseYear | throw context.unsupportedDateCalendar
      let some date := profile.resolveCompletedDateParts? (baseYearRangeParts year bound) |
        throw context.unsupportedDateCalendar
      pure (.value (.date date) true)
  | .now => do
      let some world := context.world | throw context.worldUnavailable
      pure (.value (.instant world.now) true)
  | .today => do
      let some world := context.world | throw context.worldUnavailable
      let some label := profile.localDate? world.now | throw context.unsupportedDateCalendar
      let some date := profile.resolveCompletedDateParts? label.civil.parts | throw context.temporalValueFailure
      pure (.value (.date date) true)

termination_by atom => sizeOf atom

/-- The shared temporal tree reaches arguments in order; computation poison aborts before
later arguments, while validation keeps reading (spec/05 stamp-construction grid). -/
private def evaluateCore (profile : ModelZone.ConcreteProfile) (baseYear : Option Int) (phase : Phase)
    (context : ResolvingCorrelationContext Error) (frame : CorrelationFrame) (core : HavingTemporalCore) :
    Except Error (SimpleComparisonOperand ScalarTemporalValue) :=
  let reached (operand : SimpleComparisonOperand ScalarTemporalValue) :
      Except (Sum FormalCause Error) (SimpleComparisonOperand ScalarTemporalValue) :=
    match phase, operand with
    | .computation, .unknown cause => .error (.inl cause)
    | _, operand => .ok operand
  let result := core.evalWithResultSubterm
    (fun atom _ => do reached (← (readAtom profile baseYear phase context frame atom).mapError Sum.inr))
    (fun operation _ operands => do
      let result := match operation with
        | .constructor operation => operation.apply profile operands
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

termination_by sizeOf core

private def readAmount (profile : ModelZone.ConcreteProfile) (baseYear : Option Int) (phase : Phase)
    (context : ResolvingCorrelationContext Error) (frame : CorrelationFrame) (amount : HavingTemporalAmount) :
    Except Error (Except NumericValidationUnavailable NumericArithmeticOutcome) := do
  let resolved : Except (Sum FormalCause Error) _ := amount.mapMSubterm fun source _hNumericSource => do
    let value ← (source.readArithmetic phase context frame
      (fun part source _ => do
        let source ← evaluateCore profile baseYear phase context frame source
        (part.observeScalarCore profile source NumericValidationUnavailable.formal .nonRelevant).mapError fun _ => context.unsupportedDateCalendar)
      (fun unit left right _ _ => do
        let pair ← readTemporalPair phase (fun first : Bool =>
          if first then evaluateCore profile baseYear phase context frame left
          else evaluateCore profile baseYear phase context frame right)
          scalarTemporalFormalCause? true false
        match pair with
        | .error cause => pure (.error (.formal cause))
        | .ok (first, second) =>
            (observeScalarTemporalDifference profile unit first second NumericValidationUnavailable.formal .nonRelevant).mapError fun _ => context.unsupportedDateCalendar)).mapError Sum.inr
    match phase, value with
    | .computation, .error (.formal cause) => throw (.inl cause)
    | _, value => pure value
  match resolved with
  | .error (.inl cause) => pure (.error (.formal cause))
  | .error (.inr fault) => throw fault
  | .ok expression => pure (expression.lowerForEvaluation.evalNumericOperationTree id)
termination_by sizeOf amount
decreasing_by all_goals first | decreasing_tactic | omega | (simp_all +arith; omega)

private def readDateOperand (profile : ModelZone.ConcreteProfile) (baseYear : Option Int) (phase : Phase)
    (context : ResolvingCorrelationContext Error) (frame : CorrelationFrame) (component : HavingDateComponent) :
    StateT DateComponentRelevance (Except Error) CheckedConstructedDateComponent := do
  match component with
  | .direct origin source => liftM (readHavingDateComponent origin source phase context frame)
  | .expression part source =>
      let value ← liftM (evaluateCore profile baseYear phase context frame source)
      let numeric ← liftM (((TemporalNumericPart.date part).observeScalarCore profile value some none).mapError
        fun _ => context.unsupportedDateCalendar)
      (constructorComponentOfNumeric numeric).asDateComponent
termination_by sizeOf component

private def observeDateComponents (profile : ModelZone.ConcreteProfile) (baseYear : Option Int) (phase : Phase)
    (context : ResolvingCorrelationContext Error) (frame : CorrelationFrame) (components : HavingDateComponents) :
    Except Error (ConstructedDateObservation × DateComponentRelevance) :=
  (components.attach.evaluateComponentsWith
    (fun ⟨source, _⟩ => readDateOperand profile baseYear phase context frame source) phase).run .relevant
termination_by sizeOf components

private def readTimeComponents (profile : ModelZone.ConcreteProfile) (baseYear : Option Int) (phase : Phase)
    (context : ResolvingCorrelationContext Error) (frame : CorrelationFrame) (components : HavingTimeComponents) :
    Except Error TimeConstructionResult :=
  components.evaluateWithSubterm (fun component _ => do
    match _hComponent : component with
    | .direct origin source => readTimeComponent origin source profile phase context frame
    | .expression part source =>
        let value ← evaluateCore profile baseYear phase context frame source
        let numeric ← ((TemporalNumericPart.time part).observeScalarCore profile value some none).mapError
          fun _ => context.unsupportedDateCalendar
        pure (constructorComponentOfNumeric numeric)) phase
termination_by sizeOf components
decreasing_by all_goals first | decreasing_tactic | omega | (simp_all +arith; omega)
end

def evaluate (source : HavingTemporalExpression) (phase : Phase)
    (context : ResolvingCorrelationContext Error) (frame : CorrelationFrame) :
    Except Error (SimpleComparisonOperand ScalarTemporalValue) :=
  evaluateCore source.profile source.baseYear phase context frame source.core

def observeConstructedDate (source : HavingConstructedDate) (phase : Phase)
    (context : ResolvingCorrelationContext Error) (frame : CorrelationFrame) : Except Error ConstructedDateObservation := do
  let (observation, relevance) ← observeDateComponents source.components.profile source.baseYear phase context frame source.components
  match observation with
  | .unavailable cause => pure (.unavailable cause)
  | _ =>
      if relevance == .nonRelevant then pure (.resolved .unknown)
      else pure (source.components.applyProfileReality observation)

def readNumeric (source : HavingTemporalExpression) (part : TemporalNumericPart) (phase : Phase)
    (context : ResolvingCorrelationContext Error) (frame : CorrelationFrame)
    (formal : FormalCause → Unavailable) (nonRelevant : Unavailable) :
    Except Error (Except Unavailable NumericArithmeticOutcome) := do
  let value ← source.evaluate phase context frame
  (part.observeScalarCore source.profile value formal nonRelevant).mapError fun _ => context.unsupportedDateCalendar

/-- Recursive differences share the phase-specific operand order with ordinary temporal expressions. -/
def readDifference (left right : HavingTemporalExpression) (unit : TemporalOperationUnit) (phase : Phase)
    (context : ResolvingCorrelationContext Error) (frame : CorrelationFrame)
    (formal : FormalCause → Unavailable) (nonRelevant : Unavailable) :
    Except Error (Except Unavailable NumericArithmeticOutcome) := do
  match ← readTemporalPair phase (fun source => source.evaluate phase context frame)
      scalarTemporalFormalCause? left right with
  | .error cause => pure (.error (formal cause))
  | .ok (first, second) =>
      (observeScalarTemporalDifference left.profile unit first second formal nonRelevant).mapError fun _ => context.unsupportedDateCalendar

end HavingTemporalExpression

def HavingConstructedDate.asTemporal (source : HavingConstructedDate) : HavingTemporalExpression :=
  { core := .atom (.dateConstruction source.components), profile := source.components.profile, baseYear := source.baseYear }

def HavingConstructedDate.references (source : HavingConstructedDate) : List HavingPresenceRef :=
  source.asTemporal.presenceSlots.flatMap (·.references)

def HavingConstructedDate.evalValidationRead (source : HavingConstructedDate) (operation : ConstructedDateValidityOp)
    (context : ResolvingCorrelationContext Error) (frame : CorrelationFrame) : Except Error Verdict := do
  pure ((← HavingTemporalExpression.observeConstructedDate source .validation context frame).validityVerdict operation |>.toOption.getD .unknown)

def HavingConstructedDate.evalComputationRead (source : HavingConstructedDate) (operation : ConstructedDateValidityOp)
    (context : ResolvingCorrelationContext Error) (frame : CorrelationFrame) : Except Error ComputationConditionResult := do
  pure (match (← HavingTemporalExpression.observeConstructedDate source .computation context frame).validityVerdict operation with
    | .error cause => .poison cause
    | .ok (.fired _) => .holds
    | .ok _ => .notTrue)

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
