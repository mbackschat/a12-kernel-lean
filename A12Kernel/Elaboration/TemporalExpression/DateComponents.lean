import A12Kernel.Elaboration.TemporalExpression.ReadContext

namespace A12Kernel

abbrev ScalarDateComponent (model : FlatModel) :=
  Sum (Sum (CheckedConstructedDateSource model) (CheckedIndexedDateComponent model)) (ScalarTemporalNumericAtom model)

/-- Validity requires an immediate entity component; extractor dependencies do not qualify
(CheckDateValidityConditionImpl and Date-validity static grid, 2026-10-06). -/
def CheckedConstructedDateComponents.hasImmediateEntity
    (components : CheckedConstructedDateComponents model (ScalarDateComponent model)) : Bool :=
  components.sources.any fun
    | .inl (.inl (.numberField _)) | .inl (.inl (.stringField _))
    | .inl (.inl (.dateYearField _)) | .inl (.inr _) => true
    | _ => false

/-- Preserve the established direct partial evaluator only when every component belongs to its
original source domain; its direct partial faults remain owned by the established evaluator. -/
def CheckedConstructedDateComponents.directComponents?
    (components : CheckedConstructedDateComponents model (ScalarDateComponent model)) :
    Option (CheckedConstructedDateComponents model) := do
  let direct : ScalarDateComponent model → Option (CheckedConstructedDateSource model)
    | .inl (.inl source) => some source
    | _ => none
  let day ← direct components.day
  let month ← direct components.month
  let year ← match components.year with
    | .complete source => .complete <$> direct source
    | .baseYear year => pure (.baseYear year)
    | .centuryAndShortYear century shortYear => do
        pure (.centuryAndShortYear (← direct century) (← direct shortYear))
  pure { day, month, year, profile := components.profile, profileSelected := components.profileSelected }

def elaborateScalarDateLeaf (model : FlatModel) (rowGroup : GroupPath)
    (scope : List RepeatableLevel) (position : ConstructedDateComponentPosition)
    (surface : Sum SurfaceConstructedDateSource SurfaceSemanticIndex) :
    Except ScalarTemporalExpressionError (Sum (CheckedConstructedDateSource model) (CheckedIndexedDateComponent model)) := do
  match surface with
  | .inl source => .inl <$> (elaborateConstructedDateSource model position source scope).mapError .dateComponents
  | .inr authored =>
      let selection ← (elaborateSemanticIndexSource model rowGroup authored (some scope)).mapError .indexed
      let field := selection.targetDeclaration
      let source ← match field.policy.kind.surfaceKind with
        | .number => pure (SurfaceConstructedDateSource.numberField field.id)
        | .string => pure (.stringField field.id)
        | .temporal _ => pure (.dateYearField field.id)
        | _ => throw .unsupportedSource
      let source ← (elaborateConstructedDateSource model position source field.repeatableScope).mapError .dateComponents
      if sameTarget : source.fieldId? = some selection.targetDeclaration.id then
        pure (.inr { selection, source, sameTarget })
      else throw .unsupportedSource

def scalarDateFault : ConstructedDateEvaluationFault → ScalarTemporalEvaluationFault
  | .stringNotConvertible _ _ => .componentNumberInvalid
  | _ => .calendarUnavailable

def readScalarDateLeaf (phase : Phase) (context : ScalarComputationContext) :
    Sum (CheckedConstructedDateSource model) (CheckedIndexedDateComponent model) →
      Except ScalarTemporalEvaluationFault CheckedConstructedDateComponent
  | .inl source => (source.readWith phase context.read context.storedText context.world).mapError scalarDateFault
  | .inr source => do
      let some addressed := context.addressed | throw .calendarUnavailable
      match ← (source.selection.selectEnvironmentWith phase context.semanticIndexColumnReader
          context.row context.read context.storedText).mapError (fun _ => .calendarUnavailable) with
      | .empty => pure .empty
      | .unknown cause | .poison cause => pure (.unavailable cause)
      | .value row =>
          (source.source.readWith phase (addressed.read row) (addressed.storedText row) context.world).mapError scalarDateFault

def readPartialScalarDateLeaf (context : ScalarComputationContext)
    (partialRead : TemporalPartialReadContext model) :
    Sum (CheckedConstructedDateSource model) (CheckedIndexedDateComponent model) →
      Except ScalarTemporalEvaluationFault (Option CheckedConstructedDateComponent)
  | .inl source => do
      match source.fieldId? with
      | none => some <$> (source.readWith .validation context.read context.storedText context.world).mapError scalarDateFault
      | some field =>
          let some cell ← partialRead.readCell context.row field | return none
          let text ← partialRead.storedText context.row field cell
          some <$> (source.readWith .validation (fun _ => cell) (fun _ => text) context.world).mapError scalarDateFault
  | .inr source => do
      match ← partialRead.selectedCell source.selection context.row with
      | none => pure none
      | some .empty => pure (some .empty)
      | some (.unknown cause) | some (.poison cause) => pure (some (.unavailable cause))
      | some (.value (cell, text)) =>
          some <$> (source.source.readWith .validation (fun _ => cell) (fun _ => text) context.world).mapError scalarDateFault

def observeScalarDateComponent (value : Except NumericValidationUnavailable NumericArithmeticOutcome) :
    StateT DateComponentRelevance (Except ScalarTemporalEvaluationFault) CheckedConstructedDateComponent := do
  let component ← match value with
    | .error (.formal cause) => pure (constructorComponentOfNumeric (.error (some cause)))
    | .error .nonRelevant => pure (constructorComponentOfNumeric (.error none))
    | .error _ => throw .calendarUnavailable
    | .ok outcome => pure (constructorComponentOfNumeric (.ok outcome))
  component.asDateComponent

def finishScalarDateValidity (checked : CheckedConstructedDateComponents model Source)
    (observation : ConstructedDateObservation) (relevance : DateComponentRelevance) :
    Except ScalarTemporalEvaluationFault ConstructedDateObservation :=
  match observation with
  | .unavailable cause => pure (.unavailable cause)
  | _ => if relevance == .nonRelevant then pure (.resolved .unknown)
      else (checked.applyProfileReality observation).mapError scalarDateFault

def finishScalarDateComponents (checked : CheckedConstructedDateComponents model Source)
    (observation : ConstructedDateObservation) (relevance : DateComponentRelevance) :
    Except ScalarTemporalEvaluationFault (SimpleComparisonOperand ScalarTemporalValue) := do
  match observation with
  | .unavailable cause => pure (.unknown cause)
  | _ =>
      if relevance == .nonRelevant then return .value .nonRelevant true
      pure (← (checked.finishValue observation).mapError scalarDateFault).asScalarTemporalOperand

end A12Kernel
