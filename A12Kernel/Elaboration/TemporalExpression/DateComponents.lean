import A12Kernel.Elaboration.TemporalExpression.Types

namespace A12Kernel

abbrev ScalarDateComponent (model : FlatModel) :=
  Sum (Sum (CheckedConstructedDateSource model) (CheckedIndexedDateComponent model)) (ScalarTemporalNumericAtom model)

def elaborateScalarDateLeaf (model : FlatModel) (rowGroup : GroupPath)
    (scope : List RepeatableLevel) (position : ConstructedDateComponentPosition)
    (surface : Sum SurfaceConstructedDateSource SurfaceSemanticIndex) :
    Except ScalarTemporalExpressionError (Sum (CheckedConstructedDateSource model) (CheckedIndexedDateComponent model)) := do
  match surface with
  | .inl source => .inl <$> (elaborateConstructedDateSource model position source scope).mapError .dateComponents
  | .inr authored =>
      let selection ← (elaborateSemanticIndexSource model rowGroup authored).mapError .indexed
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

/-- Relevance is separate from component payload: a later poison still wins after a cause-free
non-relevant extraction (Date-component ordering probe, 2026-10-06; spec/05 §3). -/
inductive DateComponentRelevance where
  | relevant
  | nonRelevant
  deriving DecidableEq

def observeScalarDateComponent (value : Except NumericValidationUnavailable NumericArithmeticOutcome) :
    StateT DateComponentRelevance (Except ScalarTemporalEvaluationFault) CheckedConstructedDateComponent := do
  match value with
  | .error (.formal cause) => pure (.unavailable cause)
  | .error .nonRelevant =>
      set DateComponentRelevance.nonRelevant
      pure .empty
  | .error _ => throw .calendarUnavailable
  | .ok .notEvaluated => pure .empty
  | .ok (.value value fillability) =>
      pure (if fillability.canGrow || fillability.canShrink then .empty
        else .value (temporalShiftAmountToInt32 value))

def finishScalarDateComponents (checked : CheckedConstructedDateComponents model Source)
    (observation : ConstructedDateObservation) (relevance : DateComponentRelevance) :
    Except ScalarTemporalEvaluationFault (SimpleComparisonOperand ScalarTemporalValue) := do
  match observation with
  | .unavailable cause => pure (.unknown cause)
  | _ =>
      if relevance == .nonRelevant then return .value .nonRelevant true
      match ← (checked.finishValue observation).mapError scalarDateFault with
      | .value instant parts notGiven => pure (.value (.date { instant, parts, basis := .legacyHybrid }) (!notGiven))
      | .noValue notGiven => pure (.value .noValue (!notGiven))
      | .unavailable cause => pure (.unknown cause)

end A12Kernel
