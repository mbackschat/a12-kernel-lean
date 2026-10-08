import A12Kernel.Semantics.HavingNumericAtom
import A12Kernel.Semantics.HavingFirstFilled
import A12Kernel.Semantics.HavingGroupCount
import A12Kernel.Semantics.HavingNumericProduct
import A12Kernel.Semantics.HavingCollectionCount
import A12Kernel.Semantics.HavingNumberAggregate
import A12Kernel.Semantics.HavingTemporalExpression

/-! Correlated numeric atoms and phase-specific checked reads. -/

namespace A12Kernel

abbrev HavingNumericAtom := HavingNumericAtomOf HavingTemporalExpression

namespace HavingNumericAtom

abbrev temporalDifference := @HavingNumericAtomOf.temporalDifference HavingTemporalExpression
abbrev firstFilled := @HavingNumericAtomOf.firstFilled HavingTemporalExpression
abbrev groupCount := @HavingNumericAtomOf.groupCount HavingTemporalExpression
abbrev product := @HavingNumericAtomOf.product HavingTemporalExpression
abbrev collectionCount := @HavingNumericAtomOf.collectionCount HavingTemporalExpression
abbrev aggregate := @HavingNumericAtomOf.aggregate HavingTemporalExpression
abbrev dateDifference := @HavingNumericAtomOf.dateDifference HavingTemporalExpression
abbrev dayDifference := @HavingNumericAtomOf.dayDifference HavingTemporalExpression
abbrev dateTimeDifference := @HavingNumericAtomOf.dateTimeDifference HavingTemporalExpression
abbrev baseYear := @HavingNumericAtomOf.baseYear HavingTemporalExpression
abbrev baseYearDatePart := @HavingNumericAtomOf.baseYearDatePart HavingTemporalExpression
abbrev clockPart := @HavingNumericAtomOf.clockPart HavingTemporalExpression
abbrev fieldValueAsNumber := @HavingNumericAtomOf.fieldValueAsNumber HavingTemporalExpression
abbrev field := @HavingNumericAtomOf.field HavingTemporalExpression
abbrev stringLength := @HavingNumericAtomOf.stringLength HavingTemporalExpression
abbrev stringRange := @HavingNumericAtomOf.stringRange HavingTemporalExpression
abbrev dateRangeBoundPart := @HavingNumericAtomOf.dateRangeBoundPart HavingTemporalExpression
abbrev temporalExpressionPart := @HavingNumericAtomOf.temporalExpressionPart HavingTemporalExpression
abbrev temporalPart := @HavingNumericAtomOf.temporalPart HavingTemporalExpression
abbrev repetition := @HavingNumericAtomOf.repetition HavingTemporalExpression

def origins : HavingNumericAtom → List HavingOrigin :=
  HavingNumericAtomOf.originsWith HavingTemporalExpression.origins

def fieldOrigins : HavingNumericAtom → List (HavingOrigin × FieldId) :=
  HavingNumericAtomOf.fieldOriginsWith (fun source => source.references.map fun ref => (ref.origin, ref.fieldId))

def summary : HavingNumericAtom → NumericScaleSummary := HavingNumericAtomOf.summary

end HavingNumericAtom

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

private def HavingNumericAtom.readArithmetic (phase : Phase)
    (context : ResolvingCorrelationContext Error) (frame : CorrelationFrame) :
    HavingNumericAtom → Except Error (Except NumericValidationUnavailable NumericArithmeticOutcome) :=
  fun atom => HavingNumericAtomOf.readArithmetic phase context frame atom
    (fun part source _ => source.readNumeric part phase context frame .formal .nonRelevant)
    (fun unit left right _ _ => left.readDifference right unit phase context frame .formal .nonRelevant)
    (if phase == .validation then pure (.error .nonRelevant) else .error context.unsupportedDateCalendar)

def HavingNumericAtom.readValidationResolving (context : ResolvingCorrelationContext Error)
    (frame : CorrelationFrame) (atom : HavingNumericAtom) :
    Except Error (Except Unit NumericArithmeticOutcome) := do
  let result ← atom.readArithmetic .validation context frame
  pure (result.mapError (fun _ => ()) |>.map fun value => match atom, value with
    | .field _, .value amount _ => .value amount .fixed
    | _, value => value)

def HavingNumericAtom.readValidation (context : CorrelationContext) (frame : CorrelationFrame) :
    HavingNumericAtom → Except Unit NumericArithmeticOutcome
  | .field reference =>
      match reference.resolveIn context frame with
      | .value amount => .ok (.value amount .fixed)
      | .unknown _ => .error ()
  | .repetition reference =>
      match frame.rowAt? reference with
      | some row => .ok (.value row .fixed)
      | none => .error ()
  | atom => ((atom.readValidationResolving context.asResolving frame).mapError (fun _ => ())).bind id

def HavingNumericAtom.readComputationResolving (context : ResolvingCorrelationContext Error)
    (frame : CorrelationFrame) (atom : HavingNumericAtom) : Except Error NumericComputationResult := do
  match ← atom.readArithmetic .computation context frame with
  | .error (.formal cause) => pure (.poison cause)
  | .error _ | .ok .notEvaluated => pure .domainFailure
  | .ok (.value amount _) => pure (.value amount)

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

namespace HavingNumericAtomOf
export HavingNumericAtom (origins fieldOrigins readValidation readValidationResolving readComputation readComputationIn readComputationResolving)
end HavingNumericAtomOf

end A12Kernel
