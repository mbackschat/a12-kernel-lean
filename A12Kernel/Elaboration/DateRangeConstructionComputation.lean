import A12Kernel.Elaboration.DateRangeConstructionComparison
import A12Kernel.Semantics.TemporalApplication

/-! # Checked direct DateRange construction computation -/

namespace A12Kernel

/-- Whether one construction endpoint profile supplies an exact full Date for this bounded target computation. -/
def DateRangeEndpointFormat.supportsConstructionTarget :
    DateRangeEndpointFormat → Bool
  | .full _ => true
  | _ => false

/-- Verify that the model-owned direct DateRange target remains in the computation's declaring group. -/
def FlatModel.ownsDirectDateRangeTarget
    (model : FlatModel) (declaringGroup : GroupPath)
    (target : CheckedDirectDateRange model) : Bool :=
  match model.lookupUniqueId target.source.id with
  | .ok declaration => declaration.groupPath == declaringGroup
  | .error _ => false

/-- Static refusal before one direct DateRange construction can reach its target. -/
inductive DateRangeConstructionComputationElabError where
  | construction (cause : DateRangeConstructionElabError)
  | target (cause : DirectDateRangeElabError)
  | targetGroup (actual expected : GroupPath)
  | targetFormat (actual : DateRangeInputFormat)
  | endpointFormat (start finish : DateRangeEndpointFormat)
  | incoherentCore
  deriving Repr, DecidableEq

/-- One checked full-Date construction and its direct nonrepeatable dotted/dash DateRange target. -/
structure CheckedDateRangeConstructionComputation (model : FlatModel) where
  construction : CheckedDateRangeConstruction model
  target : CheckedDirectDateRange model
  declaringGroup : GroupPath
  targetOwnedByGroup : model.ownsDirectDateRangeTarget declaringGroup target = true
  targetFormat : target.format = .exact .dayMonthYearDash
  endpointsSupported :
    (construction.start.format.supportsConstructionTarget &&
      construction.finish.format.supportsConstructionTarget) = true

/-- Certify one full-Date construction and one dotted/dash DateRange target against the same checked model. -/
def elaborateDateRangeConstructionComputation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (start finish : FieldId) :
    Except DateRangeConstructionComputationElabError
      (CheckedDateRangeConstructionComputation model) := do
  let construction ← elaborateDateRangeConstruction model start finish
    |>.mapError .construction
  let targetDeclaration ← model.resolveNonrepeatableDeclarationById targetField
    |>.mapError (fun error => .target (.source error))
  if _hGroup : targetDeclaration.groupPath = declaringGroup then
    let target ← elaborateDirectDateRange model targetField |>.mapError .target
    if hOwned : model.ownsDirectDateRangeTarget declaringGroup target then
      if hTargetFormat : target.format = .exact .dayMonthYearDash then
        if hEndpoints :
            construction.start.format.supportsConstructionTarget &&
              construction.finish.format.supportsConstructionTarget then
          pure {
            construction
            target
            declaringGroup
            targetOwnedByGroup := hOwned
            targetFormat := hTargetFormat
            endpointsSupported := hEndpoints
          }
        else
          throw (.endpointFormat construction.start.format construction.finish.format)
      else
        throw (.targetFormat target.format)
    else
      throw .incoherentCore
  else
    throw (.targetGroup targetDeclaration.groupPath declaringGroup)

/-- Project one evaluated construction into the target result domain while reusing its established formal-before-empty precedence. -/
def DateRangeConstructionObservation.asComputationResult
    (observation : DateRangeConstructionObservation) : DateRangeComputationResult :=
  match observation.comparisonOperand with
  | .notEvaluated => .noValue
  | .unknown cause => .poison cause
  | .value (.exact range) _ => .value range
  | .value _ _ => .poison .malformed

inductive DateRangeConstructionComputationFault where
  | construction (cause : DateRangeConstructionFault)
  | target (cause : DateRangeTargetEvaluationFault)
  deriving Repr, DecidableEq

/-- Execute/Analyze/Explain result retaining both endpoint observations beside the typed target outcome. -/
structure DateRangeConstructionComputationResult where
  construction : DateRangeConstructionObservation
  outcome : DateRangeTargetOutcome
  deriving Repr, DecidableEq

namespace CheckedDateRangeConstructionComputation

/-- Read the two checked endpoints once in computation phase, then render their typed range through the checked target policy. -/
def execute (operation : CheckedDateRangeConstructionComputation model)
    (input : CheckedDocument model) :
    Except DateRangeConstructionComputationFault
      DateRangeConstructionComputationResult := do
  let construction ← operation.construction.evaluate .computation input
    |>.mapError .construction
  let outcome ← DateRangeFormat.dayMonthYearDash.evaluateComputationResult
      construction.asComputationResult
    |>.mapError .target
  pure { construction, outcome }

end CheckedDateRangeConstructionComputation

end A12Kernel
