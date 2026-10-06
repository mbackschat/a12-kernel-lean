import A12Kernel.Elaboration.TemporalExpression

/-! # Numeric projection of checked temporal expressions

The temporal source owns recursive evaluation, calendar provenance and missingness. Numeric
extraction consumes that result without replacing an unavailable source by numeric zero.
-/

namespace A12Kernel

inductive TemporalNumericExpressionError where
  | source (error : ScalarTemporalExpressionError)
  | literalNotAllowed
  | sourceSlot
  | componentNotExposed
  | calendarUnavailable
  deriving Repr, DecidableEq

/-- A numeric extractor retains the complete checked temporal source and its model-zone profile.
The component certificate prevents an evaluator from guessing a missing date or clock half. -/
structure CheckedTemporalNumericExpression (model : FlatModel) where
  private mk ::
  source : CheckedScalarTemporalExpression model
  part : TemporalNumericPart
  profile : ModelZone.ConcreteProfile
  componentAdmitted : part.admitsComponents source.components model.hasBaseYear = true

def elaborateTemporalNumericExpression (model : FlatModel) (declaringGroup : GroupPath)
    (surface : SurfaceScalarTemporalExpression) (part : TemporalNumericPart)
    (targetGroup? : Option GroupPath := none) :
    Except TemporalNumericExpressionError (CheckedTemporalNumericExpression model) := do
  match surface with
  | .dateLiteral _ _ | .timeLiteral _ | .dateTimeLiteral _ => throw .literalNotAllowed
  | _ => pure ()
  if !surface.admittedSourceSlot then throw .sourceSlot
  let source ← (elaborateScalarTemporalExpression model declaringGroup surface targetGroup?).mapError .source
  if h : part.admitsComponents source.components model.hasBaseYear = true then
    let some profile := ModelZone.ConcreteProfile.ofId? model.timeZoneId | throw .calendarUnavailable
    pure { source, part, profile, componentAdmitted := h }
  else
    throw .componentNotExposed

namespace CheckedTemporalNumericExpression

/-- Project the common temporal result while retaining its independent missingness and failure. -/
def evalResult (expression : CheckedTemporalNumericExpression model) (phase : Phase)
    (context : FlatContext) : Except ScalarTemporalEvaluationFault
      (Except NumericValidationUnavailable NumericArithmeticOutcome) := do
  expression.part.observeScalar expression.profile (← expression.source.evalResult phase context)

end CheckedTemporalNumericExpression
end A12Kernel
