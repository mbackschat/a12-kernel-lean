import A12Kernel.Elaboration.TemporalExpression
import A12Kernel.Semantics.ScalarTemporalDifference

/-! # Numeric consumers of checked temporal expressions

The temporal source owns recursive evaluation, calendar provenance and missingness. Numeric
extraction and differences consume those results without replacing a formal source by numeric zero.
-/

namespace A12Kernel

inductive TemporalNumericExpressionError where
  | source (error : ScalarTemporalExpressionError)
  | literalNotAllowed
  | sourceSlot
  | componentNotExposed
  | calendarUnavailable
  deriving Repr, DecidableEq

/-- Numeric projections and differences retain their temporal operands in authored order. -/
inductive TemporalNumericExpressionOf (Source : Type) where
  | projection (part : TemporalNumericPart) (source : Source)
  | difference (unit : TemporalOperationUnit) (left right : Source)

namespace TemporalNumericExpressionOf

def sources : TemporalNumericExpressionOf Source → List Source
  | .projection _ source => [source]
  | .difference _ left right => [left, right]

def admitted (hasBaseYear : Bool) (components : Source → TemporalComponents) :
    TemporalNumericExpressionOf Source → Bool
  | .projection part source => part.admitsComponents (components source) hasBaseYear
  | .difference unit left right => unit.admitsScalarDifference hasBaseYear (components left) (components right)

end TemporalNumericExpressionOf

abbrev SurfaceTemporalNumericExpression := TemporalNumericExpressionOf SurfaceScalarTemporalExpression

/-- Checked temporal numeric operations preserve every operand and certify the shared component gate. -/
structure CheckedTemporalNumericExpression (model : FlatModel) where
  private mk ::
  core : TemporalNumericExpressionOf (CheckedScalarTemporalExpression model)
  profile : ModelZone.ConcreteProfile
  admitted : core.admitted model.hasBaseYear (·.components) = true

def elaborateTemporalNumericOperation (model : FlatModel) (declaringGroup : GroupPath)
    (surface : SurfaceTemporalNumericExpression) (targetGroup? : Option GroupPath := none) :
    Except TemporalNumericExpressionError (CheckedTemporalNumericExpression model) := do
  let core ← match surface with
    | .projection part surface => do
        match surface with
        | .dateLiteral _ _ | .timeLiteral _ | .dateTimeLiteral _ => throw .literalNotAllowed
        | _ => pure ()
        if !surface.admittedSourceSlot .ordinary then throw .sourceSlot
        pure (.projection part (← (elaborateScalarTemporalExpression model declaringGroup surface targetGroup?).mapError .source))
    | .difference unit left right => do
        if !left.admittedSourceSlot .withPartialDate || !right.admittedSourceSlot .withPartialDate then throw .sourceSlot
        let first ← (elaborateScalarTemporalExpression model declaringGroup left targetGroup?).mapError .source
        let second ← (elaborateScalarTemporalExpression model declaringGroup right targetGroup?).mapError .source
        pure (.difference unit first second)
  if h : core.admitted model.hasBaseYear (·.components) = true then
    let some profile := ModelZone.ConcreteProfile.ofId? model.timeZoneId | throw .calendarUnavailable
    pure { core, profile, admitted := h }
  else throw .componentNotExposed

def elaborateTemporalNumericExpression (model : FlatModel) (declaringGroup : GroupPath)
    (surface : SurfaceScalarTemporalExpression) (part : TemporalNumericPart)
    (targetGroup? : Option GroupPath := none) :
    Except TemporalNumericExpressionError (CheckedTemporalNumericExpression model) :=
  elaborateTemporalNumericOperation model declaringGroup (.projection part surface) targetGroup?

namespace CheckedTemporalNumericExpression

def fieldIds (expression : CheckedTemporalNumericExpression model) : List FieldId :=
  expression.core.sources.flatMap (·.fieldIds)

def storedTextFields (expression : CheckedTemporalNumericExpression model) : List FieldId :=
  expression.core.sources.flatMap (·.storedTextFields)

def bindingScopes (expression : CheckedTemporalNumericExpression model) : List (List RepeatableLevel) :=
  expression.core.sources.flatMap (·.bindingScopes)

def boundFieldIds (expression : CheckedTemporalNumericExpression model) : List FieldId :=
  expression.core.sources.flatMap (·.boundFieldIds)

def requiresAddressed (expression : CheckedTemporalNumericExpression model) : Bool :=
  expression.core.sources.any (·.requiresAddressed)

def hasHaving (expression : CheckedTemporalNumericExpression model) : Bool :=
  expression.core.sources.any (·.core.hasHaving)

def referencesWith (expression : CheckedTemporalNumericExpression model) (field : FieldId)
    (filterReads : CorrelatedHaving → Bool) : Bool :=
  expression.core.sources.any (·.referencesWith field filterReads)

def referencesField (expression : CheckedTemporalNumericExpression model) (field : FieldId) : Bool :=
  expression.core.sources.any (·.referencesField field)

/-- Project the common temporal result while retaining its independent missingness and failure. -/
def evalResult (expression : CheckedTemporalNumericExpression model) (phase : Phase)
    (context : FlatContext) (addressed : Option ComputationFillContext := none) (row : Env := [])
    (partialRead? : Option (TemporalPartialReadContext model) := none) : Except ScalarTemporalEvaluationFault
      (Except NumericValidationUnavailable NumericArithmeticOutcome) := do
  let read (source : CheckedScalarTemporalExpression model) := source.evalResult phase context addressed row partialRead?
  match expression.core with
  | .projection part source => part.observeScalar expression.profile (← read source)
  | .difference unit left right =>
      match ← readTemporalPair phase read scalarTemporalFormalCause? left right with
      | .error cause => pure (.error (.formal cause))
      | .ok (first, second) =>
          (observeScalarTemporalDifference expression.profile unit first second NumericValidationUnavailable.formal .nonRelevant)
            |>.mapError ScalarTemporalPrimitiveFault.toEvaluation

end CheckedTemporalNumericExpression
end A12Kernel
