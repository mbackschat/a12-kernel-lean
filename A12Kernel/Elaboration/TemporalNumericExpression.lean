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

def TemporalNumericExpressionError.precisionDiagnostic? : TemporalNumericExpressionError → Option KernelStaticDiagnostic
  | .source (.temporalPartPrecision _ _) => some .invalidDateType
  | _ => none

/-- Stored projections preserve only components admitted by their owning declaration; full
expressions and differences retain the existing temporal value account (spec/05 §3, KF529). -/
inductive CheckedTemporalNumericCore (model : FlatModel) where
  | temporal (operation : TemporalNumericExpressionOf (CheckedScalarTemporalExpression model))
  | storedProjection (source : ScalarTemporalNumericAtom model)

def CheckedTemporalNumericCore.admitted (model : FlatModel) (scope : List RepeatableLevel) :
    CheckedTemporalNumericCore model → Bool
  | .temporal operation => operation.admitted model.hasBaseYear (·.components)
  | .storedProjection (.numeric (.temporalPart .inner field part format)) =>
      model.admitsTemporalNumericPart field part format &&
        (model.lookupUniqueId field.id).toOption.any (·.repetitionBoundBy scope)
  | .storedProjection (.indexedPart selection part format) =>
      selection.bindingScopes.all (·.isPrefixOf scope) &&
        selection.targetDeclaration.toTemporalField?.any fun field =>
          model.admitsTemporalNumericPart field part format
  | .storedProjection (.numeric _) | .storedProjection (.ordinary _) |
      .storedProjection (.projection _ _ _) => false

/-- A numeric projection retains the host scope as part of its stored-source certificate. -/
structure CheckedTemporalNumericExpression (model : FlatModel) where
  private mk ::
  core : CheckedTemporalNumericCore model
  scope : List RepeatableLevel
  profile : ModelZone.ConcreteProfile
  admitted : core.admitted model scope = true

def elaborateTemporalNumericOperation (model : FlatModel) (declaringGroup : GroupPath)
    (surface : SurfaceTemporalNumericExpression) (targetGroup? : Option GroupPath := none) :
    Except TemporalNumericExpressionError (CheckedTemporalNumericExpression model) := do
  let scope := model.repeatableScopeForGroupPath (targetGroup?.getD declaringGroup)
  let core ← match surface with
    | .projection part surface => do
        match surface with
        | .dateLiteral _ _ | .timeLiteral _ | .dateTimeLiteral _ => throw .literalNotAllowed
        | _ => pure ()
        if !surface.admittedSourceSlot .ordinary then throw .sourceSlot
        let projected ← (elaborateScalarTemporalProjection model declaringGroup surface part targetGroup?).mapError .source
        match projected with
        | .numeric _ | .indexedPart _ _ _ => pure (.storedProjection projected)
        | .projection _ _ _ | .ordinary _ =>
            pure (.temporal (.projection part
              (← (elaborateScalarTemporalExpression model declaringGroup surface targetGroup?).mapError .source)))
    | .difference unit left right => do
        if !left.admittedSourceSlot .withPartialDate || !right.admittedSourceSlot .withPartialDate then throw .sourceSlot
        let first ← (elaborateScalarTemporalExpression model declaringGroup left targetGroup?).mapError .source
        let second ← (elaborateScalarTemporalExpression model declaringGroup right targetGroup?).mapError .source
        pure (.temporal (.difference unit first second))
  if h : core.admitted model scope = true then
    let some profile := ModelZone.ConcreteProfile.ofId? model.timeZoneId | throw .calendarUnavailable
    pure { core, scope, profile, admitted := h }
  else throw .componentNotExposed

def elaborateTemporalNumericExpression (model : FlatModel) (declaringGroup : GroupPath)
    (surface : SurfaceScalarTemporalExpression) (part : TemporalNumericPart)
    (targetGroup? : Option GroupPath := none) :
    Except TemporalNumericExpressionError (CheckedTemporalNumericExpression model) :=
  elaborateTemporalNumericOperation model declaringGroup (.projection part surface) targetGroup?

namespace CheckedTemporalNumericExpression

def fieldIds (expression : CheckedTemporalNumericExpression model) : List FieldId :=
  match expression.core with
  | .temporal operation => operation.sources.flatMap (·.fieldIds)
  | .storedProjection source => source.fieldIds

def storedTextFields (expression : CheckedTemporalNumericExpression model) : List FieldId :=
  match expression.core with
  | .temporal operation => operation.sources.flatMap (·.storedTextFields)
  | .storedProjection source => source.storedTextFields

def bindingScopes (expression : CheckedTemporalNumericExpression model) : List (List RepeatableLevel) :=
  match expression.core with
  | .temporal operation => operation.sources.flatMap (·.bindingScopes)
  | .storedProjection source => source.bindingScopes

def boundFieldIds (expression : CheckedTemporalNumericExpression model) : List FieldId :=
  match expression.core with
  | .temporal operation => operation.sources.flatMap (·.boundFieldIds)
  | .storedProjection source => source.boundFieldIds

def requiresAddressed (expression : CheckedTemporalNumericExpression model) : Bool :=
  match expression.core with
  | .temporal operation => operation.sources.any (·.requiresAddressed)
  | .storedProjection source => source.requiresAddressed

def hasHaving (expression : CheckedTemporalNumericExpression model) : Bool :=
  match expression.core with
  | .temporal operation => operation.sources.any (·.core.hasHaving)
  | .storedProjection source => source.hasHaving

def referencesWith (expression : CheckedTemporalNumericExpression model) (field : FieldId)
    (filterReads : CorrelatedHaving → Bool) : Bool :=
  match expression.core with
  | .temporal operation => operation.sources.any (·.referencesWith field filterReads)
  | .storedProjection source => source.referencesWith field filterReads

def referencesField (expression : CheckedTemporalNumericExpression model) (field : FieldId) : Bool :=
  expression.referencesWith field (·.referencesField field)

/-- Project the common temporal result while retaining its independent missingness and failure. -/
def evalResult (expression : CheckedTemporalNumericExpression model) (phase : Phase)
    (context : FlatContext) (addressed : Option ComputationFillContext := none) (row : Env := [])
    (partialRead? : Option (TemporalPartialReadContext model) := none) : Except ScalarTemporalEvaluationFault
      (Except NumericValidationUnavailable NumericArithmeticOutcome) := do
  let read (source : CheckedScalarTemporalExpression model) := source.evalResult phase context addressed row partialRead?
  match expression.core with
  | .storedProjection source => source.evalResult phase context addressed row partialRead?
  | .temporal (.projection part source) => part.observeScalar expression.profile (← read source)
  | .temporal (.difference unit left right) =>
      match ← readTemporalPair phase read scalarTemporalFormalCause? left right with
      | .error cause => pure (.error (.formal cause))
      | .ok (first, second) =>
          (observeScalarTemporalDifference expression.profile unit first second NumericValidationUnavailable.formal .nonRelevant)
            |>.mapError ScalarTemporalPrimitiveFault.toEvaluation

end CheckedTemporalNumericExpression
end A12Kernel
