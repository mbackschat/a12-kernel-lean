import A12Kernel.Semantics.TemporalExpression
import A12Kernel.Elaboration.TemporalExtremumStream
import A12Kernel.Elaboration.Flat.FieldValueRead

/-! # Checked scalar temporal expressions in comparisons

The initial source vocabulary is direct stored fields and field-list extrema. Both sides retain
one expression tree and use the shared fold. Row sets, world operands, constructors and shifts
remain outside this scalar admission boundary.
-/

namespace A12Kernel

inductive SurfaceScalarTemporalExpression where
  | field (reference : SurfaceFieldPath)
  | extremum (operator : TemporalExtremumOp) (source : SurfaceFieldEntitySource)

inductive ScalarTemporalExpressionError where
  | model (error : ResolveError)
  | read (error : ResolveError)
  | extremum (error : TemporalExtremumOperandElabError)
  | nonTemporal (path : List String)
  | unsupportedSource
  | incompatibleFormats
  deriving Repr

inductive ScalarTemporalDomain where
  | date
  | yearless
  | time
  | instant
  deriving Repr, DecidableEq

/-- The constructor is sealed: domain selection and every source's declaration are checked together. -/
structure CheckedScalarTemporalComparison (model : FlatModel) where
  private mk ::
  left : TemporalExpressionOf FlatTemporalField
  right : TemporalExpressionOf FlatTemporalField
  operator : TemporalComparisonOp
  domain : ScalarTemporalDomain
  modelWellFormed : model.validate.isOk = true

private def resolveScalarTemporalExpression (model : FlatModel) (rowGroup : GroupPath) :
    SurfaceScalarTemporalExpression → Except ScalarTemporalExpressionError
      (TemporalExpressionOf FlatTemporalField × TemporalComponents)
  | .field reference => do
      let declaration ← (model.resolveFieldValueRead rowGroup reference).mapError .read
      let some field := declaration.toTemporalField? | throw (.nonTemporal declaration.path)
      if declaration.toTemporalTargetPolicy?.any (·.partialMode != .full) then
        throw .unsupportedSource
      pure (.atom field, field.components.withBaseYear model.hasBaseYear)
  | .extremum operator operands => do
      let source ← (TemporalExtremumOperands.elaborate model rowGroup operands).mapError .extremum
      let fields ← source.shape.operands.mapM fun
        | .field declaration _ => do
            if !declaration.repeatableScope.isEmpty then throw .unsupportedSource
            let some field := declaration.toTemporalField? | throw (.nonTemporal declaration.path)
            pure (TemporalExpressionOf.atom field)
        | _ => throw .unsupportedSource
      let first :: rest := fields | throw .unsupportedSource
      pure (.extremum operator first rest, source.components)

/-- Ordinary comparison admission is reused; mixed date/instant ordering awaits a shared projection. -/
def elaborateScalarTemporalComparison (model : FlatModel) (rowGroup : GroupPath)
    (operator : TemporalComparisonOp) (left right : SurfaceScalarTemporalExpression) :
    Except ScalarTemporalExpressionError (CheckedScalarTemporalComparison model) := do
  match h : model.validate with
  | .error error => throw (.model error)
  | .ok () =>
      let (left, leftComponents) ← resolveScalarTemporalExpression model rowGroup left
      let (right, rightComponents) ← resolveScalarTemporalExpression model rowGroup right
      if !operator.admitsFormats model.hasBaseYear leftComponents rightComponents then
        throw .incompatibleFormats
      if leftComponents.hasTime != rightComponents.hasTime then throw .unsupportedSource
      let domain ←
        if leftComponents.hasTime then
          if leftComponents == TemporalComponents.now && rightComponents == TemporalComponents.now then
            pure ScalarTemporalDomain.instant
          else if leftComponents == TemporalComponents.time && rightComponents == TemporalComponents.time then
            pure ScalarTemporalDomain.time
          else throw .unsupportedSource
        else pure (if leftComponents.year then ScalarTemporalDomain.date else ScalarTemporalDomain.yearless)
      pure { left, right, operator, domain, modelWellFormed := by rw [h]; rfl }

namespace CheckedScalarTemporalComparison

def fields (comparison : CheckedScalarTemporalComparison model) : List FlatTemporalField :=
  comparison.left.atoms ++ comparison.right.atoms

def referencesField (comparison : CheckedScalarTemporalComparison model) (field : FieldId) : Bool :=
  comparison.fields.any (·.id == field)

/-- Each profile uses the existing temporal projection and ordering, never stored text or an invented year. -/
def eval (comparison : CheckedScalarTemporalComparison model) (context : FlatContext) : Verdict :=
  let compareWith {α : Type} (select : TemporalExtremumOp → α → α → α)
      (holds : α → α → Bool) (project : FlatTemporalField → CellObservation → SimpleComparisonOperand α) :=
    evalSymmetricComparison holds
      (comparison.left.evalWith select fun field => project field (context.observeValidationAt field.id))
      (comparison.right.evalWith select fun field => project field (context.observeValidationAt field.id))
  match comparison.domain with
  | .date => compareWith TemporalExtremumOp.select comparison.operator.holds
      (fun field => CellObservation.asMaskedDateExtremumOperand field.components model.baseYear)
  | .yearless => compareWith TemporalExtremumOp.selectMonthDay comparison.operator.holdsMonthDay
      (fun field => CellObservation.asYearlessDateExtremumOperand field.components)
  | .time => compareWith TemporalExtremumOp.selectTime comparison.operator.holdsTime
      (fun _ => CellObservation.asTimeExtremumOperand)
  | .instant => compareWith TemporalExtremumOp.selectInstant comparison.operator.holdsInstant
      (fun _ => CellObservation.asDateTimeExtremumOperand)

end CheckedScalarTemporalComparison

end A12Kernel
