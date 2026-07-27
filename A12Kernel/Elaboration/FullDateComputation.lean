import A12Kernel.Elaboration.FullDateComputationApplication
import A12Kernel.Elaboration.TemporalTargetPolicy

/-! # Checked nonrepeatable full-Date computations

This capsule admits the field, `Today`, date-typed `BaseYear`, and selected Base-Year range forms of the existing `FlatTemporalOperand` against one full-Date target. Field evaluation reads once through `CheckedDocument`; `Today` resolves once from the execution's explicit `World` in the checked model zone; Base Year and its selected January 1/December 31 endpoints resolve model configuration through the same zone capability without reading the clock. Every path retains an exact instant and delegates rendering and basic checking to `CheckedFullDateTarget`. Alternatives, scheduling, DateTime, partial dates, wider expressions, message construction, and destination compatibility remain separate.
-/

namespace A12Kernel

/-- Static refusal before a bounded full-Date computation can execute. -/
inductive FullDateComputationElabError where
  | target (error : FullDateTargetElabError)
  | source (error : ResolveError)
  | sourceNotTemporal (source : FieldId)
  | sourceKind (source : FieldId) (actual : TemporalKind)
  | sourceComponents (source : FieldId) (actual : TemporalComponents)
  | targetSelfReference (field : FieldId)
  | baseYearNotDeclared
  | incoherentCore
  deriving Repr, DecidableEq

/-- Whether one resolved field is exactly an ordinary nonrepeatable full-Date source in this model. -/
def FlatModel.admitsFullDateComputationSource
    (model : FlatModel) (source : FlatTemporalField) : Bool :=
  match model.lookupUniqueId source.id with
  | .error _ => false
  | .ok declaration =>
      declaration.repeatableScope.isEmpty &&
        declaration.toTemporalField? == some source &&
        source.kind == .date &&
        source.components == TemporalComponents.fullDate

/-- Admit exactly an ordinary distinct full-Date field or `Today` in this model's zone. This is a refinement of the shared temporal operand, not another expression tree. -/
def FlatModel.admitsFullDateComputationOperand
    (model : FlatModel) (targetField : FieldId) :
    FlatTemporalOperand → Bool
  | .fieldValue source =>
      model.admitsFullDateComputationSource source &&
        source.id != targetField
  | .todayValue zoneId => zoneId == model.timeZoneId
  | .baseYearValue zoneId year =>
      zoneId == model.timeZoneId && model.baseYear == some year
  | .baseYearRangeValue zoneId year _ =>
      zoneId == model.timeZoneId && model.baseYear == some year
  | _ => false

/-- One model-certified field/`Today`/Base-Year computation. Direct and range-selected Base Year share the existing endpoint representation. -/
structure CheckedFullDateComputation (model : FlatModel) where
  operand : FlatTemporalOperand
  target : CheckedFullDateTarget model
  operandAdmitted :
    model.admitsFullDateComputationOperand
      target.checked.target.id operand = true

/-- Resolve one ordinary nonrepeatable full-Date field operand and one distinct target against the same validated model. -/
def elaborateFullDateFieldComputation
    (model : FlatModel) (sourceField targetField : FieldId) :
    Except FullDateComputationElabError
      (CheckedFullDateComputation model) := do
  let target ← elaborateFullDateTarget model targetField |>.mapError .target
  let declaration ←
    model.resolveNonrepeatableDeclarationById sourceField |>.mapError .source
  let source ← match declaration.toTemporalField? with
    | some source => pure source
    | none => throw (.sourceNotTemporal sourceField)
  if _hKind : source.kind = .date then
    if _hComponents : source.components = TemporalComponents.fullDate then
      if _hDistinct : source.id = target.checked.target.id then
        throw (.targetSelfReference targetField)
      else
        let operand := FlatTemporalOperand.fieldValue source
        if hOperand :
            model.admitsFullDateComputationOperand
              target.checked.target.id operand = true then
          pure {
            operand
            target
            operandAdmitted := hOperand }
        else
          throw .incoherentCore
    else
      throw (.sourceComponents source.id source.components)
  else
    throw (.sourceKind source.id source.kind)

/-- Build the dynamic `Today` operand from the checked model's exact zone id. No clock sample is retained in the operation. -/
def elaborateFullDateTodayComputation
    (model : FlatModel) (targetField : FieldId) :
    Except FullDateComputationElabError
      (CheckedFullDateComputation model) := do
  let target ← elaborateFullDateTarget model targetField |>.mapError .target
  let operand := FlatTemporalOperand.todayValue model.timeZoneId
  if hOperand :
      model.admitsFullDateComputationOperand
        target.checked.target.id operand = true then
    pure { operand, target, operandAdmitted := hOperand }
  else
    throw .incoherentCore

/-- Build date-typed `BaseYear` from the checked model's configured year and exact zone id. It is model configuration, not a clock sample or numeric coercion. -/
def elaborateFullDateBaseYearComputation
    (model : FlatModel) (targetField : FieldId) :
    Except FullDateComputationElabError
      (CheckedFullDateComputation model) := do
  let target ← elaborateFullDateTarget model targetField |>.mapError .target
  let year ← match model.baseYear with
    | some year => pure year
    | none => throw .baseYearNotDeclared
  let operand :=
    FlatTemporalOperand.baseYearValue model.timeZoneId year
  if hOperand :
      model.admitsFullDateComputationOperand
        target.checked.target.id operand = true then
    pure { operand, target, operandAdmitted := hOperand }
  else
    throw .incoherentCore

/-- Build one selected Base-Year range endpoint from the checked model's configured year and exact zone id. -/
def elaborateFullDateBaseYearRangeComputation
    (model : FlatModel) (targetField : FieldId)
    (endpoint : BaseYearRangeEndpoint) :
    Except FullDateComputationElabError
      (CheckedFullDateComputation model) := do
  let target ← elaborateFullDateTarget model targetField |>.mapError .target
  let year ← match model.baseYear with
    | some year => pure year
    | none => throw .baseYearNotDeclared
  let operand :=
    FlatTemporalOperand.baseYearRangeValue
      model.timeZoneId year endpoint
  if hOperand :
      model.admitsFullDateComputationOperand
        target.checked.target.id operand = true then
    pure { operand, target, operandAdmitted := hOperand }
  else
    throw .incoherentCore

/-- Structural failure outside the rich full-Date result domain. -/
inductive FullDateComputationFault where
  | document (error : CheckedDocumentError)
  | sourceValueKind (source : FieldId)
  | todayUnavailable (zoneId : String)
  | baseYearUnavailable (zoneId : String) (year : Int)
  | baseYearRangeUnavailable (zoneId : String) (year : Int)
      (endpoint : BaseYearRangeEndpoint)
  | unsupportedOperand
  | target (error : FullDateTargetEvaluationFault)
  deriving Repr, DecidableEq

namespace CheckedFullDateComputation

/-- Evaluate the admitted operand without ambient time. A field preserves computation-phase empty and poison; `Today` resolves from the supplied world at this call. -/
def evaluateOperand (operation : CheckedFullDateComputation model)
    (world : World)
    (input : CheckedDocument model) :
    Except FullDateComputationFault FullDateComputationResult :=
  match operation.operand with
  | .fieldValue source =>
      match input.read { field := source.id, path := [] } with
      | .error error => .error (.document error)
      | .ok cell =>
          match observeCell .computation cell with
          | .empty => pure .noValue
          | .poison cause | .unknown cause => pure (.poison cause)
          | .value (.temporal (.date instant _ _)) => pure (.value instant)
          | .value _ => throw (.sourceValueKind source.id)
  | .todayValue zoneId =>
      match world.today? zoneId with
      | some instant => pure (.value instant)
      | none => throw (.todayUnavailable zoneId)
  | .baseYearValue zoneId year =>
      match world.resolveLocal? zoneId year 1 1 0 0 0 with
      | some instant => pure (.value instant)
      | none => throw (.baseYearUnavailable zoneId year)
  | .baseYearRangeValue zoneId year endpoint =>
      let parts := baseYearRangeParts year endpoint
      match world.resolveLocal? zoneId
          parts.year parts.month parts.day 0 0 0 with
      | some instant => pure (.value instant)
      | none =>
          throw (.baseYearRangeUnavailable zoneId year endpoint)
  | _ => throw .unsupportedOperand

/-- Execute the checked operand through the existing declaration-owned target policy. -/
def evaluateOutcome (operation : CheckedFullDateComputation model)
    (world : World)
    (input : CheckedDocument model) :
    Except FullDateComputationFault FullDateTargetOutcome :=
  match operation.evaluateOperand world input with
  | .error error => .error error
  | .ok result => operation.target.evaluate result |>.mapError .target

/-- Execute and classify the one rich target outcome against the same immutable source document. Residual messages remain already-classified opaque input. -/
def executeResult (operation : CheckedFullDateComputation model)
    (world : World)
    (input : CheckedDocument model)
    (residualMessages : List ResidualMessage) :
    Except FullDateComputationFault
      (FullDateComputationRunView ResidualMessage) := do
  let outcome ← operation.evaluateOutcome world input
  pure (FullDateComputationRunView.fromOutcomes input residualMessages
    [(operation.target.checked.target.id, outcome)])

end CheckedFullDateComputation

end A12Kernel
