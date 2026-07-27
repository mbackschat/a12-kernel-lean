import A12Kernel.Elaboration.CheckedDocument
import A12Kernel.Elaboration.ValueAsDate

/-! # Partial-Date and checked `TimeFromDateTime`

This capsule supplies the second operand of `DateTime(ValueAsDate(...), time)` from `TimeFromDateTime` over one ordinary nonrepeatable complete-DateTime field in the same validated model. The generated extractor reads the source wall-clock components in the model zone and re-anchors them at 1970-01-01; the DateTime constructor observes only those components, so the existing decoded `TimeOfDay` is the exact semantic boundary.

Generated Date-before-Time evaluation remains explicit: a formal Date failure prevents the DateTime read, while cause-free Date non-relevance still reaches it. DateTime expressions, arithmetic descendants, repeatable fields, concrete parsing, and a general temporal-expression tree remain separate.
-/

namespace A12Kernel

/-- Whether one resolved declaration is the exact ordinary full-DateTime source admitted by this extraction capsule. -/
def FlatModel.admitsValueAsDateTimeExtractionSource
    (model : FlatModel) (source : FlatTemporalField) : Bool :=
  match model.lookupUniqueId source.id with
  | .error _ => false
  | .ok declaration =>
      declaration.repeatableScope.isEmpty &&
        declaration.toTemporalField? == some source &&
        source.kind == .dateTime &&
        source.components.isFullDateTime

/-- Static refusal before a partial-Date constructor can own one checked `TimeFromDateTime` read. -/
inductive ValueAsDateTimeExtractionElabError where
  | construction (error : ValueAsDateTimeElabError)
  | source (error : ResolveError)
  | sourceNotTemporal (field : FieldId)
  | sourceKind (field : FieldId) (actual : TemporalKind)
  | sourceComponents (field : FieldId) (actual : TemporalComponents)
  | incoherentCore
  deriving Repr, DecidableEq

/-- One checked partial-Date constructor plus its model-owned complete-DateTime extraction source. -/
structure CheckedValueAsDateTimeExtraction (model : FlatModel) where
  construction : CheckedValueAsDateTime model
  source : FlatTemporalField
  sourceAdmitted :
    model.admitsValueAsDateTimeExtractionSource source = true

/-- Structural failure outside the constructor's reason-bearing result domain. -/
inductive ValueAsDateTimeExtractionFault where
  | document (error : CheckedDocumentError)
  | sourcePayloadMismatch (field : FieldId)
  deriving Repr, DecidableEq

namespace ValueAsDateTimeTimeOperand

/-- Project one phase-classified complete-DateTime value to the extractor's wall-clock result. `none` identifies a forged payload whose runtime kind contradicts the checked source declaration. -/
def ofDateTimeValueObservation :
    CellObservation Value → Option ValueAsDateTimeTimeOperand
  | .empty => some (.noValue true)
  | .unknown cause | .poison cause => some (.unavailable cause)
  | .value (.temporal (.dateTime _ _ clock _)) => some (.value clock)
  | .value _ => none

end ValueAsDateTimeTimeOperand

namespace CheckedValueAsDateTimeExtraction

/-- Read the certified scalar DateTime source once and retain its wall clock, empty state, or exact formal cause. The reference semantics uses a linear immutable document lookup and adds no second zone conversion. -/
def readTime (checked : CheckedValueAsDateTimeExtraction model)
    (phase : Phase) (input : CheckedDocument model) :
    Except ValueAsDateTimeExtractionFault ValueAsDateTimeTimeOperand := do
  let cell ← input.read {
    field := checked.source.id
    path := []
  } |>.mapError .document
  match ValueAsDateTimeTimeOperand.ofDateTimeValueObservation
      (observeCell phase cell) with
  | some time => pure time
  | none => throw (.sourcePayloadMismatch checked.source.id)

/-- Check the bounded partial-Date source, then evaluate `TimeFromDateTime` only when generated left-to-right argument evaluation reaches it. -/
def evaluateRaw (checked : CheckedValueAsDateTimeExtraction model)
    (phase : Phase) (input : CheckedDocument model)
    (raw : RawCell String) :
    Except ValueAsDateTimeExtractionFault ValueAsDateTimeResult :=
  checked.construction.evaluateTimeOperandRaw phase raw fun _ =>
    checked.readTime phase input

end CheckedValueAsDateTimeExtraction

/-- Resolve one partial-Date endpoint and one ordinary complete-DateTime extraction source against the same validated model. -/
def elaborateValueAsDateTimeExtraction
    (model : FlatModel) (dateField : FieldId)
    (endpoint : ValueAsDateEndpoint) (dateTimeField : FieldId) :
    Except ValueAsDateTimeExtractionElabError
      (CheckedValueAsDateTimeExtraction model) := do
  let construction ←
    elaborateValueAsDateTime model dateField endpoint |>.mapError .construction
  let declaration ←
    model.resolveNonrepeatableDeclarationById dateTimeField |>.mapError .source
  let source ← match declaration.toTemporalField? with
    | some source => pure source
    | none => throw (.sourceNotTemporal dateTimeField)
  if _hKind : source.kind = .dateTime then
    if _hComponents : source.components.isFullDateTime = true then
      if hAdmitted :
          model.admitsValueAsDateTimeExtractionSource source = true then
        pure {
          construction
          source
          sourceAdmitted := hAdmitted
        }
      else
        throw .incoherentCore
    else
      throw (.sourceComponents source.id source.components)
  else
    throw (.sourceKind source.id source.kind)

end A12Kernel
