import A12Kernel.Elaboration.CheckedDocument
import A12Kernel.Elaboration.ValueAsDate

/-! # Partial-Date and checked Time-field construction

This capsule supplies the second operand of `DateTime(ValueAsDate(...), time)` from one ordinary nonrepeatable complete-Time field in the same validated model. It preserves generated Date-before-Time evaluation: a formal Date failure prevents the Time read, while a cause-free non-relevant Date still reaches the Time read before the constructor decides non-relevance. The existing partial-Date constructor owns zone resolution and the reason-bearing Time operand shared with resolved `Time(...)` and the exact checked Time-literal decoder. Model-relative constructor-component lowering, extraction, temporal arithmetic, repeatable fields, and a general temporal-expression tree remain separate.
-/

namespace A12Kernel

private def completeTimeComponents : TemporalComponents := {
  year := false
  month := false
  day := false
  hour := true
  minute := true
  second := true
}

/-- Whether one resolved declaration is the exact ordinary full-Time field admitted by this capsule. -/
def FlatModel.admitsValueAsDateTimeField
    (model : FlatModel) (source : FlatTemporalField) : Bool :=
  match model.lookupUniqueId source.id with
  | .error _ => false
  | .ok declaration =>
      declaration.repeatableScope.isEmpty &&
        declaration.toTemporalField? == some source &&
        source.kind == .time &&
        source.components == completeTimeComponents

/-- Static refusal before a partial-Date constructor can own one checked Time-field read. -/
inductive ValueAsDateTimeFieldElabError where
  | construction (error : ValueAsDateTimeElabError)
  | timeSource (error : ResolveError)
  | timeSourceNotTemporal (field : FieldId)
  | timeSourceKind (field : FieldId) (actual : TemporalKind)
  | timeSourceComponents (field : FieldId) (actual : TemporalComponents)
  | incoherentCore
  deriving Repr, DecidableEq

/-- One checked partial-Date constructor plus its model-owned full-Time field. -/
structure CheckedValueAsDateTimeField (model : FlatModel) where
  construction : CheckedValueAsDateTime model
  timeSource : FlatTemporalField
  timeSourceAdmitted :
    model.admitsValueAsDateTimeField timeSource = true

/-- Structural failure outside the constructor's reason-bearing result domain. -/
inductive ValueAsDateTimeFieldFault where
  | document (error : CheckedDocumentError)
  | timePayloadMismatch (field : FieldId)
  deriving Repr, DecidableEq

namespace CheckedValueAsDateTimeField

/-- Observe the certified field at its scalar address and retain exact empty/formal/value distinctions. A wrong runtime payload is structural incoherence, not semantic emptiness. -/
def readTime (checked : CheckedValueAsDateTimeField model)
    (phase : Phase) (input : CheckedDocument model) :
    Except ValueAsDateTimeFieldFault (CellObservation TimeOfDay) := do
  let cell ← input.read {
    field := checked.timeSource.id
    path := []
  } |>.mapError .document
  match observeCell phase cell with
  | .empty => pure .empty
  | .unknown cause => pure (.unknown cause)
  | .poison cause => pure (.poison cause)
  | .value (.temporal (.time _ clock)) => pure (.value clock)
  | .value _ => throw (.timePayloadMismatch checked.timeSource.id)

/-- Check the bounded partial-Date source, then read the checked Time field only when generated left-to-right argument evaluation reaches it. -/
def evaluateRaw (checked : CheckedValueAsDateTimeField model)
    (phase : Phase) (input : CheckedDocument model)
    (raw : RawCell String) :
    Except ValueAsDateTimeFieldFault ValueAsDateTimeResult := do
  let dateCell :=
    checked.construction.toCheckedValueAsDateSource.checkSourceRaw raw
  match checked.construction.toCheckedValueAsDateSource.observe phase dateCell with
  | .unavailable cause => pure (.unavailable cause)
  | _ =>
      let time ← checked.readTime phase input
      pure (checked.construction.evaluate phase dateCell time)

end CheckedValueAsDateTimeField

/-- Resolve one partial-Date endpoint and one ordinary complete-Time field against the same validated model. -/
def elaborateValueAsDateTimeField
    (model : FlatModel) (dateField : FieldId)
    (endpoint : ValueAsDateEndpoint) (timeField : FieldId) :
    Except ValueAsDateTimeFieldElabError
      (CheckedValueAsDateTimeField model) := do
  let construction ←
    elaborateValueAsDateTime model dateField endpoint |>.mapError .construction
  let declaration ←
    model.resolveNonrepeatableDeclarationById timeField |>.mapError .timeSource
  let source ← match declaration.toTemporalField? with
    | some source => pure source
    | none => throw (.timeSourceNotTemporal timeField)
  if _hKind : source.kind = .time then
    if _hComponents : source.components = completeTimeComponents then
      if hAdmitted : model.admitsValueAsDateTimeField source = true then
        pure {
          construction := construction
          timeSource := source
          timeSourceAdmitted := hAdmitted
        }
      else
        throw .incoherentCore
    else
      throw (.timeSourceComponents source.id source.components)
  else
    throw (.timeSourceKind source.id source.kind)

end A12Kernel
