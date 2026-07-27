import A12Kernel.Elaboration.CheckedDocument
import A12Kernel.Elaboration.ValueAsDate

/-! # Partial-Date and checked `TimeFromDateTime`

This capsule supplies the second operand of `DateTime(ValueAsDate(...), time)` from `TimeFromDateTime` over one ordinary nonrepeatable complete-DateTime field in the same validated model, either directly or after one `AddHours`, `AddMinutes`, or `AddSeconds` with an authored numeric literal or ordinary Number field. The shifted source may instead be the execution's explicit `World.now` with either amount form. A sub-day addition shifts the retained exact instant; the generated extractor then reads the shifted wall-clock components in the model zone and re-anchors them at 1970-01-01. The outer DateTime constructor observes only those components, so the existing decoded `TimeOfDay` remains the exact semantic boundary.

Generated Date-before-Time evaluation remains explicit: a formal Date failure prevents the DateTime read, while cause-free Date non-relevance still reaches it. Within the nested shift, the DateTime source is evaluated before the amount. A direct Number field retains the helper's directional missing provenance: an empty amount supplies zero, so the shifted value remains concrete but omission-typed. Wider DateTime and amount expressions, repeatable fields, concrete parsing, and a general temporal-expression tree remain separate.
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

/-- Whether one resolved declaration is the exact ordinary Number source admitted as a shift amount. -/
def FlatModel.admitsValueAsDateTimeShiftAmount
    (model : FlatModel) (source : FlatNumberField) : Bool :=
  match model.lookupUniqueId source.id with
  | .error _ => false
  | .ok declaration =>
      declaration.repeatableScope.isEmpty &&
        declaration.toNumberField? == some source

/-- Static refusal before a partial-Date constructor can own one checked `TimeFromDateTime` read. -/
inductive ValueAsDateTimeExtractionElabError where
  | construction (error : ValueAsDateTimeElabError)
  | source (error : ResolveError)
  | sourceNotTemporal (field : FieldId)
  | sourceKind (field : FieldId) (actual : TemporalKind)
  | sourceComponents (field : FieldId) (actual : TemporalComponents)
  | amount (error : ResolveError)
  | amountNotNumber (field : FieldId)
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
  | shiftedInstantOutsideProfile (instant : Instant)
  deriving Repr, DecidableEq

namespace ValueAsDateTimeTimeOperand

/-- Project one phase-classified complete-DateTime value to the extractor's wall-clock result. `none` identifies a forged payload whose runtime kind contradicts the checked source declaration. -/
def ofDateTimeValueObservation :
    CellObservation Value → Option ValueAsDateTimeTimeOperand
  | .empty => some (.noValue true)
  | .unknown cause | .poison cause => some (.unavailable cause)
  | .value (.temporal (.dateTime _ _ clock _)) => some (.value clock false)
  | .value _ => none

/-- Shift one exact DateTime instant by the authored literal's Java-compatible integer amount, then project its model-zone whole-second clock. `none` is bounded profile failure, not a semantic no-value. -/
def ofShiftedInstant? (profile : ModelZone.ConcreteProfile)
    (unit : DateTimeSubdayUnit) (amount : Rat) (instant : Instant) :
    Option ValueAsDateTimeTimeOperand :=
  (profile.localDateTime?
    (instant.shift unit (ValueAsDateShiftUnit.amountToInt32 amount))).map
      (fun shifted => .value shifted.time false)

/-- Shift one exact instant through a checked numeric operand. Directional fillability is the runtime helper's own not-given test, so an empty Number field retains a concrete zero-shift value with omission provenance. -/
def ofShiftedNumericOperand? (profile : ModelZone.ConcreteProfile)
    (unit : DateTimeSubdayUnit) (instant : Instant) :
    NumericOperand → Option ValueAsDateTimeTimeOperand
  | .unknown cause => some (.unavailable cause)
  | .value amount fillability =>
      (profile.localDateTime?
        (instant.shift unit (ValueAsDateShiftUnit.amountToInt32 amount))).map
          (fun shifted =>
            .value shifted.time
              (fillability.canGrow || fillability.canShrink))

end ValueAsDateTimeTimeOperand

/-- One statically checked sub-day shift amount. Literals are fixed; an ordinary Number field retains empty and formal observations without introducing a wider numeric-expression carrier. -/
inductive CheckedValueAsDateTimeShiftAmount (model : FlatModel) where
  | literal (amount : Rat)
  | field (source : FlatNumberField)
      (sourceAdmitted :
        model.admitsValueAsDateTimeShiftAmount source = true)

namespace CheckedValueAsDateTimeShiftAmount

/-- Evaluate a checked amount after the DateTime source has been reached. Structural document failure remains outside numeric missingness and formal causes. -/
def read (amount : CheckedValueAsDateTimeShiftAmount model)
    (phase : Phase) (input : CheckedDocument model) :
    Except ValueAsDateTimeExtractionFault NumericOperand :=
  match amount with
  | .literal value => pure (.value value .fixed)
  | .field source _ => do
      let cell ← input.read {
        field := source.id
        path := []
      } |>.mapError .document
      pure ((observeCell phase cell).asDirectNumericComparisonOperand source.info)

end CheckedValueAsDateTimeShiftAmount

/-- Resolve one ordinary nonrepeatable Number shift amount against the validated model. Both field- and `Now`-sourced shifts reuse this exact admission boundary. -/
def elaborateValueAsDateTimeFieldShiftAmount
    (model : FlatModel) (amountField : FieldId) :
    Except ValueAsDateTimeExtractionElabError
      (CheckedValueAsDateTimeShiftAmount model) := do
  let declaration ←
    model.resolveNonrepeatableDeclarationById amountField |>.mapError .amount
  let source ← match declaration.toNumberField? with
    | some source => pure source
    | none => throw (.amountNotNumber amountField)
  if hAdmitted :
      model.admitsValueAsDateTimeShiftAmount source = true then
    pure (.field source hAdmitted)
  else
    throw .incoherentCore

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

/-- One checked complete-DateTime source shifted by a checked literal or ordinary Number field before its Time projection. The shared base owns source admission and outer Date-before-Time order. -/
structure CheckedValueAsDateTimeShiftExtraction (model : FlatModel)
    extends CheckedValueAsDateTimeExtraction model where
  unit : DateTimeSubdayUnit
  amount : CheckedValueAsDateTimeShiftAmount model

namespace CheckedValueAsDateTimeShiftExtraction

/-- Read the certified source before the amount, apply Java-compatible signed-32-bit conversion, then decode the shifted exact instant under the model-owned profile. A formal source stops before the amount; an empty source still reaches it. -/
def readShiftedTime (checked : CheckedValueAsDateTimeShiftExtraction model)
    (phase : Phase) (input : CheckedDocument model) :
    Except ValueAsDateTimeExtractionFault ValueAsDateTimeTimeOperand := do
  let cell ← input.read {
    field := checked.source.id
    path := []
  } |>.mapError .document
  match observeCell phase cell with
  | .empty =>
      match ← checked.amount.read phase input with
      | .unknown cause => pure (.unavailable cause)
      | .value _ _ => pure (.noValue true)
  | .unknown cause | .poison cause => pure (.unavailable cause)
  | .value (.temporal (.dateTime instant _ _ _)) =>
      match ← checked.amount.read phase input with
      | .unknown cause => pure (.unavailable cause)
      | .value value fillability =>
          let shifted := instant.shift checked.unit
            (ValueAsDateShiftUnit.amountToInt32 value)
          match ValueAsDateTimeTimeOperand.ofShiftedNumericOperand?
              checked.construction.profile checked.unit instant
                (.value value fillability) with
          | some time => pure time
          | none => throw (.shiftedInstantOutsideProfile shifted)
  | .value _ => throw (.sourcePayloadMismatch checked.source.id)

/-- Check the bounded partial-Date source, then evaluate the shifted DateTime extraction only when generated left-to-right argument evaluation reaches it. -/
def evaluateRaw (checked : CheckedValueAsDateTimeShiftExtraction model)
    (phase : Phase) (input : CheckedDocument model)
    (raw : RawCell String) :
    Except ValueAsDateTimeExtractionFault ValueAsDateTimeResult :=
  checked.construction.evaluateTimeOperandRaw phase raw fun _ =>
    checked.readShiftedTime phase input

end CheckedValueAsDateTimeShiftExtraction

/-- One checked partial-Date constructor whose Time side shifts dynamic `Now` by a checked literal or ordinary Number field before extraction. The world remains an execution input and no instant is sampled during elaboration. -/
structure CheckedValueAsDateTimeNowShiftExtraction (model : FlatModel) where
  construction : CheckedValueAsDateTime model
  unit : DateTimeSubdayUnit
  amount : CheckedValueAsDateTimeShiftAmount model

namespace CheckedValueAsDateTimeNowShiftExtraction

/-- Read the checked amount after sampling this execution's exact `World.now`, then project the shifted model-zone clock. -/
def readShiftedTime (checked : CheckedValueAsDateTimeNowShiftExtraction model)
    (phase : Phase) (world : World) (input : CheckedDocument model) :
    Except ValueAsDateTimeExtractionFault ValueAsDateTimeTimeOperand := do
  match ← checked.amount.read phase input with
  | .unknown cause => pure (.unavailable cause)
  | .value value fillability =>
      let shifted := world.now.shift checked.unit
        (ValueAsDateShiftUnit.amountToInt32 value)
      match ValueAsDateTimeTimeOperand.ofShiftedNumericOperand?
          checked.construction.profile checked.unit world.now
            (.value value fillability) with
      | some time => pure time
      | none => throw (.shiftedInstantOutsideProfile shifted)

/-- Check the bounded partial-Date source before the world-dependent Time operand, preserving generated Date-before-Time evaluation. -/
def evaluateRaw (checked : CheckedValueAsDateTimeNowShiftExtraction model)
    (phase : Phase) (world : World) (input : CheckedDocument model)
    (raw : RawCell String) :
    Except ValueAsDateTimeExtractionFault ValueAsDateTimeResult :=
  checked.construction.evaluateTimeOperandRaw phase raw fun _ =>
    checked.readShiftedTime phase world input

end CheckedValueAsDateTimeNowShiftExtraction

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

/-- Resolve one checked direct extraction, then retain one source-closed sub-day unit and authored numeric literal for exact-instant shifting. -/
def elaborateValueAsDateTimeShiftExtraction
    (model : FlatModel) (dateField : FieldId)
    (endpoint : ValueAsDateEndpoint) (dateTimeField : FieldId)
    (unit : DateTimeSubdayUnit) (amount : Rat) :
    Except ValueAsDateTimeExtractionElabError
      (CheckedValueAsDateTimeShiftExtraction model) := do
  let extraction ←
    elaborateValueAsDateTimeExtraction model dateField endpoint dateTimeField
  pure { extraction with unit, amount := .literal amount }

/-- Resolve one checked direct extraction and one ordinary nonrepeatable Number amount against the same validated model. -/
def elaborateValueAsDateTimeFieldShiftExtraction
    (model : FlatModel) (dateField : FieldId)
    (endpoint : ValueAsDateEndpoint) (dateTimeField : FieldId)
    (unit : DateTimeSubdayUnit) (amountField : FieldId) :
    Except ValueAsDateTimeExtractionElabError
      (CheckedValueAsDateTimeShiftExtraction model) := do
  let extraction ←
    elaborateValueAsDateTimeExtraction model dateField endpoint dateTimeField
  let amount ← elaborateValueAsDateTimeFieldShiftAmount model amountField
  pure { extraction with unit, amount }

/-- Resolve the partial-Date side without sampling `Now`, then retain the selected sub-day unit and authored numeric literal for execution. -/
def elaborateValueAsDateTimeNowShiftExtraction
    (model : FlatModel) (dateField : FieldId)
    (endpoint : ValueAsDateEndpoint)
    (unit : DateTimeSubdayUnit) (amount : Rat) :
    Except ValueAsDateTimeExtractionElabError
      (CheckedValueAsDateTimeNowShiftExtraction model) := do
  let construction ←
    elaborateValueAsDateTime model dateField endpoint |>.mapError .construction
  pure { construction, unit, amount := .literal amount }

/-- Resolve the partial-Date side and one ordinary nonrepeatable Number amount without sampling `Now`. -/
def elaborateValueAsDateTimeNowFieldShiftExtraction
    (model : FlatModel) (dateField : FieldId)
    (endpoint : ValueAsDateEndpoint)
    (unit : DateTimeSubdayUnit) (amountField : FieldId) :
    Except ValueAsDateTimeExtractionElabError
      (CheckedValueAsDateTimeNowShiftExtraction model) := do
  let construction ←
    elaborateValueAsDateTime model dateField endpoint |>.mapError .construction
  let amount ← elaborateValueAsDateTimeFieldShiftAmount model amountField
  pure { construction, unit, amount }

end A12Kernel
