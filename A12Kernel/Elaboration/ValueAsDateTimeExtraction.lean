import A12Kernel.Elaboration.ValueAsDate
import A12Kernel.Elaboration.DateFromDateTime

/-! # Partial-Date and checked `TimeFromDateTime`

This capsule supplies the second operand of `DateTime(ValueAsDate(...), time)` from `TimeFromDateTime` over one ordinary nonrepeatable complete-DateTime field in the same validated model, either directly or after one `AddHours`, `AddMinutes`, or `AddSeconds` with an authored numeric literal, ordinary Number field, or checked same-group arithmetic expression over ordinary Number fields. The shifted source may instead be the execution's explicit `World.now` with any amount form, and either exact shifted source may feed one further checked sub-day shift. A sub-day addition retains the whole shifted exact instant and model-zone label; the generated extractor is a proved projection that reads only the shifted wall-clock components and re-anchors them at 1970-01-01. The outer DateTime constructor observes only those components, while whole-DateTime computation consumers retain the exact instant.

Generated Date-before-Time evaluation remains explicit: a formal Date failure prevents the DateTime read, while cause-free Date non-relevance still reaches it. Within the nested shift, the DateTime source is evaluated before the amount. Numeric expressions reuse the existing one-pass lowering and arithmetic-fillability result: an empty amount can still supply a concrete omission-typed value, while domain-invalid arithmetic yields no DateTime value. Wider DateTime sources, non-Number numeric atoms, repeatable fields, concrete parsing, and a general temporal-expression tree remain separate.

The complete-DateTime/profile/Number certificate is also the exact static source reused by the calendar-day shift owner; elapsed sub-day evaluation and calendar-day mutation remain separate consumers.
-/

namespace A12Kernel

/-- Whether one resolved declaration is the ordinary full-DateTime source this extraction admits. It is
the **same** requirement `DateFromDateTime` imposes, which is measured rather than assumed: the Kernel
wants a complete DateTime for both component extractors and refuses every other source at the operator.
[`DateFromDateTime.lean`](DateFromDateTime.lean) owns it; this name is retained for the existing
certificate. -/
def FlatModel.admitsValueAsDateTimeExtractionSource
    (model : FlatModel) (source : FlatTemporalField) : Bool :=
  model.admitsCompleteDateTimeSource source

/-- Static refusal before a partial-Date constructor can own one checked `TimeFromDateTime` read. -/
inductive ValueAsDateTimeExtractionElabError where
  | construction (error : ValueAsDateTimeElabError)
  | source (error : ResolveError)
  | sourceNotTemporal (field : FieldId)
  | sourceKind (field : FieldId) (actual : TemporalKind)
  | sourceComponents (field : FieldId) (actual : TemporalComponents)
  | amount (error : ResolveError)
  | amountNotNumber (field : FieldId)
  | amountExpression (error : NumericValidationElabError)
  | amountExpressionNotDirectNumber
  | unsupportedZone (zoneId : String)
  | incoherentCore
  deriving Repr, DecidableEq

namespace ValueAsDateTimeExtractionElabError

/-- Preserve the established DateTime-specific error surface while delegating amount certification to its shared owner. -/
def ofTemporalShiftAmount : TemporalShiftAmountElabError →
    ValueAsDateTimeExtractionElabError
  | .field error => .amount error
  | .fieldNotNumber field => .amountNotNumber field
  | .expression error => .amountExpression error
  | .expressionNotDirectNumber => .amountExpressionNotDirectNumber
  | .incoherentCore => .incoherentCore

end ValueAsDateTimeExtractionElabError

/-- One checked partial-Date constructor plus its model-owned complete-DateTime extraction source. -/
structure CheckedValueAsDateTimeExtraction (model : FlatModel) where
  construction : CheckedValueAsDateTime model
  source : FlatTemporalField
  sourceAdmitted :
    model.admitsValueAsDateTimeExtractionSource source = true

/-- Structural failure outside the constructor's reason-bearing result domain. A non-formal numeric unavailability is unreachable through the direct-Number expression certificate and remains explicit if that invariant is ever violated. -/
inductive ValueAsDateTimeExtractionFault where
  | document (error : CheckedDocumentError)
  | amountExpressionUnavailable (error : NumericValidationUnavailable)
  | sourcePayloadMismatch (field : FieldId)
  | shiftedInstantOutsideProfile (instant : Instant)
  deriving Repr, DecidableEq

namespace ValueAsDateTimeResult

/-- Forget only the whole DateTime value after exact-instant shifting, for consumers
    whose authored operation explicitly extracts the wall clock. -/
def asTimeOperand : ValueAsDateTimeResult → ValueAsDateTimeTimeOperand
  | .noValue notGiven => .noValue notGiven
  | .value localDateTime _ notGiven => .value localDateTime.time notGiven
  | .nonRelevant => .nonRelevant
  | .unavailable cause => .unavailable cause

/-- Shift one exact instant through a checked numeric operand while retaining its whole
    model-zone DateTime label, exact instant, and omission provenance. -/
def ofShiftedNumericOperand? (profile : ModelZone.ConcreteProfile)
    (unit : DateTimeSubdayUnit) (instant : Instant) :
    NumericOperand → Option ValueAsDateTimeResult
  | .unknown cause => some (.unavailable cause)
  | .value amount fillability =>
      let shiftedInstant :=
        instant.shift unit (temporalShiftAmountToInt32 amount)
      (profile.localDateTime? shiftedInstant).map fun shifted =>
        .value shifted shiftedInstant
          (fillability.canGrow || fillability.canShrink)

/-- Interpret one already-resolved numeric shift amount without coupling exact-instant arithmetic to scalar or addressed field resolution. -/
def ofShiftedArithmetic (profile : ModelZone.ConcreteProfile)
    (unit : DateTimeSubdayUnit) (instant : Instant) :
    Except NumericValidationUnavailable NumericArithmeticOutcome →
      Except ValueAsDateTimeExtractionFault ValueAsDateTimeResult
  | .error (.formal cause) => pure (.unavailable cause)
  | .error cause => throw (.amountExpressionUnavailable cause)
  | .ok .notEvaluated => pure (.noValue false)
  | .ok (NumericArithmeticOutcome.value amount fillability) =>
      let shifted := instant.shift unit (temporalShiftAmountToInt32 amount)
      match ofShiftedNumericOperand? profile unit instant
          (.value amount fillability) with
      | some result => pure result
      | none => throw (.shiftedInstantOutsideProfile shifted)

/-- Evaluate a phase-classified complete-DateTime source before its amount through one caller-selected scalar or addressed read channel. The thunk preserves the source-before-amount short circuit across both placements. -/
def evaluateShiftedDateTimeObservation
    (profile : ModelZone.ConcreteProfile) (unit : DateTimeSubdayUnit)
    (sourceField : FieldId) (observation : CellObservation Value)
    (readAmount : Unit → Except Fault
      (Except NumericValidationUnavailable NumericArithmeticOutcome))
    (mapFault : ValueAsDateTimeExtractionFault → Fault) :
    Except Fault ValueAsDateTimeResult :=
  match observation with
  | .empty =>
      match readAmount () with
      | .error error => .error error
      | .ok (.error (.formal cause)) => .ok (.unavailable cause)
      | .ok (.error reason) => .error (mapFault (.amountExpressionUnavailable reason))
      | .ok (.ok _) => .ok (.noValue true)
  | .unknown cause | .poison cause => .ok (.unavailable cause)
  | .value (.temporal (.dateTime instant _ _ _)) =>
      match readAmount () with
      | .error error => .error error
      | .ok resolved =>
          (ofShiftedArithmetic profile unit instant resolved).mapError mapFault
  | .value _ => .error (mapFault (.sourcePayloadMismatch sourceField))

end ValueAsDateTimeResult

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
    (instant.shift unit (temporalShiftAmountToInt32 amount))).map
      (fun shifted => .value shifted.time false)

/-- Shift one exact instant through a checked numeric operand. Directional fillability is the runtime helper's own not-given test, so an empty Number field retains a concrete zero-shift value with omission provenance. -/
def ofShiftedNumericOperand? (profile : ModelZone.ConcreteProfile)
    (unit : DateTimeSubdayUnit) (instant : Instant) :
    NumericOperand → Option ValueAsDateTimeTimeOperand
  | operand =>
      (ValueAsDateTimeResult.ofShiftedNumericOperand?
        profile unit instant operand).map (·.asTimeOperand)

end ValueAsDateTimeTimeOperand

/-- Read and apply a checked amount without collapsing arithmetic domain failure to zero. -/
def CheckedTemporalShiftAmount.readShiftedDateTime
    (amount : CheckedTemporalShiftAmount model)
    (phase : Phase) (input : CheckedDocument model)
    (profile : ModelZone.ConcreteProfile)
    (unit : DateTimeSubdayUnit) (instant : Instant) :
    Except ValueAsDateTimeExtractionFault ValueAsDateTimeResult := do
  let resolved ← amount.read phase input |>.mapError .document
  ValueAsDateTimeResult.ofShiftedArithmetic profile unit instant resolved

/-- Specialize exact DateTime shifting to the authored wall-clock extraction result. -/
def CheckedTemporalShiftAmount.readShiftedTime
    (amount : CheckedTemporalShiftAmount model)
    (phase : Phase) (input : CheckedDocument model)
    (profile : ModelZone.ConcreteProfile)
    (unit : DateTimeSubdayUnit) (instant : Instant) :
    Except ValueAsDateTimeExtractionFault ValueAsDateTimeTimeOperand :=
  amount.readShiftedDateTime phase input profile unit instant
    |>.map (·.asTimeOperand)

/-- Resolve one ordinary nonrepeatable Number shift amount against the validated model. Both field- and `Now`-sourced shifts reuse this exact admission boundary. -/
def elaborateValueAsDateTimeFieldShiftAmount
    (model : FlatModel) (amountField : FieldId) :
    Except ValueAsDateTimeExtractionElabError
      (CheckedTemporalShiftAmount model) :=
  elaborateTemporalFieldShiftAmount model amountField
    |>.mapError ValueAsDateTimeExtractionElabError.ofTemporalShiftAmount

/-- Resolve one checked same-group numeric operation and retain only the direct Number-field atom subset audited for temporal shifting. -/
def elaborateValueAsDateTimeExpressionShiftAmount
    (model : FlatModel) (rowGroup : GroupPath)
    (surface : AuthoredNumericExpr SurfaceNumericAtom) :
    Except ValueAsDateTimeExtractionElabError
      (CheckedTemporalShiftAmount model) :=
  elaborateTemporalExpressionShiftAmount model rowGroup surface
    |>.mapError ValueAsDateTimeExtractionElabError.ofTemporalShiftAmount

/-- Resolve a numeric shift expression at a repeatable authoring group while retaining the direct-Number-only temporal operand certificate. -/
def elaborateValueAsDateTimeRepeatableExpressionShiftAmount
    (model : FlatModel) (rowGroup : GroupPath)
    (surface : AuthoredNumericExpr SurfaceNumericAtom) :
    Except ValueAsDateTimeExtractionElabError
      (CheckedTemporalShiftAmount model) :=
  elaborateRepeatableTemporalExpressionShiftAmount model rowGroup surface
    |>.mapError ValueAsDateTimeExtractionElabError.ofTemporalShiftAmount

/-- One checked complete-DateTime field and its exact model-zone profile. -/
structure CheckedDateTimeSource (model : FlatModel) where
  source : FlatTemporalField
  sourceAdmitted :
    model.admitsValueAsDateTimeExtractionSource source = true
  profile : ModelZone.ConcreteProfile
  profileMatches :
    ModelZone.ConcreteProfile.ofId? model.timeZoneId = some profile

/-- The checked DateTime source plus one numeric amount shared by elapsed sub-day and
    calendar-day shift consumers. -/
structure CheckedDateTimeNumericShiftSource (model : FlatModel)
    extends CheckedDateTimeSource model where
  amount : CheckedTemporalShiftAmount model

/-- One shared checked DateTime shift source specialized to elapsed sub-day arithmetic. -/
structure CheckedShiftedDateTimeSource (model : FlatModel)
    extends CheckedDateTimeNumericShiftSource model where
  unit : DateTimeSubdayUnit

namespace ValueAsDateTimeResult

/-- Project one generated DateTime expression result into target execution. Quiet
    no-value and cause-free non-relevance store nothing; a reached formal cause remains
    poison; a value carries only its exact instant into declaration-owned rendering. -/
def asTemporalComputationResult :
    ValueAsDateTimeResult → TemporalComputationResult
  | .noValue _ | .nonRelevant => .noValue
  | .value _ instant _ => .value instant
  | .unavailable cause => .poison cause

/-- Omission carried by a value-producing or value-less DateTime shift. -/
def shiftNotGiven : ValueAsDateTimeResult → Bool
  | .noValue notGiven | .value _ _ notGiven => notGiven
  | .nonRelevant | .unavailable _ => false

/-- Add inherited omission provenance to a composed DateTime result without changing
    exact value, non-relevance, or formal cause identity. -/
def inheritNotGiven (result : ValueAsDateTimeResult)
    (inherited : Bool) : ValueAsDateTimeResult :=
  match result with
  | .noValue notGiven => .noValue (inherited || notGiven)
  | .value localDateTime instant notGiven =>
      .value localDateTime instant (inherited || notGiven)
  | .nonRelevant => .nonRelevant
  | .unavailable cause => .unavailable cause

/-- Apply one reached outer numeric amount to an exact inner DateTime result. This
    owns the shared value, no-value, omission, and bounded-profile behavior used by
    both field-backed and dynamic nested sub-day shifts. -/
def applyShiftedAmount (profile : ModelZone.ConcreteProfile)
    (nextUnit : DateTimeSubdayUnit) (source : ValueAsDateTimeResult) :
    NumericArithmeticOutcome →
      Except ValueAsDateTimeExtractionFault ValueAsDateTimeResult
  | .notEvaluated =>
      match source with
      | .noValue notGiven | .value _ _ notGiven => pure (.noValue notGiven)
      | .nonRelevant => pure .nonRelevant
      | .unavailable cause => pure (.unavailable cause)

  | .value amount fillability =>
      match source with
      | .noValue notGiven =>
          pure (.noValue
            (notGiven || fillability.canGrow || fillability.canShrink))
      | .value _ instant notGiven =>
          let shiftedInstant :=
            instant.shift nextUnit (temporalShiftAmountToInt32 amount)
          match ofShiftedNumericOperand?
              profile nextUnit instant (.value amount fillability) with
          | some result => pure (result.inheritNotGiven notGiven)
          | none => throw (.shiftedInstantOutsideProfile shiftedInstant)
      | .nonRelevant => pure .nonRelevant
      | .unavailable cause => pure (.unavailable cause)

/-- Read and apply one checked elapsed amount to an already evaluated exact DateTime
    result. A reached formal cause stops before this read; cause-free no-value reaches
    it. -/
def evaluateShiftedAmount (profile : ModelZone.ConcreteProfile)
    (unit : DateTimeSubdayUnit)
    (amount : CheckedTemporalShiftAmount model)
    (source : ValueAsDateTimeResult)
    (phase : Phase) (input : CheckedDocument model) :
    Except ValueAsDateTimeExtractionFault ValueAsDateTimeResult :=
  match source with
  | .unavailable cause => .ok (.unavailable cause)
  | source =>
      match amount.read phase input with
      | .error error => .error (.document error)
      | .ok (.error (.formal cause)) => .ok (.unavailable cause)
      | .ok (.error reason) =>
          .error (.amountExpressionUnavailable reason)
      | .ok (.ok outcome) =>
          source.applyShiftedAmount profile unit outcome

end ValueAsDateTimeResult

namespace CheckedShiftedDateTimeSource

/-- Read the certified DateTime before its amount and retain the shifted whole
    DateTime's exact instant, wall label, omission provenance, and formal cause. -/
def evaluate (checked : CheckedShiftedDateTimeSource model)
    (phase : Phase) (input : CheckedDocument model) :
    Except ValueAsDateTimeExtractionFault ValueAsDateTimeResult := do
  let cell ← input.read {
    field := checked.source.id
    path := []
  } |>.mapError .document
  ValueAsDateTimeResult.evaluateShiftedDateTimeObservation
    checked.profile checked.unit checked.source.id (observeCell phase cell)
    (fun _ => checked.amount.read phase input |>.mapError .document) id

/-- Specialize the whole shifted value to the existing wall-clock extraction result. -/
def readTime (checked : CheckedShiftedDateTimeSource model)
    (phase : Phase) (input : CheckedDocument model) :
    Except ValueAsDateTimeExtractionFault ValueAsDateTimeTimeOperand :=
  checked.evaluate phase input |>.map (·.asTimeOperand)

/-- Apply a reached outer numeric amount to one exact inner sub-day result. -/
def applyResultAmount (checked : CheckedShiftedDateTimeSource model)
    (nextUnit : DateTimeSubdayUnit) (source : ValueAsDateTimeResult) :
    NumericArithmeticOutcome →
      Except ValueAsDateTimeExtractionFault ValueAsDateTimeResult
  | outcome =>
      source.applyShiftedAmount checked.profile nextUnit outcome

/-- Feed one exact sub-day result into one further generated sub-day shift. The inner
    operation runs before the outer amount; cause-free no-value still reaches it. -/
def evaluateThen (checked : CheckedShiftedDateTimeSource model)
    (nextUnit : DateTimeSubdayUnit)
    (nextAmount : CheckedTemporalShiftAmount model)
    (phase : Phase) (input : CheckedDocument model) :
    Except ValueAsDateTimeExtractionFault ValueAsDateTimeResult :=
  match checked.evaluate phase input with
  | .error error => .error error
  | .ok source =>
      source.evaluateShiftedAmount checked.profile
        nextUnit nextAmount phase input

end CheckedShiftedDateTimeSource

/-- Check one ordinary complete-DateTime field and select its exact model-zone profile. -/
def elaborateDateTimeSource
    (model : FlatModel) (sourceField : FieldId) :
    Except ValueAsDateTimeExtractionElabError
      (CheckedDateTimeSource model) := do
  let declaration ←
    model.resolveNonrepeatableDeclarationById sourceField |>.mapError .source
  let source ← match declaration.toTemporalField? with
    | some source => pure source
    | none => throw (.sourceNotTemporal sourceField)
  if _hKind : source.kind = .dateTime then
    if _hComponents : source.components.isFullDateTime = true then
      if hAdmitted :
          model.admitsValueAsDateTimeExtractionSource source = true then
        match hProfile : ModelZone.ConcreteProfile.ofId? model.timeZoneId with
        | some profile =>
            pure {
              source
              sourceAdmitted := hAdmitted
              profile
              profileMatches := hProfile
            }
        | none => throw (.unsupportedZone model.timeZoneId)
      else
        throw .incoherentCore
    else
      throw (.sourceComponents source.id source.components)
  else
    throw (.sourceKind source.id source.kind)

/-- Check the shared field-backed DateTime source and numeric amount before one
    operation selects elapsed or calendar-day shifting. -/
def elaborateDateTimeNumericShiftSource
    (model : FlatModel) (sourceField : FieldId)
    (amount : CheckedTemporalShiftAmount model) :
    Except ValueAsDateTimeExtractionElabError
      (CheckedDateTimeNumericShiftSource model) := do
  let source ← elaborateDateTimeSource model sourceField
  pure { source with amount }

/-- Check the shared field-backed shifted-DateTime source after its amount has been certified by the selected numeric-expression boundary. -/
def elaborateShiftedDateTimeSource
    (model : FlatModel) (sourceField : FieldId)
    (unit : DateTimeSubdayUnit)
    (amount : CheckedTemporalShiftAmount model) :
    Except ValueAsDateTimeExtractionElabError
      (CheckedShiftedDateTimeSource model) := do
  let source ←
    elaborateDateTimeNumericShiftSource model sourceField amount
  pure { source with unit }

/-- Read one already-certified complete-DateTime source at an exact address and retain its wall clock, clean absence, or exact formal cause. Static source admission and address ownership remain the caller's checked responsibilities. -/
def readTimeFromDateTimeSourceAt (source : FlatTemporalField)
    (address : CellAddr) (phase : Phase) (input : CheckedDocument model) :
    Except ValueAsDateTimeExtractionFault ValueAsDateTimeTimeOperand := do
  let cell ← input.read address |>.mapError .document
  match ValueAsDateTimeTimeOperand.ofDateTimeValueObservation
      (observeCell phase cell) with
  | some time => pure time
  | none => throw (.sourcePayloadMismatch source.id)

/-- Scalar compatibility specialization of the exact-address complete-DateTime clock read. -/
def readTimeFromDateTimeSource (source : FlatTemporalField)
    (phase : Phase) (input : CheckedDocument model) :
    Except ValueAsDateTimeExtractionFault ValueAsDateTimeTimeOperand :=
  readTimeFromDateTimeSourceAt source { field := source.id, path := [] }
    phase input

namespace CheckedValueAsDateTimeExtraction

/-- Read the certified scalar DateTime source once and retain its wall clock, empty state, or exact formal cause. The reference semantics uses a linear immutable document lookup and adds no second zone conversion. -/
def readTime (checked : CheckedValueAsDateTimeExtraction model)
    (phase : Phase) (input : CheckedDocument model) :
    Except ValueAsDateTimeExtractionFault ValueAsDateTimeTimeOperand :=
  readTimeFromDateTimeSource checked.source phase input

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
  amount : CheckedTemporalShiftAmount model

namespace CheckedValueAsDateTimeShiftExtraction

/-- Forget only the enclosing partial-Date construction while retaining its already-checked model-zone shift source. -/
def toCheckedShiftedDateTimeSource
    (checked : CheckedValueAsDateTimeShiftExtraction model) :
    CheckedShiftedDateTimeSource model := {
  source := checked.source
  sourceAdmitted := checked.sourceAdmitted
  profile := checked.construction.profile
  profileMatches := checked.construction.profileMatches
  unit := checked.unit
  amount := checked.amount
}

/-- Read the certified source before the amount, apply Java-compatible signed-32-bit conversion, then decode the shifted exact instant under the model-owned profile. A formal source stops before the amount; an empty source still reaches it. -/
def readShiftedTime (checked : CheckedValueAsDateTimeShiftExtraction model)
    (phase : Phase) (input : CheckedDocument model) :
    Except ValueAsDateTimeExtractionFault ValueAsDateTimeTimeOperand :=
  checked.toCheckedShiftedDateTimeSource.readTime phase input

/-- Check the bounded partial-Date source, then evaluate the shifted DateTime extraction only when generated left-to-right argument evaluation reaches it. -/
def evaluateRaw (checked : CheckedValueAsDateTimeShiftExtraction model)
    (phase : Phase) (input : CheckedDocument model)
    (raw : RawCell String) :
    Except ValueAsDateTimeExtractionFault ValueAsDateTimeResult :=
  checked.construction.evaluateTimeOperandRaw phase raw fun _ =>
    checked.readShiftedTime phase input

end CheckedValueAsDateTimeShiftExtraction

/-- One checked model-zone profile, sub-day unit, and amount for shifting this execution's dynamic `World.now`. -/
structure CheckedShiftedNowDateTimeSource (model : FlatModel) where
  profile : ModelZone.ConcreteProfile
  profileMatches :
    ModelZone.ConcreteProfile.ofId? model.timeZoneId = some profile
  unit : DateTimeSubdayUnit
  amount : CheckedTemporalShiftAmount model

namespace CheckedShiftedNowDateTimeSource

/-- Shift this execution's exact `World.now` while retaining the whole model-zone
    DateTime label, exact instant, and numeric omission provenance. -/
def evaluate (checked : CheckedShiftedNowDateTimeSource model)
    (phase : Phase) (world : World) (input : CheckedDocument model) :
    Except ValueAsDateTimeExtractionFault ValueAsDateTimeResult :=
  checked.amount.readShiftedDateTime phase input
    checked.profile checked.unit world.now

/-- Shift this execution's exact instant before a consumer projects the whole Time or one component. -/
def readTime (checked : CheckedShiftedNowDateTimeSource model)
    (phase : Phase) (world : World) (input : CheckedDocument model) :
    Except ValueAsDateTimeExtractionFault ValueAsDateTimeTimeOperand :=
  checked.evaluate phase world input |>.map (·.asTimeOperand)

/-- Apply a reached outer amount through the shared exact-result mechanism. -/
def applyResultAmount (checked : CheckedShiftedNowDateTimeSource model)
    (nextUnit : DateTimeSubdayUnit) (source : ValueAsDateTimeResult) :
    NumericArithmeticOutcome →
      Except ValueAsDateTimeExtractionFault ValueAsDateTimeResult
  | outcome =>
      source.applyShiftedAmount checked.profile nextUnit outcome

/-- Feed one dynamically sampled exact result into one further generated sub-day
    shift. The inner amount runs before the outer amount, and the supplied `World`
    remains the sole dynamic input. -/
def evaluateThen (checked : CheckedShiftedNowDateTimeSource model)
    (nextUnit : DateTimeSubdayUnit)
    (nextAmount : CheckedTemporalShiftAmount model)
    (phase : Phase) (world : World) (input : CheckedDocument model) :
    Except ValueAsDateTimeExtractionFault ValueAsDateTimeResult :=
  match checked.evaluate phase world input with
  | .error error => .error error
  | .ok source =>
      source.evaluateShiftedAmount checked.profile
        nextUnit nextAmount phase input

end CheckedShiftedNowDateTimeSource

/-- Check a dynamic shifted-DateTime source without sampling its execution world. -/
def elaborateShiftedNowDateTimeSource
    (model : FlatModel) (unit : DateTimeSubdayUnit)
    (amount : CheckedTemporalShiftAmount model) :
    Except ValueAsDateTimeExtractionElabError
      (CheckedShiftedNowDateTimeSource model) :=
  match hProfile : ModelZone.ConcreteProfile.ofId? model.timeZoneId with
  | some profile =>
      pure {
        profile
        profileMatches := hProfile
        unit
        amount
      }
  | none => throw (.unsupportedZone model.timeZoneId)

/-- One checked partial-Date constructor whose Time side shifts dynamic `Now` by a checked amount before extraction. The world remains an execution input and no instant is sampled during elaboration. -/
structure CheckedValueAsDateTimeNowShiftExtraction (model : FlatModel) where
  construction : CheckedValueAsDateTime model
  unit : DateTimeSubdayUnit
  amount : CheckedTemporalShiftAmount model

namespace CheckedValueAsDateTimeNowShiftExtraction

/-- Forget only the enclosing partial-Date construction while retaining its already-checked dynamic shift source. -/
def toCheckedShiftedNowDateTimeSource
    (checked : CheckedValueAsDateTimeNowShiftExtraction model) :
    CheckedShiftedNowDateTimeSource model := {
  profile := checked.construction.profile
  profileMatches := checked.construction.profileMatches
  unit := checked.unit
  amount := checked.amount
}

/-- Read the checked amount after sampling this execution's exact `World.now`, then project the shifted model-zone clock. -/
def readShiftedTime (checked : CheckedValueAsDateTimeNowShiftExtraction model)
    (phase : Phase) (world : World) (input : CheckedDocument model) :
    Except ValueAsDateTimeExtractionFault ValueAsDateTimeTimeOperand :=
  checked.toCheckedShiftedNowDateTimeSource.readTime phase world input

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

/-- Resolve one checked direct extraction and one same-group numeric operation over ordinary Number fields. -/
def elaborateValueAsDateTimeExpressionShiftExtraction
    (model : FlatModel) (rowGroup : GroupPath)
    (dateField : FieldId) (endpoint : ValueAsDateEndpoint)
    (dateTimeField : FieldId) (unit : DateTimeSubdayUnit)
    (amount : AuthoredNumericExpr SurfaceNumericAtom) :
    Except ValueAsDateTimeExtractionElabError
      (CheckedValueAsDateTimeShiftExtraction model) := do
  let extraction ←
    elaborateValueAsDateTimeExtraction model dateField endpoint dateTimeField
  let checkedAmount ←
    elaborateValueAsDateTimeExpressionShiftAmount model rowGroup amount
  pure { extraction with unit, amount := checkedAmount }

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

/-- Resolve the partial-Date side and one same-group numeric operation over ordinary Number fields without sampling `Now`. -/
def elaborateValueAsDateTimeNowExpressionShiftExtraction
    (model : FlatModel) (rowGroup : GroupPath)
    (dateField : FieldId) (endpoint : ValueAsDateEndpoint)
    (unit : DateTimeSubdayUnit)
    (amount : AuthoredNumericExpr SurfaceNumericAtom) :
    Except ValueAsDateTimeExtractionElabError
      (CheckedValueAsDateTimeNowShiftExtraction model) := do
  let construction ←
    elaborateValueAsDateTime model dateField endpoint |>.mapError .construction
  let checkedAmount ←
    elaborateValueAsDateTimeExpressionShiftAmount model rowGroup amount
  pure { construction, unit, amount := checkedAmount }

end A12Kernel
