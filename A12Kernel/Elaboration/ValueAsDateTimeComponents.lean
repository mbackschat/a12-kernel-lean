import A12Kernel.Elaboration.CheckedDocument
import A12Kernel.Elaboration.ValueAsDate

/-! # Partial-Date and checked `Time(...)` components

This capsule checks and executes one mixed prefix of ordinary nonrepeatable Number fields
and matching time-component extractors over ordinary Time or DateTime fields. Number
declarations retain their integral nonnegative positional certificate; extractor
declarations retain their temporal kind, component, and exact authored-position
certificate. Execution reads the immutable checked document in Hour/Minute/Second order
and delegates defaults and clock classification to `TimeConstructionResult`.

String fields remain excluded because the flat declaration does not retain the kernel
checker's extensible-enumeration distinction. Wider expression-sourced extractors remain
outside this field-backed capsule.
-/

namespace A12Kernel

/-- The declaration gate selected by a field's authored `Time(...)` position. -/
inductive TimeComponentPosition where
  | hour
  | minute
  | second
  deriving Repr, DecidableEq

namespace TimeComponentPosition

/-- Inclusive maximum accepted as the position-specific alternative to stored length 2. -/
def maximum : TimeComponentPosition → Rat
  | .hour => 23
  | .minute | .second => 59

/-- The only extractor token admitted at this constructor position. -/
def extractor : TimeComponentPosition → TimeNumericPart
  | .hour => .hour
  | .minute => .minute
  | .second => .second

end TimeComponentPosition

private def hasNonnegativeNumberDomain
    (declaration : FlatFieldDecl) (source : FlatNumberField) : Bool :=
  if source.info.signed then
    match declaration.numericTargetConstraints.minimum with
    | some minimum => decide (0 ≤ minimum)
    | none => false
  else
    true

/-- Exact Number declaration gate used by one `Time(...)` component position. The
    two-character alternative is the declaration's complete stored-length bound, not its
    integer-digit cap. -/
def FlatModel.admitsTimeNumberField (model : FlatModel)
    (position : TimeComponentPosition) (source : FlatNumberField) : Bool :=
  match model.lookupUniqueId source.id with
  | .error _ => false
  | .ok declaration =>
      let constraints := declaration.numericTargetConstraints
      declaration.repeatableScope.isEmpty &&
        declaration.toNumberField? == some source &&
        source.info.scale == 0 &&
        constraints.minFractionalDigits == 0 &&
        (constraints.maxStoredLength == some 2 ||
          constraints.maximum == some position.maximum) &&
        hasNonnegativeNumberDomain declaration source

/-- One ordinary Number field whose declaration carries the exact component certificate. -/
structure CheckedTimeNumberField (model : FlatModel) where
  position : TimeComponentPosition
  source : FlatNumberField
  admitted : model.admitsTimeNumberField position source = true

/-- Exact field-backed extractor admission. The selected temporal half and constructor
    position are both static obligations. -/
def FlatModel.admitsTimeExtractorField (model : FlatModel)
    (position : TimeComponentPosition) (part : TimeNumericPart)
    (source : FlatTemporalField) : Bool :=
  match model.lookupUniqueId source.id with
  | .error _ => false
  | .ok declaration =>
      declaration.repeatableScope.isEmpty &&
        declaration.toTemporalField? == some source &&
        (source.kind == .time || source.kind == .dateTime) &&
        part.admittedBy source.components &&
        position.extractor == part

/-- One ordinary Time or DateTime field under its matching extraction token. -/
structure CheckedTimeExtractorField (model : FlatModel) where
  position : TimeComponentPosition
  part : TimeNumericPart
  source : FlatTemporalField
  admitted : model.admitsTimeExtractorField position part source = true

/-- One grammar-valid field-backed component before model-relative checking. -/
inductive SurfaceTimeComponent where
  | number (field : FieldId)
  | extractor (part : TimeNumericPart) (field : FieldId)
  deriving Repr, DecidableEq

/-- One checked component retaining the branch-specific static certificate. -/
inductive CheckedTimeComponent (model : FlatModel) where
  | number (checked : CheckedTimeNumberField model)
  | extractor (checked : CheckedTimeExtractorField model)

/-- The grammar-valid one-to-three-component prefix. Omitted trailing components are
    absent from this type and therefore cannot be read. -/
inductive SurfaceTimeComponents where
  | hour (hour : SurfaceTimeComponent)
  | minute (hour minute : SurfaceTimeComponent)
  | second (hour minute second : SurfaceTimeComponent)
  deriving Repr, DecidableEq

/-- A checked mixed prefix retaining each component's authored position. -/
inductive CheckedTimeComponents (model : FlatModel) where
  | hour (hour : CheckedTimeComponent model)
  | minute (hour minute : CheckedTimeComponent model)
  | second (hour minute second : CheckedTimeComponent model)

/-- Static rejection before any `Time(...)` component source is read. -/
inductive TimeComponentsElabError where
  | field (position : TimeComponentPosition) (error : ResolveError)
  | numberSourceKind (position : TimeComponentPosition) (field : FieldId)
  | extractorSourceKind (position : TimeComponentPosition) (field : FieldId)
  | extractorMismatch (position : TimeComponentPosition) (actual : TimeNumericPart)
  | declarationNotAdmitted (position : TimeComponentPosition) (field : FieldId)
  deriving Repr, DecidableEq

private def elaborateTimeNumberField (model : FlatModel)
    (position : TimeComponentPosition) (field : FieldId) :
    Except TimeComponentsElabError (CheckedTimeNumberField model) := do
  let declaration ←
    model.resolveNonrepeatableDeclarationById field |>.mapError (.field position)
  let source ← match declaration.toNumberField? with
    | some source => pure source
    | none => throw (.numberSourceKind position field)
  if admitted : model.admitsTimeNumberField position source = true then
    pure { position, source, admitted }
  else
    throw (.declarationNotAdmitted position field)

private def elaborateTimeExtractorField (model : FlatModel)
    (position : TimeComponentPosition) (part : TimeNumericPart) (field : FieldId) :
    Except TimeComponentsElabError (CheckedTimeExtractorField model) := do
  if position.extractor != part then
    throw (.extractorMismatch position part)
  let declaration ←
    model.resolveNonrepeatableDeclarationById field |>.mapError (.field position)
  let source ← match declaration.toTemporalField? with
    | some source => pure source
    | none => throw (.extractorSourceKind position field)
  if admitted : model.admitsTimeExtractorField position part source = true then
    pure { position, part, source, admitted }
  else
    throw (.declarationNotAdmitted position field)

private def elaborateTimeComponent (model : FlatModel)
    (position : TimeComponentPosition) :
    SurfaceTimeComponent → Except TimeComponentsElabError (CheckedTimeComponent model)
  | .number field =>
      .number <$> elaborateTimeNumberField model position field
  | .extractor part field =>
      .extractor <$> elaborateTimeExtractorField model position part field

/-- Check every supplied component from Hour through Second and preserve that prefix order. -/
def elaborateTimeComponents (model : FlatModel) :
    SurfaceTimeComponents →
      Except TimeComponentsElabError (CheckedTimeComponents model)
  | .hour hour => do
      pure (.hour (← elaborateTimeComponent model .hour hour))
  | .minute hour minute => do
      pure (.minute
        (← elaborateTimeComponent model .hour hour)
        (← elaborateTimeComponent model .minute minute))
  | .second hour minute second => do
      pure (.second
        (← elaborateTimeComponent model .hour hour)
        (← elaborateTimeComponent model .minute minute)
        (← elaborateTimeComponent model .second second))

/-- Structural failure outside the reason-bearing `TimeConstructionResult` domain. -/
inductive TimeComponentsFault where
  | document (error : CheckedDocumentError)
  | payloadKind (field : FieldId)
  | nonIntegralPayload (field : FieldId) (value : Rat)
  deriving Repr, DecidableEq

namespace CheckedTimeNumberField

/-- Project one checked Number cell to the constructor component domain without applying
    arithmetic truncation or accepting a mismatched runtime payload. -/
def classify (checked : CheckedTimeNumberField model)
    (observation : CellObservation Value) :
    Except TimeComponentsFault TimeConstructionComponent :=
  match observation with
  | .empty => pure .empty
  | .unknown cause | .poison cause => pure (.unavailable cause)
  | .value (.num value) =>
      if value.den = 1 then
        pure (.value value.num)
      else
        throw (.nonIntegralPayload checked.source.id value)
  | .value _ => throw (.payloadKind checked.source.id)

/-- Read one certified scalar component through the immutable checked document. -/
def read (checked : CheckedTimeNumberField model)
    (phase : Phase) (input : CheckedDocument model) :
    Except TimeComponentsFault TimeConstructionComponent := do
  let cell ← input.read {
    field := checked.source.id
    path := []
  } |>.mapError .document
  checked.classify (observeCell phase cell)

end CheckedTimeNumberField

namespace CheckedTimeExtractorField

private def clockObservation? (kind : TemporalKind) :
    CellObservation Value → Option (CellObservation TimeOfDay)
  | .empty => some .empty
  | .unknown cause => some (.unknown cause)
  | .poison cause => some (.poison cause)
  | .value (.temporal (.time _ clock)) =>
      if kind == .time then some (.value clock) else none
  | .value (.temporal (.dateTime _ _ clock _)) =>
      if kind == .dateTime then some (.value clock) else none
  | .value _ => none

private def componentOfNumericOperand (field : FieldId) :
    NumericOperand → Except TimeComponentsFault TimeConstructionComponent
  | .value amount fillability =>
      if fillability.canGrow || fillability.canShrink then
        pure .empty
      else if amount.den = 1 then
          pure (.value amount.num)
        else
          throw (.nonIntegralPayload field amount)
  | .unknown cause => pure (.unavailable cause)

/-- Project the selected clock component. Empty temporal input follows the extractor's
    symmetric numeric-zero rule; formal unavailability retains its exact cause. -/
def classify (checked : CheckedTimeExtractorField model)
    (observation : CellObservation Value) :
    Except TimeComponentsFault TimeConstructionComponent :=
  match clockObservation? checked.source.kind observation with
  | some projected =>
      componentOfNumericOperand checked.source.id
        (checked.part.fromTimeObservation projected)
  | none => throw (.payloadKind checked.source.id)

/-- Read one certified scalar temporal source through the immutable checked document. -/
def read (checked : CheckedTimeExtractorField model)
    (phase : Phase) (input : CheckedDocument model) :
    Except TimeComponentsFault TimeConstructionComponent := do
  let cell ← input.read {
    field := checked.source.id
    path := []
  } |>.mapError .document
  checked.classify (observeCell phase cell)

end CheckedTimeExtractorField

namespace CheckedTimeComponent

/-- Execute exactly the statically selected component branch. -/
def read (checked : CheckedTimeComponent model)
    (phase : Phase) (input : CheckedDocument model) :
    Except TimeComponentsFault TimeConstructionComponent :=
  match checked with
  | .number field => field.read phase input
  | .extractor field => field.read phase input

end CheckedTimeComponent

namespace CheckedTimeComponents

/-- Evaluate only the supplied prefix. A reached formal component stops before every later
    field read; omitted trailing slots are delegated to `TimeConstructionArity`. -/
def evaluate (checked : CheckedTimeComponents model)
    (phase : Phase) (input : CheckedDocument model) :
    Except TimeComponentsFault TimeConstructionResult :=
  match checked with
  | CheckedTimeComponents.hour hourField => do
      let hourValue ← hourField.read phase input
      pure (TimeConstructionArity.hour.evaluate hourValue .empty .empty)
  | CheckedTimeComponents.minute hourField minuteField => do
      let hourValue ← hourField.read phase input
      match hourValue with
      | .unavailable cause => pure (.unavailable cause)
      | hourValue =>
          let minuteValue ← minuteField.read phase input
          pure (TimeConstructionArity.minute.evaluate hourValue minuteValue .empty)
  | CheckedTimeComponents.second hourField minuteField secondField => do
      let hourValue ← hourField.read phase input
      match hourValue with
      | .unavailable cause => pure (.unavailable cause)
      | hourValue =>
          let minuteValue ← minuteField.read phase input
          match minuteValue with
          | .unavailable cause => pure (.unavailable cause)
          | minuteValue =>
              let secondValue ← secondField.read phase input
              pure (TimeConstructionArity.second.evaluate
                hourValue minuteValue secondValue)

end CheckedTimeComponents

namespace CheckedValueAsDateTime

/-- Check the bounded partial-Date source first, then execute a checked mixed Time prefix
    only when generated left-to-right DateTime construction reaches it. -/
def evaluateComponentsRaw (checked : CheckedValueAsDateTime model)
    (time : CheckedTimeComponents model)
    (phase : Phase) (input : CheckedDocument model) (raw : RawCell String) :
    Except TimeComponentsFault ValueAsDateTimeResult :=
  checked.evaluateTimeOperandRaw phase raw fun _ => do
    let timeResult ← time.evaluate phase input
    pure timeResult.asDateTimeOperand

end CheckedValueAsDateTime

end A12Kernel
