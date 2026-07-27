import A12Kernel.Elaboration.CheckedDocument
import A12Kernel.Elaboration.ValueAsDate

/-! # Partial-Date and Number-field `Time(...)`

This capsule checks and executes the ordinary nonrepeatable Number-field form of each
supplied `Time(...)` component. The declaration must guarantee an integral nonnegative
value and either the two-character stored bound or the exact maximum for its position.
Execution reads the immutable checked document in Hour/Minute/Second order and delegates
all component defaults and clock classification to `TimeConstructionResult`.

String fields remain excluded because the flat declaration does not retain the kernel
checker's extensible-enumeration distinction. Extractors and mixed component forms remain
separate.
-/

namespace A12Kernel

/-- The declaration gate selected by a field's authored `Time(...)` position. -/
inductive TimeNumberFieldPosition where
  | hour
  | minute
  | second
  deriving Repr, DecidableEq

namespace TimeNumberFieldPosition

/-- Inclusive maximum accepted as the position-specific alternative to stored length 2. -/
def maximum : TimeNumberFieldPosition → Rat
  | .hour => 23
  | .minute | .second => 59

end TimeNumberFieldPosition

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
    (position : TimeNumberFieldPosition) (source : FlatNumberField) : Bool :=
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
  position : TimeNumberFieldPosition
  source : FlatNumberField
  admitted : model.admitsTimeNumberField position source = true

/-- The grammar-valid one-to-three-field prefix forms. Omitted trailing components are
    absent from this type and therefore cannot be read. -/
inductive SurfaceTimeNumberFields where
  | hour (hour : FieldId)
  | minute (hour minute : FieldId)
  | second (hour minute second : FieldId)
  deriving Repr, DecidableEq

/-- A checked one-to-three-field prefix retaining each field's authored position. -/
inductive CheckedTimeNumberFields (model : FlatModel) where
  | hour (hour : CheckedTimeNumberField model)
  | minute (hour minute : CheckedTimeNumberField model)
  | second (hour minute second : CheckedTimeNumberField model)

/-- Static rejection before any `Time(...)` component field is read. -/
inductive TimeNumberFieldsElabError where
  | field (position : TimeNumberFieldPosition) (error : ResolveError)
  | notNumber (position : TimeNumberFieldPosition) (field : FieldId)
  | declarationNotAdmitted (position : TimeNumberFieldPosition) (field : FieldId)
  deriving Repr, DecidableEq

private def elaborateTimeNumberField (model : FlatModel)
    (position : TimeNumberFieldPosition) (field : FieldId) :
    Except TimeNumberFieldsElabError (CheckedTimeNumberField model) := do
  let declaration ←
    model.resolveNonrepeatableDeclarationById field |>.mapError (.field position)
  let source ← match declaration.toNumberField? with
    | some source => pure source
    | none => throw (.notNumber position field)
  if admitted : model.admitsTimeNumberField position source = true then
    pure { position, source, admitted }
  else
    throw (.declarationNotAdmitted position field)

/-- Check every supplied field from Hour through Second and preserve that prefix order. -/
def elaborateTimeNumberFields (model : FlatModel) :
    SurfaceTimeNumberFields →
      Except TimeNumberFieldsElabError (CheckedTimeNumberFields model)
  | .hour hour => do
      pure (.hour (← elaborateTimeNumberField model .hour hour))
  | .minute hour minute => do
      pure (.minute
        (← elaborateTimeNumberField model .hour hour)
        (← elaborateTimeNumberField model .minute minute))
  | .second hour minute second => do
      pure (.second
        (← elaborateTimeNumberField model .hour hour)
        (← elaborateTimeNumberField model .minute minute)
        (← elaborateTimeNumberField model .second second))

/-- Structural failure outside the reason-bearing `TimeConstructionResult` domain. -/
inductive TimeNumberFieldsFault where
  | document (error : CheckedDocumentError)
  | payloadKind (field : FieldId)
  | nonIntegralPayload (field : FieldId) (value : Rat)
  deriving Repr, DecidableEq

namespace CheckedTimeNumberField

/-- Project one checked Number cell to the constructor component domain without applying
    arithmetic truncation or accepting a mismatched runtime payload. -/
def classify (checked : CheckedTimeNumberField model)
    (observation : CellObservation Value) :
    Except TimeNumberFieldsFault TimeConstructionComponent :=
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
    Except TimeNumberFieldsFault TimeConstructionComponent := do
  let cell ← input.read {
    field := checked.source.id
    path := []
  } |>.mapError .document
  checked.classify (observeCell phase cell)

end CheckedTimeNumberField

namespace CheckedTimeNumberFields

/-- Evaluate only the supplied prefix. A reached formal component stops before every later
    field read; omitted trailing slots are delegated to `TimeConstructionArity`. -/
def evaluate (checked : CheckedTimeNumberFields model)
    (phase : Phase) (input : CheckedDocument model) :
    Except TimeNumberFieldsFault TimeConstructionResult :=
  match checked with
  | CheckedTimeNumberFields.hour hourField => do
      let hourValue ← hourField.read phase input
      pure (TimeConstructionArity.hour.evaluate hourValue .empty .empty)
  | CheckedTimeNumberFields.minute hourField minuteField => do
      let hourValue ← hourField.read phase input
      match hourValue with
      | .unavailable cause => pure (.unavailable cause)
      | hourValue =>
          let minuteValue ← minuteField.read phase input
          pure (TimeConstructionArity.minute.evaluate hourValue minuteValue .empty)
  | CheckedTimeNumberFields.second hourField minuteField secondField => do
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

end CheckedTimeNumberFields

namespace CheckedValueAsDateTime

/-- Check the bounded partial-Date source first, then execute a checked Number-field Time
    prefix only when generated left-to-right DateTime construction reaches it. -/
def evaluateNumberFieldsRaw (checked : CheckedValueAsDateTime model)
    (time : CheckedTimeNumberFields model)
    (phase : Phase) (input : CheckedDocument model) (raw : RawCell String) :
    Except TimeNumberFieldsFault ValueAsDateTimeResult :=
  checked.evaluateTimeOperandRaw phase raw fun _ => do
    let timeResult ← time.evaluate phase input
    pure timeResult.asDateTimeOperand

end CheckedValueAsDateTime

end A12Kernel
