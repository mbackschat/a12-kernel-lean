import A12Kernel.Elaboration.CheckedDocument
import A12Kernel.Elaboration.ValueAsDateTimeExtraction

/-! # Partial-Date and checked `Time(...)` components

This capsule checks and executes one mixed prefix of ordinary nonrepeatable Number fields,
pattern-backed String fields, and matching time-component extractors over ordinary Time
or DateTime fields. A bounded nonliteral extractor may instead consume the shared checked
field-backed DateTime shift. Each declaration retains its branch-specific static
certificate. Execution reads the immutable checked document in Hour/Minute/Second order
and delegates defaults and clock classification to `TimeConstructionResult`.

The String branch covers the six checker-recognized digit patterns. The separate
extensible-enumeration alternative remains excluded because the flat declaration does not
retain that fact. Wider recursive temporal-expression sources remain outside.
-/

namespace A12Kernel

/-- The declaration gate selected by a field's authored `Time(...)` position. -/
inductive TimeComponentPosition where
  | hour
  | minute
  | second
  deriving Repr, DecidableEq

namespace TimeComponentPosition

/-- Inclusive natural-number bound for a quoted constant at this position. -/
def maximumNat : TimeComponentPosition → Nat
  | .hour => 23
  | .minute | .second => 59

/-- Inclusive maximum accepted as the position-specific alternative to stored length 2. -/
def maximum : TimeComponentPosition → Rat
  | position => position.maximumNat

/-- Decode one already-unescaped quoted constant under the pinned Java 21 decimal-digit profile and position bound. -/
def decodeConstant? (position : TimeComponentPosition)
    (source : String) : Option Int := do
  let value ← parseJava21BmpNatural? source
  if value ≤ position.maximumNat then
    some value
  else
    none

/-- The only extractor token admitted at this constructor position. -/
def extractor : TimeComponentPosition → TimeNumericPart
  | .hour => .hour
  | .minute => .minute
  | .second => .second

end TimeComponentPosition

/-- Exact Number declaration gate shared by scalar and addressed `Time(...)` component positions. Placement is certified separately, so this predicate owns only kind and numeric policy. The two-character alternative is the declaration's complete stored-length bound, not its integer-digit cap. -/
def FlatModel.admitsTimeNumberComponentField (model : FlatModel)
    (position : TimeComponentPosition) (source : FlatNumberField) : Bool :=
  match model.lookupUniqueId source.id with
  | .error _ => false
  | .ok declaration =>
      let constraints := declaration.numericTargetConstraints
      declaration.toNumberField? == some source &&
        source.info.scale == 0 &&
        constraints.minFractionalDigits == 0 &&
        (constraints.maxStoredLength == some 2 ||
          constraints.maximum == some position.maximum) &&
        declaration.numberDomainNonnegative source

/-- Scalar specialization of the shared Number-component policy gate. -/
def FlatModel.admitsTimeNumberField (model : FlatModel)
    (position : TimeComponentPosition) (source : FlatNumberField) : Bool :=
  match model.lookupUniqueId source.id with
  | .error _ => false
  | .ok declaration =>
      declaration.repeatableScope.isEmpty &&
        model.admitsTimeNumberComponentField position source

/-- One ordinary Number field whose declaration carries the exact component certificate. -/
structure CheckedTimeNumberField (model : FlatModel) where
  position : TimeComponentPosition
  source : FlatNumberField
  admitted : model.admitsTimeNumberField position source = true

/-- Whether the exact declared source is one of the six digit patterns the construction
    checker recognizes without interpreting general regular-expression equivalence. -/
def isTimeComponentDigitPattern (source : String) : Bool :=
  isTemporalComponentDigitPattern 2 source

/-- Placement-neutral pattern-backed String declaration gate shared by scalar and addressed `Time(...)` components. Extensible-enumeration admission is deliberately not represented here. -/
def FlatModel.admitsTimeStringComponentField (model : FlatModel)
    (source : FlatStringField) : Bool :=
  match model.lookupUniqueId source.id with
  | .error _ => false
  | .ok declaration =>
      declaration.toStringValueField? == some source &&
        declaration.customType.isNone &&
        declaration.enumeration.isNone &&
        declaration.stringPolicy.maxLength == some 2 &&
        declaration.stringPatternSource.any isTimeComponentDigitPattern

/-- Scalar specialization of the shared String-component policy gate. -/
def FlatModel.admitsTimeStringField (model : FlatModel)
    (source : FlatStringField) : Bool :=
  match model.lookupUniqueId source.id with
  | .error _ => false
  | .ok declaration =>
      declaration.repeatableScope.isEmpty &&
        model.admitsTimeStringComponentField source

/-- One ordinary checked String field under the recognized digit-pattern subset. -/
structure CheckedTimeStringField (model : FlatModel) where
  position : TimeComponentPosition
  source : FlatStringField
  admitted : model.admitsTimeStringField source = true

/-- Placement-neutral field-backed extractor admission. The selected temporal half and constructor position are static obligations; placement is certified separately. -/
def FlatModel.admitsTimeExtractorComponentField (model : FlatModel)
    (position : TimeComponentPosition) (part : TimeNumericPart)
    (source : FlatTemporalField) : Bool :=
  match model.lookupUniqueId source.id with
  | .error _ => false
  | .ok declaration =>
      declaration.toTemporalField? == some source &&
        (source.kind == .time || source.kind == .dateTime) &&
        part.admittedBy source.components &&
        position.extractor == part

/-- Scalar specialization of the shared extractor-component policy gate. -/
def FlatModel.admitsTimeExtractorField (model : FlatModel)
    (position : TimeComponentPosition) (part : TimeNumericPart)
    (source : FlatTemporalField) : Bool :=
  match model.lookupUniqueId source.id with
  | .error _ => false
  | .ok declaration =>
      declaration.repeatableScope.isEmpty &&
        model.admitsTimeExtractorComponentField position part source

/-- One ordinary Time or DateTime field under its matching extraction token. -/
structure CheckedTimeExtractorField (model : FlatModel) where
  position : TimeComponentPosition
  part : TimeNumericPart
  source : FlatTemporalField
  admitted : model.admitsTimeExtractorField position part source = true

/-- One matching component extractor over the shared checked field-backed DateTime shift. -/
structure CheckedShiftedTimeExtractor (model : FlatModel) where
  position : TimeComponentPosition
  part : TimeNumericPart
  source : CheckedShiftedDateTimeSource model
  positionMatches : position.extractor = part

/-- One grammar-valid field-backed component before model-relative checking. -/
inductive SurfaceTimeComponent where
  | number (field : FieldId)
  | string (field : FieldId)
  | constant (source : String)
  | extractor (part : TimeNumericPart) (field : FieldId)
  deriving Repr, DecidableEq

/-- One checked component retaining the branch-specific static certificate. -/
inductive CheckedTimeComponent (model : FlatModel) where
  | number (checked : CheckedTimeNumberField model)
  | string (checked : CheckedTimeStringField model)
  | constant (value : Int)
  | extractor (checked : CheckedTimeExtractorField model)
  | shiftedExtractor (checked : CheckedShiftedTimeExtractor model)

/-- The zero-to-three-component prefix shared by surface and checked carriers. Omitted trailing components are fixed zeroes and cannot be read. -/
inductive TimeComponentPrefix (Component : Type) where
  | empty
  | hour (hour : Component)
  | minute (hour minute : Component)
  | second (hour minute second : Component)
  deriving Repr, DecidableEq

/-- The grammar-valid component prefix before model-relative checking. -/
abbrev SurfaceTimeComponents :=
  TimeComponentPrefix SurfaceTimeComponent

/-- A checked mixed prefix retaining each component's authored position. -/
abbrev CheckedTimeComponents (model : FlatModel) :=
  TimeComponentPrefix (CheckedTimeComponent model)

/-- Static rejection before any `Time(...)` component source is read. -/
inductive TimeComponentsElabError where
  | field (position : TimeComponentPosition) (error : ResolveError)
  | numberSourceKind (position : TimeComponentPosition) (field : FieldId)
  | stringSourceKind (position : TimeComponentPosition) (field : FieldId)
  | constantNotAdmitted (position : TimeComponentPosition) (source : String)
  | extractorSourceKind (position : TimeComponentPosition) (field : FieldId)
  | extractorMismatch (position : TimeComponentPosition) (actual : TimeNumericPart)
  | declarationNotAdmitted (position : TimeComponentPosition) (field : FieldId)
  | shifted (error : ValueAsDateTimeExtractionElabError)
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

private def elaborateTimeStringField (model : FlatModel)
    (position : TimeComponentPosition) (field : FieldId) :
    Except TimeComponentsElabError (CheckedTimeStringField model) := do
  let declaration ←
    model.resolveNonrepeatableDeclarationById field |>.mapError (.field position)
  let source ← match declaration.toStringValueField? with
    | some source => pure source
    | none => throw (.stringSourceKind position field)
  if admitted : model.admitsTimeStringField source = true then
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
  | .string field =>
      .string <$> elaborateTimeStringField model position field
  | .constant source =>
      match position.decodeConstant? source with
      | some value => pure (.constant value)
      | none => throw (.constantNotAdmitted position source)
  | .extractor part field =>
      .extractor <$> elaborateTimeExtractorField model position part field

/-- Check every supplied component from Hour through Second and preserve that prefix order. -/
def elaborateTimeComponents (model : FlatModel) :
    SurfaceTimeComponents →
      Except TimeComponentsElabError (CheckedTimeComponents model)
  | .empty => pure .empty
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

/-- Check one matching Time-component extractor over the shared field-backed sub-day shift. -/
def elaborateShiftedTimeExtractor
    (model : FlatModel)
    (position : TimeComponentPosition) (part : TimeNumericPart)
    (sourceField : FieldId) (unit : DateTimeSubdayUnit)
    (amount : CheckedTemporalShiftAmount model) :
    Except TimeComponentsElabError (CheckedTimeComponent model) := do
  if hPosition : position.extractor = part then
    let source ←
      elaborateShiftedDateTimeSource model sourceField unit amount
        |>.mapError .shifted
    pure (.shiftedExtractor {
      position
      part
      source
      positionMatches := hPosition
    })
  else
    throw (.extractorMismatch position part)

/-- Check a matching component extractor over one literal field-backed DateTime shift. -/
def elaborateShiftedTimeExtractorLiteral
    (model : FlatModel) (position : TimeComponentPosition)
    (part : TimeNumericPart) (sourceField : FieldId)
    (unit : DateTimeSubdayUnit) (amount : Rat) :
    Except TimeComponentsElabError (CheckedTimeComponent model) :=
  elaborateShiftedTimeExtractor model position part sourceField unit
    (.literal amount)

/-- Check a matching component extractor over one field-backed DateTime shift whose amount is a checked direct-Number expression. -/
def elaborateShiftedTimeExtractorExpression
    (model : FlatModel) (rowGroup : GroupPath)
    (position : TimeComponentPosition) (part : TimeNumericPart)
    (sourceField : FieldId) (unit : DateTimeSubdayUnit)
    (amount : AuthoredNumericExpr SurfaceNumericAtom) :
    Except TimeComponentsElabError (CheckedTimeComponent model) := do
  let checkedAmount ←
    elaborateValueAsDateTimeExpressionShiftAmount model rowGroup amount
      |>.mapError .shifted
  elaborateShiftedTimeExtractor model position part
    sourceField unit checkedAmount

/-- Structural failure outside the reason-bearing `TimeConstructionResult` domain. -/
inductive TimeComponentsFault where
  | document (error : CheckedDocumentError)
  | payloadKind (field : FieldId)
  | stringNotConvertible (field : FieldId) (value : String)
  | nonIntegralPayload (field : FieldId) (value : Rat)
  | shifted (error : ValueAsDateTimeExtractionFault)
  deriving Repr, DecidableEq

namespace CheckedTimeNumberField

/-- Project one checked Number cell to the constructor component domain without applying arithmetic truncation or accepting a mismatched runtime payload. The classifier is placement-neutral; scalar and addressed readers supply the exact field identity. -/
def classifyTimeNumberComponent (field : FieldId)
    (observation : CellObservation Value) :
    Except TimeComponentsFault TimeConstructionComponent :=
  match observation with
  | .empty => pure .empty
  | .unknown cause | .poison cause => pure (.unavailable cause)
  | .value (.num value) =>
      if value.den = 1 then
        pure (.value value.num)
      else
        throw (.nonIntegralPayload field value)
  | .value _ => throw (.payloadKind field)

/-- Scalar specialization of the shared Number-component classifier. -/
def classify (checked : CheckedTimeNumberField model)
    (observation : CellObservation Value) :
    Except TimeComponentsFault TimeConstructionComponent :=
  classifyTimeNumberComponent checked.source.id observation

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

namespace CheckedTimeStringField

/-- Convert one already checked digit String through the existing ASCII-natural parser. Pattern and maximum-length checking happened when the document was constructed. The classifier is placement-neutral; scalar and addressed readers supply the exact field identity. -/
def classifyTimeStringComponent (field : FieldId)
    (observation : CellObservation Value) :
    Except TimeComponentsFault TimeConstructionComponent :=
  match observation with
  | .empty => pure .empty
  | .unknown cause | .poison cause => pure (.unavailable cause)
  | .value (.str value) =>
      match parseAsciiNatural? value with
      | some amount => pure (.value amount)
      | none => throw (.stringNotConvertible field value)
  | .value _ => throw (.payloadKind field)

/-- Scalar specialization of the shared String-component classifier. -/
def classify (checked : CheckedTimeStringField model)
    (observation : CellObservation Value) :
    Except TimeComponentsFault TimeConstructionComponent :=
  classifyTimeStringComponent checked.source.id observation

/-- Read one certified scalar String component through the immutable checked document. -/
def read (checked : CheckedTimeStringField model)
    (phase : Phase) (input : CheckedDocument model) :
    Except TimeComponentsFault TimeConstructionComponent := do
  let cell ← input.read {
    field := checked.source.id
    path := []
  } |>.mapError .document
  checked.classify (observeCell phase cell)

end CheckedTimeStringField

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

/-- Project a selected clock component without imposing placement. Empty temporal input follows the extractor's symmetric numeric-zero rule; formal unavailability retains its exact cause. -/
def classifyTimeExtractorComponent (field : FieldId) (kind : TemporalKind)
    (part : TimeNumericPart)
    (observation : CellObservation Value) :
    Except TimeComponentsFault TimeConstructionComponent :=
  match clockObservation? kind observation with
  | some projected =>
      componentOfNumericOperand field (part.fromTimeObservation projected)
  | none => throw (.payloadKind field)

/-- Scalar specialization of the shared temporal-extractor classifier. -/
def classify (checked : CheckedTimeExtractorField model)
    (observation : CellObservation Value) :
    Except TimeComponentsFault TimeConstructionComponent :=
  classifyTimeExtractorComponent checked.source.id checked.source.kind
    checked.part observation

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

namespace ValueAsDateTimeTimeOperand

/-- Project one reason-bearing shifted DateTime clock through the runtime extractor's numeric-zero and missingness rules. A present-but-valueless DateTime yields fixed zero; only not-given provenance makes the component empty. -/
def extractComponent (operand : ValueAsDateTimeTimeOperand)
    (part : TimeNumericPart) : TimeConstructionComponent :=
  match operand with
  | .noValue true => .empty
  | .noValue false => .value 0
  | .value _ true => .empty
  | .value time false => .value (part.extract time).num
  | .nonRelevant => .nonRelevant
  | .unavailable cause => .unavailable cause

end ValueAsDateTimeTimeOperand

namespace CheckedShiftedTimeExtractor

/-- Execute the shared checked shift before applying this extractor's exact component and reason projection. -/
def read (checked : CheckedShiftedTimeExtractor model)
    (phase : Phase) (input : CheckedDocument model) :
    Except TimeComponentsFault TimeConstructionComponent := do
  let time ← checked.source.readTime phase input |>.mapError .shifted
  pure (ValueAsDateTimeTimeOperand.extractComponent time checked.part)

end CheckedShiftedTimeExtractor

namespace CheckedTimeComponent

/-- Whether this exact checked component reads one field. Shifted extractors include their DateTime source and every checked direct-Number amount atom. -/
def referencesField (checked : CheckedTimeComponent model)
    (field : FieldId) : Bool :=
  match checked with
  | .number checked => checked.source.id == field
  | .string checked => checked.source.id == field
  | .constant _ => false
  | .extractor checked => checked.source.id == field
  | .shiftedExtractor checked =>
      checked.source.source.id == field ||
        checked.source.amount.referencesField field

/-- Execute exactly the statically selected component branch. -/
def read (checked : CheckedTimeComponent model)
    (phase : Phase) (input : CheckedDocument model) :
    Except TimeComponentsFault TimeConstructionComponent :=
  match checked with
  | .number field => field.read phase input
  | .string field => field.read phase input
  | .constant value => pure (.value value)
  | .extractor field => field.read phase input
  | .shiftedExtractor source => source.read phase input

end CheckedTimeComponent

namespace TimeComponentPrefix

/-- Whether any supplied component satisfies its carrier-specific field-reference predicate; omitted suffixes contribute no reference. -/
def referencesFieldWith (checked : TimeComponentPrefix Component)
    (referencesField : Component → FieldId → Bool)
    (field : FieldId) : Bool :=
  match checked with
  | .empty => false
  | .hour hourComponent => referencesField hourComponent field
  | .minute hourComponent minuteComponent =>
      referencesField hourComponent field ||
        referencesField minuteComponent field
  | .second hourComponent minuteComponent secondComponent =>
      referencesField hourComponent field ||
        referencesField minuteComponent field ||
        referencesField secondComponent field

/-- Evaluate one supplied prefix through its carrier-specific reader. A reached formal
    component stops before every later read; omitted trailing slots remain fixed zeroes. -/
def evaluateWith (checked : TimeComponentPrefix Component)
    (read : Component → Except Error TimeConstructionComponent) :
    Except Error TimeConstructionResult :=
  match checked with
  | .empty =>
      pure (TimeConstructionArity.zero.evaluate .empty .empty .empty)
  | .hour hourField => do
      let hourValue ← read hourField
      pure (TimeConstructionArity.hour.evaluate hourValue .empty .empty)
  | .minute hourField minuteField => do
      let hourValue ← read hourField
      match hourValue with
      | .unavailable cause => pure (.unavailable cause)
      | hourValue =>
          let minuteValue ← read minuteField
          pure (TimeConstructionArity.minute.evaluate hourValue minuteValue .empty)
  | .second hourField minuteField secondField => do
      let hourValue ← read hourField
      match hourValue with
      | .unavailable cause => pure (.unavailable cause)
      | hourValue =>
          let minuteValue ← read minuteField
          match minuteValue with
          | .unavailable cause => pure (.unavailable cause)
          | minuteValue =>
              let secondValue ← read secondField
              pure (TimeConstructionArity.second.evaluate
                hourValue minuteValue secondValue)

end TimeComponentPrefix

namespace CheckedTimeComponents

/-- Whether any supplied component reads one field; omitted suffixes contribute no reference. -/
def referencesField (checked : CheckedTimeComponents model)
    (field : FieldId) : Bool :=
  checked.referencesFieldWith CheckedTimeComponent.referencesField field

/-- Evaluate one document-only checked prefix. -/
def evaluate (checked : CheckedTimeComponents model)
    (phase : Phase) (input : CheckedDocument model) :
    Except TimeComponentsFault TimeConstructionResult :=
  checked.evaluateWith fun component => component.read phase input

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
