import A12Kernel.Elaboration.TimeComponentAdmission
import A12Kernel.Elaboration.CheckedDocument
import A12Kernel.Elaboration.ValueAsDateTimeExtraction

/-! # Partial-Date and checked `Time(...)` components

This capsule checks and executes one mixed prefix of ordinary Number fields at a bound reading scope,
pattern-backed or extensible String fields, and matching time-component extractors over ordinary Time
or DateTime fields. A bounded nonliteral extractor may instead consume the shared checked
field-backed DateTime shift. Each declaration retains its branch-specific static
certificate. Execution reads the immutable checked document in Hour/Minute/Second order
and delegates defaults and clock classification to `TimeConstructionResult`.

The String branch covers the six checker-recognized digit patterns and the client-SPI
extensible String capability. Wider recursive temporal-expression sources remain outside.
-/

namespace A12Kernel

/-- One ordinary Number field whose declaration carries the exact component certificate. -/
structure CheckedTimeNumberField (model : FlatModel) where
  scope : List RepeatableLevel := []
  position : TimeComponentPosition
  source : FlatNumberField
  admitted : model.admitsTimeNumberField position source scope = true

/-- One ordinary checked String field under the recognized digit-pattern subset. -/
structure CheckedTimeStringField (model : FlatModel) where
  scope : List RepeatableLevel := []
  position : TimeComponentPosition
  source : FlatStringField
  admitted : model.admitsTimeStringField source scope = true

/-- One scope-bound temporal field whose declared **format** exposes the extracted part, under its
    matching extraction token. Any of the three temporal kinds qualifies: the declared kind is not
    read here, so a DATE-declared field formatted `HH:mm:ss` is an admitted hour source while a
    DATE-declared complete date is refused
    ([checkpoint](../../docs/sources/computation-placement-and-constant-probes.md#src-temporal-difference-gates-read-the-format)). -/
structure CheckedTimeExtractorField (model : FlatModel) where
  scope : List RepeatableLevel := []
  position : TimeComponentPosition
  part : TimeNumericPart
  source : FlatTemporalField
  admitted : model.admitsTimeExtractorField position part source scope = true

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
    (position : TimeComponentPosition) (field : FieldId) (scope : List RepeatableLevel := []) :
    Except TimeComponentsElabError (CheckedTimeNumberField model) := do
  let declaration ←
    (model.lookupUniqueId field >>= (·.requireRepetitionBoundBy scope)) |>.mapError (.field position)
  let source ← match declaration.toNumberField? with
    | some source => pure source
    | none => throw (.numberSourceKind position field)
  if admitted : model.admitsTimeNumberField position source scope = true then
    pure { scope, position, source, admitted }
  else
    throw (.declarationNotAdmitted position field)

private def elaborateTimeStringField (model : FlatModel)
    (position : TimeComponentPosition) (field : FieldId) (scope : List RepeatableLevel := []) :
    Except TimeComponentsElabError (CheckedTimeStringField model) := do
  let declaration ←
    (model.lookupUniqueId field >>= (·.requireRepetitionBoundBy scope)) |>.mapError (.field position)
  let source ← match declaration.toStringValueField? with
    | some source => pure source
    | none => throw (.stringSourceKind position field)
  if admitted : model.admitsTimeStringField source scope = true then
    pure { scope, position, source, admitted }
  else
    throw (.declarationNotAdmitted position field)

private def elaborateTimeExtractorField (model : FlatModel)
    (position : TimeComponentPosition) (part : TimeNumericPart) (field : FieldId) (scope : List RepeatableLevel := []) :
    Except TimeComponentsElabError (CheckedTimeExtractorField model) := do
  if position.extractor != part then
    throw (.extractorMismatch position part)
  let declaration ←
    (model.lookupUniqueId field >>= (·.requireRepetitionBoundBy scope)) |>.mapError (.field position)
  let source ← match declaration.toTemporalField? with
    | some source => pure source
    | none => throw (.extractorSourceKind position field)
  if admitted : model.admitsTimeExtractorField position part source scope = true then
    pure { scope, position, part, source, admitted }
  else
    throw (.declarationNotAdmitted position field)

def elaborateTimeComponent (model : FlatModel)
    (position : TimeComponentPosition) (surface : SurfaceTimeComponent)
    (scope : List RepeatableLevel := []) : Except TimeComponentsElabError (CheckedTimeComponent model) :=
  match surface with
  | .number field =>
      .number <$> elaborateTimeNumberField model position field scope
  | .string field =>
      .string <$> elaborateTimeStringField model position field scope
  | .constant source =>
      match position.decodeConstant? source with
      | some value => pure (.constant value)
      | none => throw (.constantNotAdmitted position source)
  | .extractor part field =>
      .extractor <$> elaborateTimeExtractorField model position part field scope

/-- Check every supplied component from Hour through Second and preserve that prefix order. -/
def elaborateTimeComponents (model : FlatModel) (surface : SurfaceTimeComponents)
    (scope : List RepeatableLevel := []) :
      Except TimeComponentsElabError (CheckedTimeComponents model) :=
  match surface with
  | .empty => pure .empty
  | .hour hour => do
      pure (.hour (← elaborateTimeComponent model .hour hour scope))
  | .minute hour minute => do
      pure (.minute
        (← elaborateTimeComponent model .hour hour scope)
        (← elaborateTimeComponent model .minute minute scope))
  | .second hour minute second => do
      pure (.second
        (← elaborateTimeComponent model .hour hour scope)
        (← elaborateTimeComponent model .minute minute scope)
        (← elaborateTimeComponent model .second second scope))

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

/-- Conversion failure or incoherent host input, kept outside `TimeConstructionResult`. A reached `stringNotConvertible` is a runtime failure under spec/05 §3. -/
inductive TimeComponentsFault where
  | document (error : CheckedDocumentError)
  | payloadKind (field : FieldId)
  | stringNotConvertible (field : FieldId) (value : String)
  | nonIntegralPayload (field : FieldId) (value : Rat)
  | shifted (error : ValueAsDateTimeExtractionFault)
  deriving Repr, DecidableEq

def TimeConstructionInputFault.toCheckedFault : TimeConstructionInputFault → TimeComponentsFault
  | .payloadKind field => .payloadKind field
  | .stringNotConvertible field value => .stringNotConvertible field value
  | .nonIntegralPayload field value => .nonIntegralPayload field value

namespace CheckedTimeNumberField

def classifyTimeNumberComponent (field : FieldId)
    (observation : CellObservation Value) :
    Except TimeComponentsFault TimeConstructionComponent :=
  (A12Kernel.classifyTimeNumberComponent field observation).mapError TimeConstructionInputFault.toCheckedFault

/-- Scope-bound specialization of the shared Number-component classifier. -/
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

def classifyTimeStringComponent (field : FieldId)
    (observation : CellObservation Value) :
    Except TimeComponentsFault TimeConstructionComponent :=
  (A12Kernel.classifyTimeStringComponent field observation).mapError TimeConstructionInputFault.toCheckedFault

/-- Scope-bound specialization of the shared String-component classifier. -/
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

def classifyTimeExtractorComponent (field : FieldId)
    (part : TimeNumericPart)
    (observation : CellObservation Value) :
    Except TimeComponentsFault TimeConstructionComponent :=
  (A12Kernel.classifyTimeExtractorComponent field part observation).mapError TimeConstructionInputFault.toCheckedFault

/-- Scope-bound specialization of the shared temporal-extractor classifier. -/
def classify (checked : CheckedTimeExtractorField model)
    (observation : CellObservation Value) :
    Except TimeComponentsFault TimeConstructionComponent :=
  classifyTimeExtractorComponent checked.source.id checked.part observation

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

/-- Exact authored-order field dependencies of one checked component. -/
def fieldDependencies : CheckedTimeComponent model → List FieldId
  | .number checked => [checked.source.id]
  | .string checked => [checked.source.id]
  | .constant _ => []
  | .extractor checked => [checked.source.id]
  | .shiftedExtractor checked =>
      checked.source.source.id :: checked.source.amount.fieldDependencies

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



namespace CheckedTimeComponents

/-- Whether any supplied component reads one field; omitted suffixes contribute no reference. -/
def referencesField (checked : CheckedTimeComponents model)
    (field : FieldId) : Bool :=
  checked.referencesFieldWith CheckedTimeComponent.referencesField field

/-- Evaluate one document-only checked prefix. -/
def evaluate (checked : CheckedTimeComponents model)
    (phase : Phase) (input : CheckedDocument model) :
    Except TimeComponentsFault TimeConstructionResult :=
  checked.evaluateWith (fun component => component.read phase input) phase

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
