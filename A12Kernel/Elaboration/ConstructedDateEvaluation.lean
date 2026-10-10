import A12Kernel.Elaboration.CheckedDocument
import A12Kernel.Semantics.LegacyCalendarExpression
import A12Kernel.Elaboration.ConstructedDateComponents
import A12Kernel.Semantics.BaseYearDateSource
import A12Kernel.Semantics.ConstructedDateDay
import A12Kernel.Semantics.DateTimeComparison

/-! # Checked constructed-Date component execution

This capsule evaluates one certified direct constructed Date in generated component order. Number fields, pattern-backed or extensible String fields, the complete-Year `yyyy` Date field, and direct Date/DateTime extractors read the immutable checked document; constants and direct/range-selected Base-Year extractors are fixed inputs; and `Today`/`Now` resolve only from the execution's explicit optional `World`. The two-argument form uses the model Base Year, and the four-argument form reads Century before Short-Year and combines them only when both are present. It wraps the existing cause-free construction result only to retain the first reached formal cause. UTC/GMT and pinned Berlin resolve the legacy-hybrid label without imposing the later stored-Date floor.

Exact formal causes and missing provenance remain distinguishable. A fresh real result resolves once under the selected profile and projects that exact instant into the shared temporal comparison domain. Checked shifts and differences have their own execution owners in `ConstructedDateShiftEvaluation` and `ConstructedDateDifferenceEvaluation`. General recursive extractor operands and additional zone profiles remain outside these source certificates. Snapshot readers require nonrepeatable fields; `CheckedConstructedDateSource.readWith` lets temporal expressions and computation guards supply the target-row and completed-producer reads required by spec/09 §5.
-/

namespace A12Kernel

/-- Conversion failure or incoherent host input, kept outside Date value and formal-state semantics. A reached `stringNotConvertible` is a runtime failure under spec/05 §3. -/
inductive ConstructedDateEvaluationFault where
  | document (error : CheckedDocumentError)
  | payloadKind (field : FieldId)
  | stringNotConvertible (field : FieldId) (value : String)
  | dateYearStoredMissing (field : FieldId)
  | dateYearNotConvertible (field : FieldId) (value : String)
  | nonIntegralPayload (field : FieldId) (value : Rat)
  | todayWorldRequired
  | todayUnavailable (zoneId : String)
  | nowWorldRequired
  | nowUnavailable (zoneId : String)
  | profileDateUnsupported (zoneId : String) (parts : DateParts)
  deriving Repr, DecidableEq

def ConstructedDateComponentFault.toEvaluationFault : ConstructedDateComponentFault → ConstructedDateEvaluationFault
  | .payloadKind field => .payloadKind field
  | .stringNotConvertible field value => .stringNotConvertible field value
  | .dateYearStoredMissing field => .dateYearStoredMissing field
  | .dateYearNotConvertible field value => .dateYearNotConvertible field value
  | .nonIntegralPayload field value => .nonIntegralPayload field value
  | .todayWorldRequired => .todayWorldRequired
  | .todayUnavailable zone => .todayUnavailable zone
  | .nowWorldRequired => .nowWorldRequired
  | .nowUnavailable zone => .nowUnavailable zone
  | .profileDateUnsupported zone parts => .profileDateUnsupported zone parts

namespace CheckedConstructedDateNumberField

/-- Preserve empty and formal state while rejecting a forged fractional or non-Number payload. -/
def classify (checked : CheckedConstructedDateNumberField model)
    (observation : CellObservation Value) :
    Except ConstructedDateEvaluationFault CheckedConstructedDateComponent :=
  (classifyConstructedDateNumber checked.source observation).mapError ConstructedDateComponentFault.toEvaluationFault

/-- Read one certified scalar component through the immutable checked document. -/
def read (checked : CheckedConstructedDateNumberField model)
    (phase : Phase) (input : CheckedDocument model) :
    Except ConstructedDateEvaluationFault CheckedConstructedDateComponent := do
  let cell ← input.read {
    field := checked.source.id
    path := []
  } |>.mapError .document
  checked.classify (observeCell phase cell)

end CheckedConstructedDateNumberField

namespace CheckedConstructedDateStringField

/-- Convert one already checked digit String through the bounded host-decimal conversion while preserving empty and formal state. -/
def classify (checked : CheckedConstructedDateStringField model)
    (observation : CellObservation Value) :
    Except ConstructedDateEvaluationFault CheckedConstructedDateComponent :=
  (classifyConstructedDateString checked.source observation).mapError ConstructedDateComponentFault.toEvaluationFault

/-- Read one certified scalar String component through the immutable checked document. -/
def read (checked : CheckedConstructedDateStringField model)
    (phase : Phase) (input : CheckedDocument model) :
    Except ConstructedDateEvaluationFault CheckedConstructedDateComponent := do
  let cell ← input.read {
    field := checked.source.id
    path := []
  } |>.mapError .document
  checked.classify (observeCell phase cell)

end CheckedConstructedDateStringField

namespace CheckedConstructedDateYearField

/-- Convert the exact stored `yyyy` text while using the checked cell only for empty, formal, and payload-kind state. This is intentionally distinct from `YearFromDate`, which projects the decoded temporal value. -/
def classify (checked : CheckedConstructedDateYearField model)
    (observation : CellObservation Value) (stored : Option String) :
    Except ConstructedDateEvaluationFault CheckedConstructedDateComponent :=
  (classifyConstructedDateYear checked.source observation stored).mapError ConstructedDateComponentFault.toEvaluationFault

/-- Read one certified `yyyy` Date component from the immutable checked cell and its retained exact stored text. -/
def read (checked : CheckedConstructedDateYearField model)
    (phase : Phase) (input : CheckedDocument model) :
    Except ConstructedDateEvaluationFault CheckedConstructedDateComponent := do
  let address : CellAddr := {
    field := checked.source.id
    path := []
  }
  let cell ← input.read address |>.mapError .document
  checked.classify (observeCell phase cell)
    (input.storedTextAt address)

end CheckedConstructedDateYearField

namespace CheckedConstructedDateExtractorField

/-- Preserve empty and formal state while projecting the certified calendar component from a Date or
DateTime payload. The payload is held by its format's family, not the declared kind, as every flat
temporal read tests it ([`FlatTemporalField.holdsValue`](../Semantics/FlatValidation.lean)). -/
def classify (checked : CheckedConstructedDateExtractorField model)
    (observation : CellObservation Value) :
    Except ConstructedDateEvaluationFault CheckedConstructedDateComponent :=
  (classifyConstructedDateExtractor checked.source checked.part observation
    (model.temporalNumericPartialFormat checked.source.id)).mapError ConstructedDateComponentFault.toEvaluationFault

/-- Read one certified scalar Date component through the immutable checked document. -/
def read (checked : CheckedConstructedDateExtractorField model)
    (phase : Phase) (input : CheckedDocument model) :
    Except ConstructedDateEvaluationFault CheckedConstructedDateComponent := do
  let cell ← input.read {
    field := checked.source.id
    path := []
  } |>.mapError .document
  checked.classify (observeCell phase cell)

end CheckedConstructedDateExtractorField

namespace CheckedConstructedDateBaseYearExtractor

/-- Project the matching component from the configured direct or range-selected Base-Year Date source without consulting document state. `baseYearDateSourceNumericPart` owns that source interpretation; its normalized rational numerator is exact for every admitted component. -/
def read (checked : CheckedConstructedDateBaseYearExtractor model)
    (_phase : Phase) (_input : CheckedDocument model) :
    Except ConstructedDateEvaluationFault CheckedConstructedDateComponent :=
  pure (.value
    (baseYearDateSourceNumericPart
      checked.year checked.source checked.part).num)

end CheckedConstructedDateBaseYearExtractor

namespace CheckedConstructedDatePointInTimeExtractor

/-- Decode one exact instant through the certified profile and project the selected Date
    component, preserving the acquisition-specific structural fault. -/
def project
    (checked : CheckedConstructedDatePointInTimeExtractor model)
    (instant : Instant) (unavailable : ConstructedDateEvaluationFault) :
    Except ConstructedDateEvaluationFault CheckedConstructedDateComponent :=
  match checked.profile.localDate? instant with
  | none => throw unavailable
  | some date =>
      pure (.value (checked.part.extract date.civil.parts).num)

/-- Resolve the selected point in time from the supplied execution world, then project
    the matching local calendar component through the model-certified zone profile.
    `Today` asks the world for model-zone midnight; `Now` keeps its exact instant. -/
def read (checked : CheckedConstructedDatePointInTimeExtractor model)
    (world : Option World) :
    Except ConstructedDateEvaluationFault CheckedConstructedDateComponent :=
  (readConstructedDateClock checked.point checked.part model.timeZoneId checked.profile world).mapError
    ConstructedDateComponentFault.toEvaluationFault

end CheckedConstructedDatePointInTimeExtractor

namespace CheckedConstructedDateSource

/-- Read one component with the caller's explicit optional execution world. -/
def read (checked : CheckedConstructedDateSource model)
    (phase : Phase) (input : CheckedDocument model)
    (world : Option World) :
    Except ConstructedDateEvaluationFault CheckedConstructedDateComponent :=
  match checked with
  | .numberField source => source.read phase input
  | .stringField source => source.read phase input
  | .dateYearField source => source.read phase input
  | .constant value => pure (.value value)
  | .extractor source => source.read phase input
  | .baseYearExtractor source => source.read phase input
  | .pointInTimeExtractor source => source.read world

/-- Use the caller's row and phase readers without replacing computed cells or their stored text with the input snapshot (spec/09 §5). -/
def readWith (source : CheckedConstructedDateSource model) (phase : Phase)
    (readCell : FieldId → CheckedCell) (storedText : FieldId → Option String) (world : Option World) :
    Except ConstructedDateEvaluationFault CheckedConstructedDateComponent :=
  match source with
  | .numberField checked => checked.classify (observeCell phase (readCell checked.source.id))
  | .stringField checked => checked.classify (observeCell phase (readCell checked.source.id))
  | .dateYearField checked => checked.classify (observeCell phase (readCell checked.source.id))
      (storedText checked.source.id)
  | .constant value => pure (.value value)
  | .extractor checked => checked.classify (observeCell phase (readCell checked.source.id))
  | .baseYearExtractor checked => pure (.value
      (baseYearDateSourceNumericPart checked.year checked.source checked.part).num)
  | .pointInTimeExtractor checked => checked.read world

end CheckedConstructedDateSource

namespace CheckedConstructedDateYear

/-- Read one checked year form with the caller's explicit optional world. Split-year evaluation preserves Century-before-Short-Year formal precedence, while any ordinary empty component keeps the construction incomplete. -/
def readWith [Monad m] (checked : CheckedConstructedDateYear model Source)
    (readSource : Source → m CheckedConstructedDateComponent)
    (phase : Phase := .computation) : m CheckedConstructedDateComponent :=
  checked.resolved.readWith readSource phase

def read (checked : CheckedConstructedDateYear model)
    (phase : Phase) (input : CheckedDocument model) (world : Option World) :
    Except ConstructedDateEvaluationFault CheckedConstructedDateComponent :=
  checked.readWith (fun source => source.read phase input world) phase

end CheckedConstructedDateYear

namespace CheckedConstructedDateComponents

/-- Resolve one real constructed Date exactly as its fresh model-zone parse does.
    Exact consumers retain this instant instead of reducing the value to calendar
    parts and resolving it again at a later boundary. -/
def resolveFreshInstant (checked : CheckedConstructedDateComponents model Source)
    (parts : DateParts) : Except ConstructedDateEvaluationFault (Option Instant) :=
  pure (checked.resolved.resolveFreshInstant parts)

/-- Decide whether one already hybrid-real Date also exists at local midnight in the
    selected profile. The calendar label remains independent of the stored-Date floor,
    which only a later target may apply (calendar boundary grid, 2026-10-04). -/
def profileAcceptsDate (checked : CheckedConstructedDateComponents model Source)
    (parts : DateParts) :
    Except ConstructedDateEvaluationFault Bool := do
  pure (← checked.resolveFreshInstant parts).isSome

/-- Apply the selected profile's local-midnight reality without changing incomplete,
    already-unreal, or formally unavailable construction results. -/
def applyProfileReality (checked : CheckedConstructedDateComponents model Source) :
    ConstructedDateObservation →
      Except ConstructedDateEvaluationFault ConstructedDateObservation
  | .resolved (.real parts) => do
      if ← checked.profileAcceptsDate parts then
        pure (.resolved (.real parts))
      else
        pure (.resolved .unreal)
  | observation => pure observation

/-- Read Day, Month, and Year in generated argument order before applying a profile
    consumer. Computation stops on formal poison; validation evaluates later arguments, whose
    conversion may still throw, before retaining the first formal cause (spec/05 §3). -/
def evaluateComponentsWith [Monad m] (checked : CheckedConstructedDateComponents model Source)
    (readSource : Source → m CheckedConstructedDateComponent)
    (phase : Phase := .computation) : m ConstructedDateObservation :=
  checked.resolved.evaluateComponentsWith readSource phase

def evaluateComponents (checked : CheckedConstructedDateComponents model)
    (phase : Phase) (input : CheckedDocument model) (world : Option World) :
    Except ConstructedDateEvaluationFault ConstructedDateObservation :=
  checked.evaluateComponentsWith (fun source => source.read phase input world) phase

/-- Evaluate checked components and apply the selected profile's local-midnight
    reality for validity and component consumers. -/
def evaluate (checked : CheckedConstructedDateComponents model)
    (phase : Phase) (input : CheckedDocument model)
    (world : Option World) :
    Except ConstructedDateEvaluationFault ConstructedDateObservation := do
  checked.applyProfileReality
    (← checked.evaluateComponents phase input world)

/-- Finish one constructed observation at the shared exact value boundary. A real local
    label is resolved exactly once here; later comparison, shift, and difference
    consumers receive that retained instant rather than resolving `parts` again. -/
def finishValue (checked : CheckedConstructedDateComponents model Source)
    (observation : ConstructedDateObservation) : Except ConstructedDateEvaluationFault ConstructedDateValue :=
  pure (checked.resolved.finishValue observation)

def evaluateValueWith (checked : CheckedConstructedDateComponents model Source)
    (readSource : Source → Except ConstructedDateEvaluationFault CheckedConstructedDateComponent)
    (phase : Phase := .computation) :
    Except ConstructedDateEvaluationFault ConstructedDateValue := do
  checked.finishValue (← checked.evaluateComponentsWith readSource phase)

def evaluateValue (checked : CheckedConstructedDateComponents model)
    (phase : Phase) (input : CheckedDocument model) (world : Option World) :
    Except ConstructedDateEvaluationFault ConstructedDateValue :=
  checked.evaluateValueWith (fun source => source.read phase input world) phase

/-- Evaluate checked `Valid(Date(...))` with one explicit optional world, keeping document faults and formal causes in their separate channels. -/
def evaluateValid (checked : CheckedConstructedDateComponents model)
    (phase : Phase) (input : CheckedDocument model) (world : Option World) :
    Except ConstructedDateEvaluationFault (Except FormalCause Verdict) :=
  (checked.evaluate phase input world).map
    ConstructedDateObservation.validVerdict

/-- Evaluate checked `Invalid(Date(...))` with one explicit optional world, keeping document faults and formal causes in their separate channels. -/
def evaluateInvalid (checked : CheckedConstructedDateComponents model)
    (phase : Phase) (input : CheckedDocument model) (world : Option World) :
    Except ConstructedDateEvaluationFault (Except FormalCause Verdict) :=
  (checked.evaluate phase input world).map
    ConstructedDateObservation.invalidVerdict

/-- Evaluate one checked Day/Month/Quarter/Year projection with one explicit optional world without adding another numeric result family. -/
def evaluateNumericPart (checked : CheckedConstructedDateComponents model)
    (part : DateNumericPart) (phase : Phase)
    (input : CheckedDocument model) (world : Option World) :
    Except ConstructedDateEvaluationFault
      (Except FormalCause ConstructedDateNumericResult) :=
  (checked.evaluate phase input world).map fun observation =>
    observation.numericPart part

end CheckedConstructedDateComponents

end A12Kernel
