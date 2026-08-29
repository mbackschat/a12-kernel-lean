import A12Kernel.Elaboration.CheckedIndexColumn
import A12Kernel.Elaboration.ComputationFormalInput
import A12Kernel.Elaboration.DateRangeConstructionComputation
import A12Kernel.Elaboration.TemporalComputationResult

/-! # Checked String-keyed DateRange construction computation

This capsule admits two exact full-Date fields selected by literal or direct nonrepeatable evaluated String semantic-index keys in one direct one-level repeatable group. It reuses the immutable checked document, generated preliminary column, shared semantic-index poison policy, positional Date completion, and direct DateRange target renderer. Fragments, nested or cross-group indices, comparisons, and wider target placement remain separate.
-/

namespace A12Kernel

inductive IndexedDateRangeEndpointKey where
  | literal (value : String)
  | field (field : FieldId)
  deriving Repr, DecidableEq

instance : Coe String IndexedDateRangeEndpointKey :=
  ⟨IndexedDateRangeEndpointKey.literal⟩

inductive CheckedIndexedDateRangeEndpointKey where
  | literal (value : String)
  | field (source : FlatStringField)
  deriving Repr, DecidableEq

namespace CheckedIndexedDateRangeEndpointKey

/-- A dynamic key is owned only when it is the exact direct evaluated String declaration in the checked model. -/
def admittedBy (key : CheckedIndexedDateRangeEndpointKey)
    (model : FlatModel) : Bool :=
  match key with
  | .literal _ => true
  | .field source => model.admitsStringValueField source

end CheckedIndexedDateRangeEndpointKey

inductive IndexedDateRangeEndpointElabError where
  | resolve (cause : ResolveError)
  | missingIndexField (group : GroupPath)
  | indexNotString (path : List String)
  | targetNotDate (field : FieldId)
  | unsupportedComponents (field : FieldId) (actual : TemporalComponents)
  | targetPolicyUnavailable (field : FieldId)
  | unsupportedPolicy (field : FieldId) (mode : TemporalPartialMode)
      (format : String)
  | unsupportedZone (zoneId : String)
  | nestedScope (field : FieldId) (scope : List RepeatableLevel)
  | keyNotEvaluatedString (path : List String)
  | incoherentKey
  deriving Repr, DecidableEq

/-- One exact Date declaration selected through its containing one-level String index. The private constructor keeps the model-derived group, declaration policy, and zone profile inseparable. -/
structure CheckedIndexedDateRangeEndpoint (model : FlatModel) where
  private mk ::
  group : RepeatableGroupDecl
  indexDeclaration : FlatFieldDecl
  targetDeclaration : FlatFieldDecl
  target : FlatTemporalField
  format : FullDateTargetFormat
  profile : ModelZone.ConcreteProfile
  key : CheckedIndexedDateRangeEndpointKey
  keyOwned : key.admittedBy model = true

/-- Certify one direct one-level String-indexed full-Date endpoint. -/
private def elaborateIndexedDateRangeEndpoint (model : FlatModel)
    (field : FieldId) (key : IndexedDateRangeEndpointKey) :
    Except IndexedDateRangeEndpointElabError
      (CheckedIndexedDateRangeEndpoint model) := do
  model.validate |>.mapError .resolve
  let declaration ← model.lookupUniqueId field |>.mapError .resolve
  let group ← model.lookupUniqueRepeatablePath declaration.groupPath
    |>.mapError .resolve
  if declaration.repeatableScope != [group.level] then
    throw (.nestedScope field declaration.repeatableScope)
  let indexId ← match group.indexField with
    | some indexId => pure indexId
    | none => throw (.missingIndexField group.path)
  let indexDeclaration ← model.lookupUniqueId indexId |>.mapError .resolve
  if indexDeclaration.policy.kind != .string then
    throw (.indexNotString indexDeclaration.path)
  let target ← match declaration.toTemporalField? with
    | some target => pure target
    | none => throw (.targetNotDate field)
  if target.kind != .date then
    throw (.targetNotDate field)
  if target.components != TemporalComponents.fullDate then
    throw (.unsupportedComponents field target.components)
  let policy ← match declaration.toTemporalTargetPolicy? with
    | some policy => pure policy
    | none => throw (.targetPolicyUnavailable field)
  if policy.partialMode != .full then
    throw (.unsupportedPolicy field policy.partialMode policy.format)
  let format ← match FullDateTargetFormat.ofSource? policy.format with
    | some format => pure format
    | none => throw (.unsupportedPolicy field policy.partialMode policy.format)
  let profile ← match ModelZone.ConcreteProfile.ofId? model.timeZoneId with
    | some profile => pure profile
    | none => throw (.unsupportedZone model.timeZoneId)
  let checkedKey ← match key with
    | .literal value => pure (.literal value)
    | .field keyField =>
        let keyDeclaration ← model.resolveNonrepeatableDeclarationById keyField
          |>.mapError .resolve
        match keyDeclaration.toStringValueField? with
        | some source => pure (.field source)
        | none => throw (.keyNotEvaluatedString keyDeclaration.path)
  if hKey : checkedKey.admittedBy model = true then
    pure {
      group
      indexDeclaration
      targetDeclaration := declaration
      target
      format
      profile
      key := checkedKey
      keyOwned := hKey
    }
  else
    throw .incoherentKey

inductive IndexedDateRangeConstructionComputationElabError where
  | start (cause : IndexedDateRangeEndpointElabError)
  | finish (cause : IndexedDateRangeEndpointElabError)
  | differentGroups (start finish : GroupPath)
  | target (cause : DirectDateRangeElabError)
  | targetFormat (source : FullDateTargetFormat) (target : DateRangeInputFormat)
  | incoherentCore
  deriving Repr, DecidableEq

/-- Two literal- or direct-field-keyed Date endpoints and one matching direct DateRange target, all certified against the same model. -/
structure CheckedIndexedDateRangeConstructionComputation (model : FlatModel) where
  start : CheckedIndexedDateRangeEndpoint model
  finish : CheckedIndexedDateRangeEndpoint model
  sameGroup : start.group = finish.group
  target : CheckedDirectDateRange model
  declaringGroup : GroupPath
  /-- The declaring group is a representable path; placement itself is unconstrained. See the
  sibling certificate in [`DateRangeConstructionComputation.lean`](DateRangeConstructionComputation.lean). -/
  declaringGroupValid : GroupPath.isValid declaringGroup = true
  format : DateRangeConstructionTargetFormat
  profileOwned : DateRangeConstructionTargetFormat.ofProfiles?
    (.full start.format) target.format = some format

/-- Admit the measured same-indexed-group exact-Date construction and direct target profile. -/
def elaborateIndexedDateRangeConstructionComputation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (startField : FieldId) (startKey : IndexedDateRangeEndpointKey)
    (finishField : FieldId) (finishKey : IndexedDateRangeEndpointKey) :
    Except IndexedDateRangeConstructionComputationElabError
      (CheckedIndexedDateRangeConstructionComputation model) := do
  let start ← elaborateIndexedDateRangeEndpoint model startField startKey
    |>.mapError .start
  let finish ← elaborateIndexedDateRangeEndpoint model finishField finishKey
    |>.mapError .finish
  if hSame : start.group = finish.group then
    -- Resolved for its refusal, not its result. No placement test follows, only the group-validity
    -- check the removed equality test used to imply.
    let _ ← model.resolveNonrepeatableDeclarationById targetField
      |>.mapError (fun error => .target (.source error))
    let target ← elaborateDirectDateRange model targetField |>.mapError .target
    if hValid : GroupPath.isValid declaringGroup = true then
      match hFormat : DateRangeConstructionTargetFormat.ofProfiles?
          (.full start.format) target.format with
      | some format => pure {
          start
          finish
          sameGroup := hSame
          target
          declaringGroup
          declaringGroupValid := hValid
          format
          profileOwned := hFormat
        }
      | none => throw (.targetFormat start.format target.format)
    else
      throw (.target (.source (.invalidRuleGroup declaringGroup)))
  else
    throw (.differentGroups start.group.path finish.group.path)

/-- Runtime evidence for a literal key or one direct evaluated String key-field observation. -/
inductive IndexedDateRangeEndpointKeyObservation where
  | literal (value : String)
  | field (source : FlatStringField) (value : CellObservation String)
  deriving Repr, DecidableEq

namespace IndexedDateRangeEndpointKeyObservation

def value : IndexedDateRangeEndpointKeyObservation → CellObservation String
  | .literal value => .value value
  | .field _ value => value

def selectableToken? (key : IndexedDateRangeEndpointKeyObservation) : Option String :=
  match key.value with
  | .value value => if value.isEmpty then none else some value
  | .empty | .unknown _ | .poison _ => none

end IndexedDateRangeEndpointKeyObservation

/-- Runtime evidence for one keyed endpoint: the authored or observed key, selected physical address when selection succeeded, and the typed endpoint observation. -/
structure IndexedDateRangeEndpointObservation where
  key : IndexedDateRangeEndpointKeyObservation
  address : Option CellAddr
  value : CellObservation DateRangeConstructionEndpointValue
  deriving Repr, DecidableEq

inductive IndexedDateRangeConstructionComputationFault where
  | column (cause : CheckedIndexColumnError)
  | endpoint (cause : DateRangeConstructionFault)
  | target (cause : DateRangeTargetEvaluationFault)
  deriving Repr, DecidableEq

/-- Failure while composing one checked indexed DateRange construction's complete formal-input preparation with its existing rich result boundary. -/
inductive IndexedDateRangeConstructionFormalInputFault where
  | formalInput (cause : ComputationFormalInputPlanError)
  | preliminary (cause : CheckedIndexPreliminaryError)
  | execution (formalErrorsInOperands : List ComputationFormalInputFinding)
      (cause : IndexedDateRangeConstructionComputationFault)
  deriving Repr, DecidableEq

/-- Rich execution result retaining both keyed endpoint selections beside the typed target outcome. -/
structure IndexedDateRangeConstructionComputationResult where
  start : IndexedDateRangeEndpointObservation
  finish : IndexedDateRangeEndpointObservation
  outcome : DateRangeTargetOutcome
  deriving Repr, DecidableEq

namespace CheckedIndexedDateRangeConstructionComputation

def referencesEndpointField
    (operation : CheckedIndexedDateRangeConstructionComputation model)
    (field : FieldId) : Bool :=
  operation.start.target.id == field || operation.finish.target.id == field

def referencesKeyField
    (operation : CheckedIndexedDateRangeConstructionComputation model)
    (field : FieldId) : Bool :=
  (match operation.start.key with
    | .literal _ => false
    | .field source => source.id == field) ||
  (match operation.finish.key with
    | .literal _ => false
    | .field source => source.id == field)

def referencesIndexField
    (operation : CheckedIndexedDateRangeConstructionComputation model)
    (field : FieldId) : Bool :=
  operation.start.indexDeclaration.id == field

/-- Model-declaration-ordered full-Date endpoint dependencies. -/
def endpointFieldDependencies
    (operation : CheckedIndexedDateRangeConstructionComputation model) :
    List FieldId :=
  (model.fields.filter fun declaration =>
    operation.referencesEndpointField declaration.id).map (·.id)

/-- Model-declaration-ordered dynamic selector dependencies; literal keys contribute no field. -/
def keyFieldDependencies
    (operation : CheckedIndexedDateRangeConstructionComputation model) :
    List FieldId :=
  (model.fields.filter fun declaration =>
    operation.referencesKeyField declaration.id).map (·.id)

/-- The model-declaration-ordered semantic-index column consumed by both checked endpoint selections. -/
def indexFieldDependencies
    (operation : CheckedIndexedDateRangeConstructionComputation model) :
    List FieldId :=
  (model.fields.filter fun declaration =>
    operation.referencesIndexField declaration.id).map (·.id)

/-- The model-declaration-ordered union of endpoint, dynamic-key, and implicit index dependencies. -/
def formalInputFields
    (operation : CheckedIndexedDateRangeConstructionComputation model) :
    List FieldId :=
  (model.fields.filter fun declaration =>
    operation.referencesEndpointField declaration.id ||
      operation.referencesKeyField declaration.id ||
      operation.referencesIndexField declaration.id).map (·.id)

/-- Bind endpoint, dynamic-key, and implicit index dependencies to the shared target-excluding formal-input plan. -/
def formalInputPlan
    (operation : CheckedIndexedDateRangeConstructionComputation model) :
    Except ComputationFormalInputPlanError
      (CheckedComputationFormalInputPlan model) :=
  checkComputationFormalInputPlan model
    operation.formalInputFields
    [operation.target.source.id]

private def stringKeyObservation : CellObservation → CellObservation String
  | .empty => .empty
  | .value (.str value) => .value value
  | .value _ => .poison .malformed
  | .unknown cause => .unknown cause
  | .poison cause => .poison cause

private def observeKey
    (key : CheckedIndexedDateRangeEndpointKey)
    (input : CheckedDocument model) :
    Except CheckedDocumentError IndexedDateRangeEndpointKeyObservation :=
  match key with
  | .literal value => pure (.literal value)
  | .field source => do
      let cell ← input.read { field := source.id, path := [] }
      pure (.field source (stringKeyObservation (observeCell .computation cell)))

private def evaluateEndpoint (endpoint : CheckedIndexedDateRangeEndpoint model)
    (bound : DateRangeBound) (column : ResolvedCheckedIndexColumn model)
    (preliminary : CheckedIndexPreliminary model) :
    Except IndexedDateRangeConstructionComputationFault
      IndexedDateRangeEndpointObservation := do
  let resolved ← column.toSemanticIndexColumn preliminary endpoint.target.id
    |>.mapError .column
  let key ← observeKey endpoint.key preliminary.base
    |>.mapError (fun error => .column (.document error))
  let address ← if column.unavailableKey.isSome then
      pure none
    else
      match key.selectableToken? with
      | none => pure none
      | some token =>
          match column.selectableEntryFor? (.text token) with
          | none => pure none
          | some entry => do
              let path ← entry.environment.pathForScope
                endpoint.targetDeclaration.repeatableScope
                |>.mapError (fun error => .column (.environment error))
              pure (some { field := endpoint.target.id, path })
  let value ← DateRangeEndpointFormat.evaluateObservation (.full endpoint.format)
      endpoint.profile endpoint.target.id bound
      (resolved.lookupTextObservation .computation key.value)
    |>.mapError .endpoint
  pure { key, address, value }

/-- Execute both indexed reads against one generated preliminary column, then reuse the established DateRange result and target policy. -/
def execute (operation : CheckedIndexedDateRangeConstructionComputation model)
    (preliminary : CheckedIndexPreliminary model) :
    Except IndexedDateRangeConstructionComputationFault
      IndexedDateRangeConstructionComputationResult := do
  let column ← preliminary.resolveIndexColumn operation.start.group
    |>.mapError .column
  let start ← evaluateEndpoint operation.start .start column preliminary
  let finish ← evaluateEndpoint operation.finish .finish column preliminary
  let construction : DateRangeConstructionObservation := {
    start := start.value, finish := finish.value }
  let outcome ← operation.format.evaluateComputationResult
      construction.asComputationResult |>.mapError .target
  pure { start, finish, outcome }

/-- Execute and classify one rich indexed-construction outcome against the immutable checked document underlying its preliminary index. Key and address observations remain available from `execute`; this projection reuses the shared DateRange result carrier. -/
def executeResult
    (operation : CheckedIndexedDateRangeConstructionComputation model)
    (preliminary : CheckedIndexPreliminary model)
    (residualMessages : List ResidualMessage) :
    Except IndexedDateRangeConstructionComputationFault
      (DateRangeComputationRunView ResidualMessage) := do
  let result ← operation.execute preliminary
  pure (DateRangeComputationRunView.fromOutcomes preliminary.base
    residualMessages [(operation.target.source.id, result.outcome)])

/-- Prepare selected cached and generated inputs once, execute against that same preliminary view, and place the eager inventory in the existing DateRange residual channel. -/
def executeResultWithFormalInputs
    (operation : CheckedIndexedDateRangeConstructionComputation model)
    (input : CheckedDocument model) :
    Except IndexedDateRangeConstructionFormalInputFault
      (DateRangeComputationRunView ComputationFormalInputFinding) := do
  let plan ← operation.formalInputPlan |>.mapError .formalInput
  let prepared ← plan.prepare input |>.mapError .preliminary
  match operation.executeResult prepared.preliminary
      prepared.formalErrorsInOperands with
  | .error cause =>
      .error (.execution prepared.formalErrorsInOperands cause)
  | .ok result => .ok result

end CheckedIndexedDateRangeConstructionComputation

end A12Kernel
