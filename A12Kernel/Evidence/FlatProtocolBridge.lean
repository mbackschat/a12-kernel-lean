import A12Kernel.Evidence.Replay
import A12Kernel.Reference.Evaluator
import A12Kernel.Reference.StrictJson

/-! # A12Kernel.Evidence.FlatProtocolBridge — retained flat evidence to protocol

This evidence-only module owns the typed descriptor for the first cold-implementation
capability and mechanically binds its retained projection to normalized protocol requests.
It remains outside the library, conformance, and proof roots.
-/

namespace A12Kernel.Evidence.FlatProtocolBridge

open Lean
open A12Kernel
open A12Kernel.Reference

inductive FocusedAuthoredObservation where
  | firedValue
  | firedOmission
  | silent
  deriving Repr, DecidableEq

inductive ExternalSupport where
  | verdictFiringAndPolarity
  | verdictSuppressionOnly
  deriving Repr, DecidableEq

namespace ExternalSupport

def tag : ExternalSupport → String
  | .verdictFiringAndPolarity => "verdictFiringAndPolarity"
  | .verdictSuppressionOnly => "verdictSuppressionOnly"

end ExternalSupport

inductive ExpectedResponseSource where
  | retainedProjection
  | leanRuntimeProjection
  deriving Repr, DecidableEq

namespace ExpectedResponseSource

def tag : ExpectedResponseSource → String
  | .retainedProjection => "retainedProjection"
  | .leanRuntimeProjection => "leanRuntimeProjection"

end ExpectedResponseSource

structure CaseDescriptor where
  id : String
  expectedVerdict : Verdict
  covers : List String
  deriving Repr, DecidableEq

structure CapabilityDescriptor where
  id : String
  referenceSemanticsVersion : String
  protocolVersion : Nat
  manifestSchemaVersion : Nat
  kernelBehaviorVersion : String
  operation : String
  supportManifest : System.FilePath
  evidenceRoot : System.FilePath
  projection : System.FilePath
  fixtureDirectory : System.FilePath
  cases : List CaseDescriptor
  deriving Repr, DecidableEq

def capability : CapabilityDescriptor := {
  id := "flat-validation-empty-logic-v1"
  referenceSemanticsVersion := Support.referenceSemanticsVersion
  protocolVersion := Support.protocolVersion
  manifestSchemaVersion := Support.manifestSchemaVersion
  kernelBehaviorVersion := Support.kernelBehaviorVersion
  operation := Support.Operation.flatValidationEvaluateFull.tag
  supportManifest := "reference/supported-fragment-v1.json"
  evidenceRoot := "evidence/kernel-30.8.1"
  projection := "evidence/kernel-30.8.1/projection.json"
  fixtureDirectory := "examples/reference-cli/flat-evidence"
  cases := [
    { id := "number-empty-equals-zero-content"
      expectedVerdict := .fired .omission
      covers := ["emptyNumberComparisonZero", "contentBearingRow", "omissionPolarity"] },
    { id := "number-empty-equals-zero-empty-row"
      expectedVerdict := .notFired
      covers := ["emptyNumberComparisonZero", "allEmptyRowGate", "leanNonFiringProjection"] },
    { id := "boolean-empty-equals-true"
      expectedVerdict := .notFired
      covers := ["emptyBooleanNotEvaluated", "kindSpecificEmpty", "leanNonFiringProjection"] },
    { id := "confirm-empty-not-true"
      expectedVerdict := .fired .omission
      covers := ["emptyConfirmAsFalse", "confirmNotEqualTrue", "omissionPolarity"] },
    { id := "malformed-number-equals-zero"
      expectedVerdict := .unknown
      covers := ["malformedAsUnknown", "authoredMessageSuppression", "leanUnknownProjection"] },
    { id := "healthy-or-malformed"
      expectedVerdict := .fired .value
      covers := ["strongKleeneOr", "trueDominatesUnknown", "valuePolarity"] },
    { id := "healthy-and-malformed"
      expectedVerdict := .unknown
      covers := ["strongKleeneAnd", "trueAndUnknown", "leanUnknownProjection"] },
    { id := "number-not-filled-empty-row"
      expectedVerdict := .fired .omission
      covers := ["fieldNotFilled", "emptyRowEligibility", "omissionPolarity"] }] }

private def firstDuplicate? [BEq α] : List α → Option α
  | [] => none
  | value :: rest =>
      if rest.contains value then some value else firstDuplicate? rest

def CapabilityDescriptor.validate (descriptor : CapabilityDescriptor) : Except String Unit := do
  if descriptor.id.isEmpty then throw "capability id must not be empty"
  if descriptor.cases.length != 8 then
    throw s!"{descriptor.id}: expected exactly eight cases, found {descriptor.cases.length}"
  match firstDuplicate? (descriptor.cases.map (·.id)) with
  | some duplicate => throw s!"{descriptor.id}: duplicate case id '{duplicate}'"
  | none => pure ()
  for case in descriptor.cases do
    if case.id.isEmpty then throw s!"{descriptor.id}: case id must not be empty"
    if case.covers.isEmpty then throw s!"{case.id}: coverage labels must not be empty"
    if (firstDuplicate? case.covers).isSome then
      throw s!"{case.id}: coverage labels must be unique"

private def fieldKindJson : FieldKindSpec → Json
  | .number scale signed => Json.mkObj [
      ("tag", toJson "number"), ("scale", toJson scale), ("signed", toJson signed)]
  | .boolean => Json.mkObj [("tag", toJson "boolean")]
  | .confirm => Json.mkObj [("tag", toJson "confirm")]

private def fieldJson (field : FieldSpec) : Json :=
  Json.mkObj [
    ("id", toJson field.id),
    ("groupPath", toJson field.groups),
    ("name", toJson field.name),
    ("kind", fieldKindJson field.kind),
    ("repeatableScope", toJson ([] : List Nat))]

private def pathJson (path : PathSpec) : Except String Json :=
  match path.base with
  | .absolute => pure <| Json.mkObj [
      ("base", toJson "absolute"),
      ("groups", toJson path.groups),
      ("field", toJson path.field)]
  | .relative _ => throw "flat-validation-empty-logic-v1 accepts only absolute field paths"

private def literalJson : LiteralSpec → Json
  | .number value => Json.mkObj [
      ("tag", toJson "number"), ("value", toJson (toString value))]
  | .boolean value => Json.mkObj [
      ("tag", toJson "boolean"), ("value", toJson value)]

private def conditionJson : ConditionSpec → Except String Json
  | .compare comparison path literal => do
      if comparison != "equal" && comparison != "notEqual" then
        throw s!"unsupported flat comparison '{comparison}'"
      pure <| Json.mkObj [
        ("tag", toJson "compare"),
        ("operator", toJson comparison),
        ("field", ← pathJson path),
        ("literal", literalJson literal)]
  | .fieldNotFilled path => do
      pure <| Json.mkObj [
        ("tag", toJson "fieldNotFilled"),
        ("field", ← pathJson path)]
  | .and left right => do
      pure <| Json.mkObj [
        ("tag", toJson "and"),
        ("left", ← conditionJson left),
        ("right", ← conditionJson right)]
  | .or left right => do
      pure <| Json.mkObj [
        ("tag", toJson "or"),
        ("left", ← conditionJson left),
        ("right", ← conditionJson right)]

private def cellJson? (cell : CellSpec) : Except String (Option Json) := do
  let state ← match cell.state with
    | .empty => pure none
    | .boolean true => pure <| some <| Json.mkObj [
        ("tag", toJson "parsedBoolean"), ("value", toJson true)]
    | .rejected => pure <| some <| Json.mkObj [
        ("tag", toJson "rejected"), ("cause", toJson "malformed")]
    | other => throw s!"flat-validation-empty-logic-v1 has unsupported stored cell {repr other}"
  pure <| state.map fun value => Json.mkObj [
    ("fieldId", toJson cell.fieldId), ("state", value)]

def caseProtocolRequestJson (case : CaseSpec) : Except String Json := do
  let (declaringGroup, condition, hasContent) ← match case.operation with
    | .flat declaringGroup condition hasContent => pure (declaringGroup, condition, hasContent)
    | _ => throw s!"{case.id}: expected a flat evidence operation"
  let cells ← case.cells.filterMapM cellJson?
  pure <| Json.mkObj [
    ("protocolVersion", toJson Support.protocolVersion),
    ("kernelBehaviorVersion", toJson Support.kernelBehaviorVersion),
    ("operation", toJson Support.Operation.flatValidationEvaluateFull.tag),
    ("model", Json.mkObj [
      ("fieldRefByShortNameAllowed", toJson case.fieldRefByShortNameAllowed),
      ("repeatableGroups", toJson ([] : List Json)),
      ("fields", Json.arr (case.fields.map fieldJson).toArray)]),
    ("declaringGroup", toJson declaringGroup),
    ("condition", ← conditionJson condition),
    ("cells", Json.arr cells.toArray),
    ("hasContent", toJson hasContent)]

private def replayInputToReferenceRequest
    (input : A12Kernel.Evidence.FlatReplayInput) : FlatRequest :=
  let { model, declaringGroup, condition, cells, hasContent } := input
  {
    model
    declaringGroup
    condition
    cells := cells.map fun (fieldId, raw) => { fieldId, raw }
    hasContent }

def checkedProtocolRequest (case : CaseSpec) : Except String (Json × FlatRequest) := do
  let requestJson ← caseProtocolRequestJson case
  let expected := replayInputToReferenceRequest
    (← A12Kernel.Evidence.CaseSpec.toFlatReplayInput case)
  match Decode.request requestJson with
  | .ok (.flatValidation decoded) =>
      if decoded != expected then
        throw s!"{case.id}: generated protocol request does not decode to the retained replay input"
      pure (requestJson, decoded)
  | .ok _ => throw s!"{case.id}: generated request decoded as the wrong operation"
  | .error diagnostic =>
      throw s!"{case.id}: generated protocol request was rejected: {diagnostic.asJson.compress}"

private structure MessageSignature where
  code : String
  polarity : Polarity
  pointer : String
  deriving Repr, DecidableEq

private def MessageSignature.parse (signature : String) : Except String MessageSignature := do
  let (code, polarityName, pointer) ← match signature.splitOn "|" with
    | [code, polarity, pointer] => pure (code, polarity, pointer)
    | _ => throw s!"invalid retained message signature '{signature}'"
  if code.isEmpty then throw s!"retained message signature has an empty code: '{signature}'"
  if pointer.isEmpty then throw s!"retained message signature has an empty pointer: '{signature}'"
  let polarity ← match polarityName with
    | "VALUE_ERROR" => pure .value
    | "OMISSION_ERROR" => pure .omission
    | other => throw s!"unsupported retained message polarity '{other}'"
  pure { code, polarity, pointer }

def focusedObservation (caseId focusCode focusPointer : String) (expected : List String) :
    Except String FocusedAuthoredObservation := do
  let signatures ← expected.mapM MessageSignature.parse
  let focused := signatures.filter fun signature => signature.code == focusCode
  match focused with
  | [] => pure .silent
  | [signature] =>
      if signature.pointer != focusPointer then
        throw s!"{caseId}: focused message '{focusCode}' was emitted at '{signature.pointer}', expected '{focusPointer}'"
      match signature.polarity with
      | .value => pure .firedValue
      | .omission => pure .firedOmission
  | _ => throw s!"{caseId}: retained case has duplicate focused message signatures"

private def checkFocusedObservationGuards : Except String Unit := do
  match focusedObservation "misrouted-focus-guard" "FOCUS" "/expected"
      ["FOCUS|VALUE_ERROR|/unexpected"] with
  | .error _ => pure ()
  | .ok observation =>
      throw s!"focused-observation guard accepted a misrouted message as {repr observation}"
  match focusedObservation "duplicate-focus-guard" "FOCUS" "/expected"
      ["FOCUS|VALUE_ERROR|/expected", "FOCUS|VALUE_ERROR|/other"] with
  | .error _ => pure ()
  | .ok observation =>
      throw s!"focused-observation guard accepted duplicate focused messages as {repr observation}"

def FocusedAuthoredObservation.accepts (observation : FocusedAuthoredObservation)
    (response : Response) : Bool :=
  match observation, response with
  | .firedValue, .verdict (.fired .value) => true
  | .firedOmission, .verdict (.fired .omission) => true
  | .silent, .verdict .notFired => true
  | .silent, .verdict .unknown => true
  | _, _ => false

def FocusedAuthoredObservation.classification : FocusedAuthoredObservation →
    ExternalSupport × ExpectedResponseSource
  | .firedValue | .firedOmission =>
      (.verdictFiringAndPolarity, .retainedProjection)
  | .silent => (.verdictSuppressionOnly, .leanRuntimeProjection)

structure CaseArtifact where
  descriptor : CaseDescriptor
  request : Json
  response : Json
  externalSupport : ExternalSupport
  responseSource : ExpectedResponseSource

private def CapabilityDescriptor.caseById (descriptor : CapabilityDescriptor)
    (id : String) : Except String CaseDescriptor :=
  match descriptor.cases.filter (·.id == id) with
  | [case] => pure case
  | [] => throw s!"{descriptor.id}: unexpected retained case '{id}'"
  | _ => throw s!"{descriptor.id}: ambiguous retained case '{id}'"

def CapabilityDescriptor.buildCaseArtifact (descriptor : CapabilityDescriptor)
    (case : CaseSpec) (externalExpected : List String) : Except String CaseArtifact := do
  let caseDescriptor ← descriptor.caseById case.id
  let observation ← focusedObservation case.id case.focusCode case.focusPointer externalExpected
  let (requestJson, request) ← checkedProtocolRequest case
  let actual ← match Reference.evaluate (.flatValidation request) with
    | .ok response => pure response
    | .error failure => throw s!"{case.id}: reference evaluation failed internally: {repr failure}"
  let expected : Response := .verdict caseDescriptor.expectedVerdict
  if actual.asJson != expected.asJson then
    throw s!"{case.id}: descriptor expects {expected.asJson.compress}, Lean produced {actual.asJson.compress}"
  if !FocusedAuthoredObservation.accepts observation expected then
    throw s!"{case.id}: retained focused observation does not accept {expected.asJson.compress}"
  let (externalSupport, responseSource) :=
    FocusedAuthoredObservation.classification observation
  pure {
    descriptor := caseDescriptor
    request := requestJson
    response := expected.asJson
    externalSupport
    responseSource }

def CapabilityDescriptor.requestPath (descriptor : CapabilityDescriptor)
    (case : CaseDescriptor) : System.FilePath :=
  descriptor.fixtureDirectory / s!"{case.id}.request.json"

def CapabilityDescriptor.responsePath (descriptor : CapabilityDescriptor)
    (case : CaseDescriptor) : System.FilePath :=
  descriptor.fixtureDirectory / s!"{case.id}.response.json"

private def CapabilityDescriptor.suiteCaseJson (descriptor : CapabilityDescriptor)
    (artifact : CaseArtifact) : Json :=
  Json.mkObj [
    ("id", toJson artifact.descriptor.id),
    ("request", toJson (descriptor.requestPath artifact.descriptor).toString),
    ("expectedResponse", toJson (descriptor.responsePath artifact.descriptor).toString),
    ("evidence", Json.mkObj [
      ("kind", toJson "kernelRuntimeObservation"),
      ("projection", toJson descriptor.projection.toString),
      ("caseId", toJson artifact.descriptor.id),
      ("externalSupports", toJson artifact.externalSupport.tag),
      ("expectedResponseSource", toJson artifact.responseSource.tag)]),
    ("covers", toJson artifact.descriptor.covers)]

def CapabilityDescriptor.suiteJson (descriptor : CapabilityDescriptor)
    (artifacts : List CaseArtifact) : Except String Json := do
  descriptor.validate
  if artifacts.map (·.descriptor.id) != descriptor.cases.map (·.id) then
    throw s!"{descriptor.id}: artifacts do not match descriptor order and identity"
  pure <| Json.mkObj [
    ("conformanceSchemaVersion", toJson 2),
    ("suiteId", toJson descriptor.id),
    ("referenceSemanticsVersion", toJson descriptor.referenceSemanticsVersion),
    ("protocolVersion", toJson descriptor.protocolVersion),
    ("manifestSchemaVersion", toJson descriptor.manifestSchemaVersion),
    ("kernelBehaviorVersion", toJson descriptor.kernelBehaviorVersion),
    ("operation", toJson descriptor.operation),
    ("supportManifest", toJson descriptor.supportManifest.toString),
    ("comparison", toJson "structuralJson"),
    ("cases", Json.arr (artifacts.map descriptor.suiteCaseJson).toArray)]

def CapabilityDescriptor.manifestBoundaryJson (descriptor : CapabilityDescriptor) : Json :=
  Json.mkObj [
    ("observable", toJson "focusedRuleMessagePresenceAndPolarity"),
    ("nonFiringVerdictDistinction", toJson "notFiredVersusUnknownLeanAccountOnly"),
    ("claimScope", toJson "finiteRetainedCasesOnly"),
    ("suiteId", toJson descriptor.id),
    ("retainedRuntimeCaseCount", toJson descriptor.cases.length),
    ("retainedStaticCaseCount", toJson 0),
    ("generalAcceptedInputs", toJson "leanAccountExternalEvidencePending")]

private structure RetainedObservation where
  id : String
  kernelVersion : String
  modelRef : String
  expected : List String
  divergences : List Json

private def member [FromJson α] (json : Json) (name : String) : Except String α := do
  fromJson? (← json.getObjVal? name)

private def optionalArray (json : Json) (name : String) : Except String (List Json) :=
  match json.getObjVal? name with
  | .ok value => fromJson? value
  | .error _ => pure []

private def RetainedObservation.fromJson (json : Json) : Except String RetainedObservation := do
  let metadata ← json.getObjVal? "meta"
  let operation ← json.getObjVal? "op"
  let operationKind : String ← member operation "kind"
  if operationKind != "validateFull" then
    throw s!"unsupported external operation '{operationKind}'"
  pure {
    id := ← member metadata "id"
    kernelVersion := ← member metadata "kernelVersion"
    modelRef := ← member json "modelRef"
    expected := ← member json "expected"
    divergences := ← optionalArray json "divergences" }

private def orThrow (context : String) : Except String α → IO α
  | .ok value => pure value
  | .error message => throw (IO.userError s!"{context}: {message}")

private def readJson (path : System.FilePath) : IO Json := do
  let content ← IO.FS.readFile path
  match StrictJson.parse content with
  | .ok json => pure json
  | .error error => throw (IO.userError s!"{path}: invalid JSON: {repr error}")

private def safeRelative (reference : String) : Bool :=
  !reference.isEmpty && !reference.startsWith "/" &&
    !(reference.splitOn "/").contains ".."

private def CapabilityDescriptor.selectCase (descriptor : CapabilityDescriptor)
    (bundle : Bundle) (caseDescriptor : CaseDescriptor) : Except String CaseSpec :=
  match bundle.cases.filter (·.id == caseDescriptor.id) with
  | [case] => pure case
  | [] => throw s!"{descriptor.id}: projection is missing case '{caseDescriptor.id}'"
  | _ => throw s!"{descriptor.id}: projection duplicates case '{caseDescriptor.id}'"

def CapabilityDescriptor.loadArtifacts (descriptor : CapabilityDescriptor) :
    IO (List CaseArtifact) := do
  orThrow descriptor.id descriptor.validate
  let bundle ← orThrow descriptor.projection.toString
    (Bundle.fromJson (← readJson descriptor.projection))
  orThrow descriptor.projection.toString bundle.validate
  if bundle.kernelVersion != descriptor.kernelBehaviorVersion then
    throw (IO.userError
      s!"{descriptor.id}: projection targets kernel {bundle.kernelVersion}, expected {descriptor.kernelBehaviorVersion}")
  descriptor.cases.mapM fun caseDescriptor => do
    let case ← orThrow caseDescriptor.id (descriptor.selectCase bundle caseDescriptor)
    if !safeRelative case.caseRef then
      throw (IO.userError s!"{case.id}: unsafe retained caseRef '{case.caseRef}'")
    let observation ← orThrow case.id
      (RetainedObservation.fromJson (← readJson (descriptor.evidenceRoot / case.caseRef)))
    if observation.id != case.id then
      throw (IO.userError s!"{case.id}: retained observation id is '{observation.id}'")
    if observation.kernelVersion != descriptor.kernelBehaviorVersion then
      throw (IO.userError
        s!"{case.id}: retained observation targets kernel {observation.kernelVersion}")
    if !safeRelative observation.modelRef then
      throw (IO.userError s!"{case.id}: unsafe retained modelRef '{observation.modelRef}'")
    if !(← System.FilePath.pathExists (descriptor.evidenceRoot / observation.modelRef)) then
      throw (IO.userError s!"{case.id}: retained model '{observation.modelRef}' is missing")
    if !observation.divergences.isEmpty then
      throw (IO.userError s!"{case.id}: retained observation records a strategy divergence")
    orThrow case.id (descriptor.buildCaseArtifact case observation.expected)

def CapabilityDescriptor.suitePath (descriptor : CapabilityDescriptor) : System.FilePath :=
  "reference" / s!"{descriptor.id}.conformance.json"

def CapabilityDescriptor.descriptorPath (descriptor : CapabilityDescriptor) : System.FilePath :=
  "reference" / s!"{descriptor.id}.capability.json"

private def verdictJson : Verdict → Json
  | .notFired => Json.mkObj [("tag", toJson "notFired")]
  | .unknown => Json.mkObj [("tag", toJson "unknown")]
  | .fired .value =>
      Json.mkObj [("tag", toJson "fired"), ("polarity", toJson "value")]
  | .fired .omission =>
      Json.mkObj [("tag", toJson "fired"), ("polarity", toJson "omission")]

private def CapabilityDescriptor.descriptorCaseJson (descriptor : CapabilityDescriptor)
    (artifact : CaseArtifact) : Json :=
  Json.mkObj [
    ("id", toJson artifact.descriptor.id),
    ("expectedVerdict", verdictJson artifact.descriptor.expectedVerdict),
    ("request", toJson (descriptor.requestPath artifact.descriptor).toString),
    ("expectedResponse", toJson (descriptor.responsePath artifact.descriptor).toString),
    ("externalSupports", toJson artifact.externalSupport.tag),
    ("expectedResponseSource", toJson artifact.responseSource.tag),
    ("covers", toJson artifact.descriptor.covers)]

def CapabilityDescriptor.descriptorJson (descriptor : CapabilityDescriptor)
    (artifacts : List CaseArtifact) : Except String Json := do
  descriptor.validate
  if artifacts.map (·.descriptor.id) != descriptor.cases.map (·.id) then
    throw s!"{descriptor.id}: artifacts do not match descriptor order and identity"
  pure <| Json.mkObj [
    ("capabilitySchemaVersion", toJson 1),
    ("capabilityId", toJson descriptor.id),
    ("status", toJson "developmentColdHandover"),
    ("referenceSemanticsVersion", toJson descriptor.referenceSemanticsVersion),
    ("protocolVersion", toJson descriptor.protocolVersion),
    ("manifestSchemaVersion", toJson descriptor.manifestSchemaVersion),
    ("kernelBehaviorVersion", toJson descriptor.kernelBehaviorVersion),
    ("operation", toJson descriptor.operation),
    ("supportManifest", toJson descriptor.supportManifest.toString),
    ("suite", toJson descriptor.suitePath.toString),
    ("evidence", Json.mkObj [
      ("projection", toJson descriptor.projection.toString),
      ("claimScope", toJson "finiteRetainedCasesOnly"),
      ("observable", toJson "focusedRuleMessagePresenceAndPolarity"),
      ("nonFiringVerdictDistinction", toJson "notFiredVersusUnknownLeanAccountOnly")]),
    ("inputProfile", Json.mkObj [
      ("fieldKinds", toJson ["number", "boolean", "confirm"]),
      ("pathForms", toJson ["absolute"]),
      ("repeatableScopes", toJson ["none"]),
      ("conditionForms", toJson ["compare", "fieldNotFilled", "and", "or"]),
      ("comparisonForms", toJson ["numberEqualZero", "booleanEqualTrue",
        "confirmNotEqualTrue"]),
      ("rawCellForms", toJson ["sparseEmpty", "parsedBooleanTrue",
        "rejectedMalformed"]),
      ("rowGate", toJson "explicitHasContent")]),
    ("exclusions", toJson [
      "generalFlatValidationInputs",
      "relativePaths",
      "repeatableFields",
      "generalDecimalValues",
      "otherLiteralsAndOperators",
      "completeNegativeProtocolSurface",
      "kernelInternalNotFiredVersusUnknown"]),
    ("cases", Json.arr (artifacts.map descriptor.descriptorCaseJson).toArray)]

private def assertJsonArtifact (path : System.FilePath) (expected : Json) : IO Unit := do
  let actual ← readJson path
  if actual != expected then
    throw (IO.userError
      s!"generated handover artifact '{path}' is stale\nexpected: {expected.compress}\nactual:   {actual.compress}")

private def CapabilityDescriptor.checkFixtureDirectory
    (descriptor : CapabilityDescriptor) : IO Unit := do
  let expectedNames := descriptor.cases.flatMap fun case =>
    [s!"{case.id}.request.json", s!"{case.id}.response.json"]
  let entries ← descriptor.fixtureDirectory.readDir
  for entry in entries do
    let metadata ← entry.path.symlinkMetadata
    if metadata.type != .file then
      throw (IO.userError
        s!"{descriptor.id}: generated fixture path '{entry.path}' is not a regular file")
  let actualNames := entries.toList.map (fun entry => entry.fileName)
  let extras := actualNames.filter fun name => !expectedNames.contains name
  let missing := expectedNames.filter fun name => !actualNames.contains name
  if !extras.isEmpty || !missing.isEmpty then
    throw (IO.userError
      s!"{descriptor.id}: generated fixture directory is not exact; stale={repr extras}, missing={repr missing}")

private def manifestBoundary (descriptor : CapabilityDescriptor) (manifest : Json) :
    Except String Json := do
  let operations : List Json ← member manifest "operations"
  let matching ← operations.filterM fun operation => do
    let tag : String ← member operation "operation"
    pure (tag == descriptor.operation)
  let operation ← match matching with
    | [operation] => pure operation
    | [] => throw s!"support manifest is missing operation '{descriptor.operation}'"
    | _ => throw s!"support manifest duplicates operation '{descriptor.operation}'"
  let accepted ← operation.getObjVal? "accepted"
  accepted.getObjVal? "externalEvidenceBoundary"

def CapabilityDescriptor.checkArtifacts (descriptor : CapabilityDescriptor) : IO Nat := do
  orThrow descriptor.id checkFocusedObservationGuards
  let artifacts ← descriptor.loadArtifacts
  descriptor.checkFixtureDirectory
  for artifact in artifacts do
    assertJsonArtifact (descriptor.requestPath artifact.descriptor) artifact.request
    assertJsonArtifact (descriptor.responsePath artifact.descriptor) artifact.response
  assertJsonArtifact descriptor.descriptorPath
    (← orThrow descriptor.id (descriptor.descriptorJson artifacts))
  assertJsonArtifact descriptor.suitePath (← orThrow descriptor.id (descriptor.suiteJson artifacts))
  let manifest ← readJson descriptor.supportManifest
  let actualBoundary ← orThrow descriptor.id (manifestBoundary descriptor manifest)
  let expectedBoundary := descriptor.manifestBoundaryJson
  if actualBoundary != expectedBoundary then
    throw (IO.userError
      s!"{descriptor.id}: support-manifest evidence boundary is stale\nexpected: {expectedBoundary.compress}\nactual:   {actualBoundary.compress}")
  pure artifacts.length

private def writeJson (path : System.FilePath) (json : Json) : IO Unit :=
  IO.FS.writeFile path (json.pretty 100 ++ "\n")

def CapabilityDescriptor.writeArtifacts (descriptor : CapabilityDescriptor) : IO Nat := do
  let artifacts ← descriptor.loadArtifacts
  IO.FS.createDirAll descriptor.fixtureDirectory
  for artifact in artifacts do
    writeJson (descriptor.requestPath artifact.descriptor) artifact.request
    writeJson (descriptor.responsePath artifact.descriptor) artifact.response
  writeJson descriptor.descriptorPath
    (← orThrow descriptor.id (descriptor.descriptorJson artifacts))
  writeJson descriptor.suitePath (← orThrow descriptor.id (descriptor.suiteJson artifacts))
  pure artifacts.length

end A12Kernel.Evidence.FlatProtocolBridge
