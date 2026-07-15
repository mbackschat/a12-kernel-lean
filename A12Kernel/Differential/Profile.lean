import A12Kernel.Reference.Evaluator

/-! # Bounded generated-differential profile

This process-side module defines the closed JSON profile and deterministic request generator for the first flat-validation differential campaign. It carries no semantic or evidence authority: requests are accepted by the public decoder and evaluated through the existing reference adapter.
-/

namespace A12Kernel.Differential.Profile

open Lean
open A12Kernel.Reference

def schemaVersion : Nat := 1

def profileId : String := "flat-validation-empty-logic-v1-generated-differential-v1"

def expectedCaseCount : Nat := 52

inductive ResponseProjection where
  | flatVerdictV1
  deriving Repr, DecidableEq

namespace ResponseProjection

def tag : ResponseProjection → String
  | .flatVerdictV1 => "flatVerdictV1"

def parse (value : String) : Except String ResponseProjection :=
  match value with
  | "flatVerdictV1" => pure .flatVerdictV1
  | other => throw s!"unsupported response projection '{other}'"

end ResponseProjection

inductive ProjectedVerdict where
  | notFired
  | firedValue
  | firedOmission
  | unknown
  deriving Repr, DecidableEq, BEq

namespace ProjectedVerdict

def tag : ProjectedVerdict → String
  | .notFired => "notFired"
  | .firedValue => "fired.value"
  | .firedOmission => "fired.omission"
  | .unknown => "unknown"

def all : List ProjectedVerdict := [.notFired, .firedValue, .firedOmission, .unknown]

end ProjectedVerdict

structure Compatibility where
  capabilityId : String
  operation : String
  referenceSemanticsVersion : String
  protocolVersion : Nat
  manifestSchemaVersion : Nat
  kernelBehaviorVersion : String
  deriving Repr, DecidableEq

structure Revisions where
  referenceRepository : String
  candidateRepository : String
  reference : String
  candidate : String
  deriving Repr, DecidableEq

/-- Execution fields are declared here so the later dual-process driver cannot acquire unreviewed defaults. This generator validates them but does not execute subprocesses. -/
structure ResourceBounds where
  cases : Nat
  requestBytes : Nat
  fields : Nat
  cells : Nat
  conditionDepth : Nat
  conditionNodes : Nat
  aggregateRequestBytes : Nat
  aggregateProcessInputBytes : Nat
  processTimeoutMilliseconds : Nat
  processCleanupMilliseconds : Nat
  processPollMilliseconds : Nat
  aggregateElapsedMilliseconds : Nat
  processStdoutBytes : Nat
  processStderrBytes : Nat
  aggregateProcessOutputBytes : Nat
  resultBytes : Nat
  deriving Repr, DecidableEq

structure ExecutionConfig where
  strategy : String
  processGroupContract : String
  platforms : List String
  workingDirectory : String
  environment : String
  jobs : Nat
  processesPerCase : Nat
  deriving Repr, DecidableEq

structure GeneratorConfig where
  strategy : String
  group : String
  fieldOrder : List String
  cellStateOrder : List String
  leafOrder : List String
  verdictAtomOrder : List String
  rowGateAtomOrder : List String
  connectiveOrder : List String
  deriving Repr, DecidableEq

structure Profile where
  id : String
  compatibility : Compatibility
  revisions : Revisions
  responseProjection : ResponseProjection
  observableVerdicts : List String
  bounds : ResourceBounds
  execution : ExecutionConfig
  generator : GeneratorConfig
  deriving Repr, DecidableEq

private def child (location name : String) : String :=
  if location == "$" then s!"$.{name}" else s!"{location}.{name}"

private def requireObject (json : Json) (location : String) (allowed : List String) :
    Except String (List (String × Json)) := do
  let members ← match json.getObj? with
    | .ok object => pure object.toList
    | .error _ => throw s!"{location}: expected object"
  for (name, _) in members do
    if !allowed.contains name then
      throw s!"{child location name}: unknown member"
  pure members

private def requiredJson (json : Json) (location name : String) : Except String Json :=
  match json.getObjVal? name with
  | .ok value => pure value
  | .error _ => throw s!"{child location name}: missing member"

private def required [FromJson α] (json : Json) (location name : String) : Except String α := do
  let value ← requiredJson json location name
  match fromJson? value with
  | .ok decoded => pure decoded
  | .error _ => throw s!"{child location name}: wrong type"

private def isLowerHex (character : Char) : Bool :=
  ('0' <= character && character <= '9') || ('a' <= character && character <= 'f')

private def validRevision (revision : String) : Bool :=
  revision.length == 40 && revision.toList.all isLowerHex

private def parseCompatibility (json : Json) : Except String Compatibility := do
  let location := "$.compatibility"
  let _ ← requireObject json location ["capabilityId", "operation", "referenceSemanticsVersion",
    "protocolVersion", "manifestSchemaVersion", "kernelBehaviorVersion"]
  pure {
    capabilityId := ← required json location "capabilityId"
    operation := ← required json location "operation"
    referenceSemanticsVersion := ← required json location "referenceSemanticsVersion"
    protocolVersion := ← required json location "protocolVersion"
    manifestSchemaVersion := ← required json location "manifestSchemaVersion"
    kernelBehaviorVersion := ← required json location "kernelBehaviorVersion" }

private def parseRevisions (json : Json) : Except String Revisions := do
  let location := "$.revisions"
  let _ ← requireObject json location ["referenceRepository", "candidateRepository", "reference", "candidate"]
  pure {
    referenceRepository := ← required json location "referenceRepository"
    candidateRepository := ← required json location "candidateRepository"
    reference := ← required json location "reference"
    candidate := ← required json location "candidate" }

private def parseBounds (json : Json) : Except String ResourceBounds := do
  let location := "$.bounds"
  let _ ← requireObject json location ["cases", "requestBytes", "fields", "cells",
    "conditionDepth", "conditionNodes", "aggregateRequestBytes", "aggregateProcessInputBytes",
    "processTimeoutMilliseconds",
    "processCleanupMilliseconds", "processPollMilliseconds", "aggregateElapsedMilliseconds",
    "processStdoutBytes", "processStderrBytes", "aggregateProcessOutputBytes", "resultBytes"]
  pure {
    cases := ← required json location "cases"
    requestBytes := ← required json location "requestBytes"
    fields := ← required json location "fields"
    cells := ← required json location "cells"
    conditionDepth := ← required json location "conditionDepth"
    conditionNodes := ← required json location "conditionNodes"
    aggregateRequestBytes := ← required json location "aggregateRequestBytes"
    aggregateProcessInputBytes := ← required json location "aggregateProcessInputBytes"
    processTimeoutMilliseconds := ← required json location "processTimeoutMilliseconds"
    processCleanupMilliseconds := ← required json location "processCleanupMilliseconds"
    processPollMilliseconds := ← required json location "processPollMilliseconds"
    aggregateElapsedMilliseconds := ← required json location "aggregateElapsedMilliseconds"
    processStdoutBytes := ← required json location "processStdoutBytes"
    processStderrBytes := ← required json location "processStderrBytes"
    aggregateProcessOutputBytes := ← required json location "aggregateProcessOutputBytes"
    resultBytes := ← required json location "resultBytes" }

private def parseExecution (json : Json) : Except String ExecutionConfig := do
  let location := "$.execution"
  let _ ← requireObject json location ["strategy", "processGroupContract", "platforms",
    "workingDirectory", "environment", "jobs", "processesPerCase"]
  pure {
    strategy := ← required json location "strategy"
    processGroupContract := ← required json location "processGroupContract"
    platforms := ← required json location "platforms"
    workingDirectory := ← required json location "workingDirectory"
    environment := ← required json location "environment"
    jobs := ← required json location "jobs"
    processesPerCase := ← required json location "processesPerCase" }

private def parseGenerator (json : Json) : Except String GeneratorConfig := do
  let location := "$.generator"
  let _ ← requireObject json location ["strategy", "group", "fieldOrder", "cellStateOrder",
    "leafOrder", "verdictAtomOrder", "rowGateAtomOrder", "connectiveOrder"]
  pure {
    strategy := ← required json location "strategy"
    group := ← required json location "group"
    fieldOrder := ← required json location "fieldOrder"
    cellStateOrder := ← required json location "cellStateOrder"
    leafOrder := ← required json location "leafOrder"
    verdictAtomOrder := ← required json location "verdictAtomOrder"
    rowGateAtomOrder := ← required json location "rowGateAtomOrder"
    connectiveOrder := ← required json location "connectiveOrder" }

private def expectedCompatibility : Compatibility := {
  capabilityId := "flat-validation-empty-logic-v1"
  operation := Support.Operation.flatValidationEvaluateFull.tag
  referenceSemanticsVersion := Support.referenceSemanticsVersion
  protocolVersion := Support.protocolVersion
  manifestSchemaVersion := Support.manifestSchemaVersion
  kernelBehaviorVersion := Support.kernelBehaviorVersion }

private def expectedGenerator : GeneratorConfig := {
  strategy := "exhaustiveFiniteMatrices"
  group := "GeneratedForm"
  fieldOrder := ["N", "B", "C"]
  cellStateOrder := ["sparseEmpty", "parsedBooleanTrue", "rejectedMalformed"]
  leafOrder := ["numberEqualZero", "booleanEqualTrue", "confirmNotEqualTrue", "booleanNotFilled"]
  verdictAtomOrder := ["notFired", "value", "omission", "unknown"]
  rowGateAtomOrder := ["ineligible", "eligible"]
  connectiveOrder := ["and", "or"] }

private def expectedExecution : ExecutionConfig := {
  strategy := "sequentialDualProcessViaProjectRelay"
  processGroupContract := "lean4.31-posix-setsid-sigkill"
  platforms := ["macos", "linux"]
  workingDirectory := "inherited"
  environment := "inherited"
  jobs := 1
  processesPerCase := 2 }

private def validateBounds (bounds : ResourceBounds) : Except String Unit := do
  if bounds.cases != expectedCaseCount then
    throw s!"$.bounds.cases: expected {expectedCaseCount}, found {bounds.cases}"
  if bounds.requestBytes == 0 || bounds.requestBytes >= Support.maxInputBytes then
    throw "$.bounds.requestBytes: must be positive and leave one protocol input byte for the JSON-line newline"
  if bounds.fields != 3 then throw "$.bounds.fields: expected the closed three-field model"
  if bounds.cells != 2 then throw "$.bounds.cells: expected the tight two-cell bound"
  if bounds.conditionDepth != 2 then throw "$.bounds.conditionDepth: expected the tight depth-two bound"
  if bounds.conditionNodes != 3 then throw "$.bounds.conditionNodes: expected the tight three-node bound"
  if bounds.aggregateRequestBytes < bounds.requestBytes || bounds.aggregateRequestBytes == 0 then
    throw "$.bounds.aggregateRequestBytes: must cover at least one maximum-size request"
  if bounds.aggregateRequestBytes > 4 * Support.maxInputBytes then
    throw "$.bounds.aggregateRequestBytes: exceeds the profile safety ceiling"
  if bounds.aggregateProcessInputBytes < bounds.aggregateRequestBytes ||
      bounds.aggregateProcessInputBytes > 8 * Support.maxInputBytes then
    throw "$.bounds.aggregateProcessInputBytes: must cover aggregate requests and remain below the profile safety ceiling"
  if bounds.processTimeoutMilliseconds == 0 || bounds.processTimeoutMilliseconds > 30000 then
    throw "$.bounds.processTimeoutMilliseconds: must be between 1 and 30000"
  if bounds.processCleanupMilliseconds == 0 || bounds.processCleanupMilliseconds > 10000 then
    throw "$.bounds.processCleanupMilliseconds: must be between 1 and 10000"
  if bounds.processPollMilliseconds == 0 ||
      bounds.processPollMilliseconds > bounds.processTimeoutMilliseconds ||
      bounds.processPollMilliseconds > bounds.processCleanupMilliseconds then
    throw "$.bounds.processPollMilliseconds: must be positive and fit both process deadlines"
  if bounds.aggregateElapsedMilliseconds <
      bounds.processTimeoutMilliseconds + bounds.processCleanupMilliseconds ||
      bounds.aggregateElapsedMilliseconds > 300000 then
    throw "$.bounds.aggregateElapsedMilliseconds: must cover one process lifecycle and be no greater than five minutes"
  if bounds.processStdoutBytes == 0 || bounds.processStdoutBytes > Support.maxInputBytes ||
      bounds.processStderrBytes == 0 || bounds.processStderrBytes > Support.maxInputBytes then
    throw "$.bounds: per-process output bounds must be positive and no greater than the protocol input limit"
  if bounds.aggregateProcessOutputBytes < bounds.processStdoutBytes + bounds.processStderrBytes then
    throw "$.bounds.aggregateProcessOutputBytes: must cover at least one process output budget"
  if bounds.aggregateProcessOutputBytes > 128 * Support.maxInputBytes then
    throw "$.bounds.aggregateProcessOutputBytes: exceeds the profile safety ceiling"
  -- A successful projected response has a closed, small schema. A failure can
  -- retain stdout both as a byte capture and as parsed JSON; six bytes per
  -- source byte covers worst-case JSON string escaping. The failure reserve
  -- is additive because a late failure retains earlier disagreements.
  let minimumResultBytes :=
    bounds.aggregateRequestBytes + bounds.cases * (2 * 512) +
      12 * bounds.processStdoutBytes + 6 * bounds.processStderrBytes + 65536
  if bounds.resultBytes < minimumResultBytes then
    throw s!"$.bounds.resultBytes: must be at least {minimumResultBytes} bytes to preserve every possible disagreement or process failure"
  if bounds.resultBytes > 32 * Support.maxInputBytes then
    throw "$.bounds.resultBytes: exceeds the profile safety ceiling"

private def Profile.validate (profile : Profile) : Except String Unit := do
  if profile.id != profileId then throw s!"$.profileId: expected '{profileId}'"
  if profile.compatibility != expectedCompatibility then
    throw "$.compatibility: tuple does not match the supported flat capability"
  if profile.revisions.referenceRepository != "a12-kernel-lean" then
    throw "$.revisions.referenceRepository: expected 'a12-kernel-lean'"
  if profile.revisions.candidateRepository != "a12-kernel-rust-spike" then
    throw "$.revisions.candidateRepository: expected 'a12-kernel-rust-spike'"
  if !validRevision profile.revisions.reference then
    throw "$.revisions.reference: expected a 40-character lowercase hexadecimal revision"
  if !validRevision profile.revisions.candidate then
    throw "$.revisions.candidate: expected a 40-character lowercase hexadecimal revision"
  if profile.observableVerdicts != ProjectedVerdict.all.map ProjectedVerdict.tag then
    throw "$.observableVerdicts: expected the closed ordered four-verdict projection"
  if profile.execution != expectedExecution then
    throw "$.execution: configuration does not match the closed sequential process contract"
  if profile.generator != expectedGenerator then
    throw "$.generator: configuration does not match the closed deterministic matrix"
  validateBounds profile.bounds

/-- Strictly decode the closed generation-profile schema and validate its capability identity. -/
def parseText (input : String) : Except String Profile := do
  let json ← match StrictJson.parse input with
    | .ok json => pure json
    | .error error => throw s!"invalid profile JSON: {repr error}"
  let location := "$"
  let _ ← requireObject json location ["schemaVersion", "profileId", "compatibility", "revisions",
    "responseProjection", "observableVerdicts", "bounds", "execution", "generator"]
  let receivedSchema : Nat ← required json location "schemaVersion"
  if receivedSchema != schemaVersion then
    throw s!"$.schemaVersion: unsupported version {receivedSchema}"
  let projectionName : String ← required json location "responseProjection"
  let profile : Profile := {
    id := ← required json location "profileId"
    compatibility := ← parseCompatibility (← requiredJson json location "compatibility")
    revisions := ← parseRevisions (← requiredJson json location "revisions")
    responseProjection := ← ResponseProjection.parse projectionName
    observableVerdicts := ← required json location "observableVerdicts"
    bounds := ← parseBounds (← requiredJson json location "bounds")
    execution := ← parseExecution (← requiredJson json location "execution")
    generator := ← parseGenerator (← requiredJson json location "generator") }
  profile.validate
  pure profile

inductive Family where
  | leafCellState
  | verdictAlgebra
  | rowGate
  deriving Repr, DecidableEq, BEq

namespace Family

def tag : Family → String
  | .leafCellState => "leaf-cell-state"
  | .verdictAlgebra => "verdict-algebra"
  | .rowGate => "row-gate"

end Family

structure Metrics where
  fields : Nat
  cells : Nat
  conditionDepth : Nat
  conditionNodes : Nat
  deriving Repr, DecidableEq

structure GeneratedCase where
  id : String
  family : Family
  request : Json
  metrics : Metrics

private inductive Atom where
  | numberEqualZero
  | booleanEqualTrue
  | confirmNotEqualTrue
  | booleanNotFilled
  | numberNotFilled
  deriving Repr, DecidableEq

namespace Atom

private def tag : Atom → String
  | .numberEqualZero => "number-equal-zero"
  | .booleanEqualTrue => "boolean-equal-true"
  | .confirmNotEqualTrue => "confirm-not-equal-true"
  | .booleanNotFilled => "boolean-not-filled"
  | .numberNotFilled => "number-not-filled"

end Atom

private inductive GeneratedField where
  | number
  | boolean
  | confirm
  deriving Repr, DecidableEq

namespace GeneratedField

private def parse (value : String) : Except String GeneratedField :=
  match value with
  | "N" => pure .number
  | "B" => pure .boolean
  | "C" => pure .confirm
  | other => throw s!"unsupported generated field '{other}'"

private def name : GeneratedField → String
  | .number => "N"
  | .boolean => "B"
  | .confirm => "C"

private def policy : GeneratedField → FieldPolicy
  | .number => { kind := .number { scale := 2, signed := false } }
  | .boolean => { kind := .boolean }
  | .confirm => { kind := .confirm }

private def kindJson : GeneratedField → Json
  | .number => Json.mkObj [
      ("tag", toJson "number"), ("scale", toJson 2), ("signed", toJson false)]
  | .boolean => Json.mkObj [("tag", toJson "boolean")]
  | .confirm => Json.mkObj [("tag", toJson "confirm")]

end GeneratedField

private inductive CellState where
  | sparseEmpty
  | parsedBooleanTrue
  | rejectedMalformed
  deriving Repr, DecidableEq

namespace CellState

private def parse (value : String) : Except String CellState :=
  match value with
  | "sparseEmpty" => pure .sparseEmpty
  | "parsedBooleanTrue" => pure .parsedBooleanTrue
  | "rejectedMalformed" => pure .rejectedMalformed
  | other => throw s!"unsupported generated cell state '{other}'"

private def tag : CellState → String
  | .sparseEmpty => "sparse-empty"
  | .parsedBooleanTrue => "parsed-boolean-true"
  | .rejectedMalformed => "rejected-malformed"

end CellState

private inductive Connective where
  | and
  | or
  deriving Repr, DecidableEq

namespace Connective

private def parse (value : String) : Except String Connective :=
  match value with
  | "and" => pure .and
  | "or" => pure .or
  | other => throw s!"unsupported generated connective '{other}'"

private def tag : Connective → String
  | .and => "and"
  | .or => "or"

end Connective

private structure NamedAtom where
  name : String
  atom : Atom

private structure GeneratorDomain where
  groupPath : List String
  fields : List GeneratedField
  cellStates : List CellState
  leafAtoms : List Atom
  verdictAtoms : List NamedAtom
  rowGateAtoms : List NamedAtom
  connectives : List Connective

private def parseLeafAtom (value : String) : Except String Atom :=
  match value with
  | "numberEqualZero" => pure .numberEqualZero
  | "booleanEqualTrue" => pure .booleanEqualTrue
  | "confirmNotEqualTrue" => pure .confirmNotEqualTrue
  | "booleanNotFilled" => pure .booleanNotFilled
  | other => throw s!"unsupported generated leaf atom '{other}'"

private def parseVerdictAtom (value : String) : Except String NamedAtom :=
  match value with
  | "notFired" => pure { name := "not-fired", atom := .booleanNotFilled }
  | "value" => pure { name := "value", atom := .booleanEqualTrue }
  | "omission" => pure { name := "omission", atom := .numberEqualZero }
  | "unknown" => pure { name := "unknown", atom := .confirmNotEqualTrue }
  | other => throw s!"unsupported generated verdict atom '{other}'"

private def parseRowGateAtom (value : String) : Except String NamedAtom :=
  match value with
  | "ineligible" => pure { name := "ineligible", atom := .booleanEqualTrue }
  | "eligible" => pure { name := "eligible", atom := .numberNotFilled }
  | other => throw s!"unsupported generated row-gate atom '{other}'"

private def GeneratorConfig.domain (config : GeneratorConfig) : Except String GeneratorDomain := do
  pure {
    groupPath := [config.group]
    fields := ← config.fieldOrder.mapM GeneratedField.parse
    cellStates := ← config.cellStateOrder.mapM CellState.parse
    leafAtoms := ← config.leafOrder.mapM parseLeafAtom
    verdictAtoms := ← config.verdictAtomOrder.mapM parseVerdictAtom
    rowGateAtoms := ← config.rowGateAtomOrder.mapM parseRowGateAtom
    connectives := ← config.connectiveOrder.mapM Connective.parse }

private def fieldDeclarations (groupPath : List String) : Nat → List GeneratedField → List FlatFieldDecl
  | _, [] => []
  | id, field :: rest =>
      { id, groupPath, name := field.name, policy := field.policy } ::
        fieldDeclarations groupPath (id + 1) rest

private def GeneratorDomain.expectedModel (domain : GeneratorDomain) : FlatModel := {
  fieldRefByShortNameAllowed := true
  repeatableGroups := []
  fields := fieldDeclarations domain.groupPath 0 domain.fields }

private def pathJson (domain : GeneratorDomain) (field : String) : Json :=
  Json.mkObj [
    ("base", toJson "absolute"), ("groups", toJson domain.groupPath), ("field", toJson field)]

private def conditionJson (domain : GeneratorDomain) : Atom → Json
  | .numberEqualZero => Json.mkObj [
      ("tag", toJson "compare"), ("operator", toJson "equal"), ("field", pathJson domain "N"),
      ("literal", Json.mkObj [("tag", toJson "number"), ("value", toJson "0")])]
  | .booleanEqualTrue => Json.mkObj [
      ("tag", toJson "compare"), ("operator", toJson "equal"), ("field", pathJson domain "B"),
      ("literal", Json.mkObj [("tag", toJson "boolean"), ("value", toJson true)])]
  | .confirmNotEqualTrue => Json.mkObj [
      ("tag", toJson "compare"), ("operator", toJson "notEqual"), ("field", pathJson domain "C"),
      ("literal", Json.mkObj [("tag", toJson "boolean"), ("value", toJson true)])]
  | .booleanNotFilled => Json.mkObj [
      ("tag", toJson "fieldNotFilled"), ("field", pathJson domain "B")]
  | .numberNotFilled => Json.mkObj [
      ("tag", toJson "fieldNotFilled"), ("field", pathJson domain "N")]

private def connectiveJson (domain : GeneratorDomain) (connective : Connective)
    (left right : Atom) : Json :=
  Json.mkObj [
    ("tag", toJson connective.tag),
    ("left", conditionJson domain left),
    ("right", conditionJson domain right)]

private def fieldJson (groupPath : List String) (id : Nat) (name : String) (kind : Json) : Json :=
  Json.mkObj [
    ("id", toJson id), ("groupPath", toJson groupPath), ("name", toJson name),
    ("kind", kind), ("repeatableScope", toJson ([] : List Nat))]

private def fieldJsons (groupPath : List String) : Nat → List GeneratedField → List Json
  | _, [] => []
  | id, field :: rest =>
      fieldJson groupPath id field.name field.kindJson :: fieldJsons groupPath (id + 1) rest

private def modelJson (domain : GeneratorDomain) : Json :=
  Json.mkObj [
    ("fieldRefByShortNameAllowed", toJson true),
    ("repeatableGroups", toJson ([] : List Json)),
    ("fields", Json.arr (fieldJsons domain.groupPath 0 domain.fields).toArray)]

private def parsedBooleanCell (fieldId : Nat) : Json :=
  Json.mkObj [
    ("fieldId", toJson fieldId),
    ("state", Json.mkObj [("tag", toJson "parsedBoolean"), ("value", toJson true)])]

private def rejectedCell (fieldId : Nat) : Json :=
  Json.mkObj [
    ("fieldId", toJson fieldId),
    ("state", Json.mkObj [("tag", toJson "rejected"), ("cause", toJson "malformed")])]

private def requestJson (domain : GeneratorDomain) (condition : Json) (cells : List Json)
    (hasContent : Bool) : Json :=
  Json.mkObj [
    ("protocolVersion", toJson Support.protocolVersion),
    ("kernelBehaviorVersion", toJson Support.kernelBehaviorVersion),
    ("operation", toJson Support.Operation.flatValidationEvaluateFull.tag),
    ("model", modelJson domain),
    ("declaringGroup", toJson domain.groupPath),
    ("condition", condition),
    ("cells", Json.arr cells.toArray),
    ("hasContent", toJson hasContent)]

private def targetField : Atom → GeneratedField
  | .numberEqualZero | .numberNotFilled => .number
  | .booleanEqualTrue | .booleanNotFilled => .boolean
  | .confirmNotEqualTrue => .confirm

private def fieldId? (target : GeneratedField) : Nat → List GeneratedField → Option Nat
  | _, [] => none
  | id, field :: rest =>
      if field == target then some id else fieldId? target (id + 1) rest

private def GeneratorDomain.fieldId (domain : GeneratorDomain) (field : GeneratedField) :
    Except String Nat :=
  match fieldId? field 0 domain.fields with
  | some id => pure id
  | none => throw s!"generated field '{field.name}' is absent from the configured model"

private def leafCells (domain : GeneratorDomain) (atom : Atom) : CellState → Except String (List Json)
  | .sparseEmpty => pure []
  | .parsedBooleanTrue => do
      let id ← domain.fieldId (targetField atom)
      pure [parsedBooleanCell id]
  | .rejectedMalformed => do
      let id ← domain.fieldId (targetField atom)
      pure [rejectedCell id]

private def leafCases (domain : GeneratorDomain) : Except String (List GeneratedCase) := do
  let mut cases := []
  for atom in domain.leafAtoms do
    for state in domain.cellStates do
      let cells ← leafCells domain atom state
      cases := {
        id := s!"generated-leaf-{atom.tag}-{state.tag}"
        family := .leafCellState
        request := requestJson domain (conditionJson domain atom) cells true
        metrics := {
          fields := domain.fields.length
          cells := cells.length
          conditionDepth := 1
          conditionNodes := 1 } } :: cases
  pure cases.reverse

private def verdictAlgebraCases (domain : GeneratorDomain) : Except String (List GeneratedCase) := do
  let cells := [
    parsedBooleanCell (← domain.fieldId .boolean),
    rejectedCell (← domain.fieldId .confirm)]
  let mut cases := []
  for connective in domain.connectives do
    for left in domain.verdictAtoms do
      for right in domain.verdictAtoms do
        cases := {
          id := s!"generated-algebra-{connective.tag}-{left.name}-{right.name}"
          family := .verdictAlgebra
          request := requestJson domain
            (connectiveJson domain connective left.atom right.atom) cells true
          metrics := {
            fields := domain.fields.length
            cells := cells.length
            conditionDepth := 2
            conditionNodes := 3 } } :: cases
  pure cases.reverse

private def rowGateCases (domain : GeneratorDomain) : Except String (List GeneratedCase) := do
  -- `hasContent = false` is authoritative even with this present Boolean control cell;
  -- the matrix must not infer row content from sparse-cell presence.
  let cells := [parsedBooleanCell (← domain.fieldId .boolean)]
  let mut cases := []
  for connective in domain.connectives do
    for left in domain.rowGateAtoms do
      for right in domain.rowGateAtoms do
        cases := {
          id := s!"generated-row-gate-{connective.tag}-{left.name}-{right.name}"
          family := .rowGate
          request := requestJson domain
            (connectiveJson domain connective left.atom right.atom) cells false
          metrics := {
            fields := domain.fields.length
            cells := cells.length
            conditionDepth := 2
            conditionNodes := 3 } } :: cases
  pure cases.reverse

private def firstDuplicate? [BEq α] : List α → Option α
  | [] => none
  | value :: rest => if rest.contains value then some value else firstDuplicate? rest

private def conditionMetrics : SurfaceCondition → Nat × Nat
  | .compare .. | .fieldFilled .. | .fieldNotFilled .. => (1, 1)
  | .and left right | .or left right =>
      let leftMetrics := conditionMetrics left
      let rightMetrics := conditionMetrics right
      (Nat.max leftMetrics.1 rightMetrics.1 + 1, leftMetrics.2 + rightMetrics.2 + 1)

private def strictlyIncreasing : List Nat → Bool
  | [] | [_] => true
  | first :: second :: rest => first < second && strictlyIncreasing (second :: rest)

private def validateCase (profile : Profile) (domain : GeneratorDomain)
    (case : GeneratedCase) : Except String Unit := do
  if !case.id.startsWith "generated-" then
    throw s!"{case.id}: generated case id overlaps the retained fixture namespace"
  if case.request.compress.utf8ByteSize > profile.bounds.requestBytes then
    throw s!"{case.id}: request exceeds the per-case byte bound"
  if case.metrics.fields > profile.bounds.fields || case.metrics.cells > profile.bounds.cells ||
      case.metrics.conditionDepth > profile.bounds.conditionDepth ||
      case.metrics.conditionNodes > profile.bounds.conditionNodes then
    throw s!"{case.id}: generated shape exceeds its declared structural bounds"
  match Decode.request case.request with
  | .ok (.flatValidation request) =>
      if request.model != domain.expectedModel || request.declaringGroup != domain.groupPath then
        throw s!"{case.id}: generated request escaped the configured three-field model"
      if !strictlyIncreasing (request.cells.map (·.fieldId)) then
        throw s!"{case.id}: generated cells are not in strict field-id order"
      let conditionShape := conditionMetrics request.condition
      let actualMetrics : Metrics := {
        fields := request.model.fields.length
        cells := request.cells.length
        conditionDepth := conditionShape.1
        conditionNodes := conditionShape.2 }
      if actualMetrics != case.metrics then
        throw s!"{case.id}: declared metrics do not match the decoded request"
  | .ok _ => throw s!"{case.id}: generated request decoded as the wrong operation"
  | .error diagnostic =>
      throw s!"{case.id}: generated request was rejected: {diagnostic.asJson.compress}"

/-- Enumerate and validate the complete finite positive profile. -/
def generate (profile : Profile) : Except String (List GeneratedCase) := do
  profile.validate
  let domain ← profile.generator.domain
  let cases := (← leafCases domain) ++ (← verdictAlgebraCases domain) ++
    (← rowGateCases domain)
  if cases.length != profile.bounds.cases then
    throw s!"generated {cases.length} cases, expected {profile.bounds.cases}"
  match firstDuplicate? (cases.map (·.id)) with
  | some duplicate => throw s!"duplicate generated case id '{duplicate}'"
  | none => pure ()
  match firstDuplicate? (cases.map (·.request.compress)) with
  | some _ => throw "generated two byte-identical requests"
  | none => pure ()
  for case in cases do validateCase profile domain case
  let aggregateBytes := (cases.map fun case => case.request.compress.utf8ByteSize).sum
  if aggregateBytes > profile.bounds.aggregateRequestBytes then
    throw s!"generated request bytes {aggregateBytes} exceed aggregate bound {profile.bounds.aggregateRequestBytes}"
  let aggregateProcessInputBytes :=
    (cases.map fun case => (case.request.compress ++ "\n").utf8ByteSize *
      profile.execution.processesPerCase).sum
  if aggregateProcessInputBytes > profile.bounds.aggregateProcessInputBytes then
    throw s!"generated process-input bytes {aggregateProcessInputBytes} exceed aggregate bound {profile.bounds.aggregateProcessInputBytes}"
  pure cases

private def exactObject (json : Json) (location : String) (allowed : List String) :
    Except String Unit := do
  let _ ← requireObject json location allowed
  pure ()

/-- Apply the profile's declared observable projection to one candidate/reference response. -/
def projectResponse (profile : Profile) (json : Json) : Except String ProjectedVerdict := do
  match profile.responseProjection with
  | .flatVerdictV1 =>
      exactObject json "$response" ["protocolVersion", "kernelBehaviorVersion", "outcome", "verdict"]
      let protocol : Nat ← required json "$response" "protocolVersion"
      let kernel : String ← required json "$response" "kernelBehaviorVersion"
      let outcome : String ← required json "$response" "outcome"
      if protocol != profile.compatibility.protocolVersion ||
          kernel != profile.compatibility.kernelBehaviorVersion || outcome != "ok" then
        throw "$response: incompatible or non-success response envelope"
      let verdict ← requiredJson json "$response" "verdict"
      exactObject verdict "$response.verdict" ["tag", "polarity"]
      let tag : String ← required verdict "$response.verdict" "tag"
      let polarity? : Option String ← match verdict.getObjVal? "polarity" with
        | .error _ => pure none
        | .ok value =>
            match fromJson? value with
            | .ok polarity => pure (some polarity)
            | .error _ => throw "$response.verdict.polarity: wrong type"
      match tag, polarity? with
      | "notFired", none => pure .notFired
      | "unknown", none => pure .unknown
      | "fired", some "value" => pure .firedValue
      | "fired", some "omission" => pure .firedOmission
      | _, _ => throw "$response.verdict: outside flatVerdictV1"

def evaluateReference (profile : Profile) (case : GeneratedCase) : Except String ProjectedVerdict := do
  let response ← match Reference.evaluateText case.request.compress with
    | .ok response => pure response
    | .error failure => throw s!"{case.id}: internal reference failure {repr failure}"
  projectResponse profile response.asJson

end A12Kernel.Differential.Profile
