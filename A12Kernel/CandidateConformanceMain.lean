import Lake
import A12Kernel.Reference.StrictJson
import Lean.Data.Json

/-! # A12Kernel.CandidateConformanceMain — language-neutral candidate gate

This process runs a suite of normalized request/response fixtures against an independently implemented command-line candidate. It compares parsed JSON, while separately requiring deterministic candidate output bytes.
-/

open Lean

private inductive EvidenceKind where
  | kernelRuntimeObservation
  | kernelStaticDiagnostic
  | kernelStaticAcceptance
  deriving Repr, DecidableEq

namespace EvidenceKind

def tag : EvidenceKind → String
  | .kernelRuntimeObservation => "kernelRuntimeObservation"
  | .kernelStaticDiagnostic => "kernelStaticDiagnostic"
  | .kernelStaticAcceptance => "kernelStaticAcceptance"

def fromTag? : String → Option EvidenceKind
  | "kernelRuntimeObservation" => some .kernelRuntimeObservation
  | "kernelStaticDiagnostic" => some .kernelStaticDiagnostic
  | "kernelStaticAcceptance" => some .kernelStaticAcceptance
  | _ => none

end EvidenceKind

private inductive ExternalSupport where
  | firingRows
  | elaborationRejectionClass
  | elaborationAcceptanceOnly
  deriving Repr, DecidableEq

namespace ExternalSupport

def tag : ExternalSupport → String
  | .firingRows => "firingRows"
  | .elaborationRejectionClass => "elaborationRejectionClass"
  | .elaborationAcceptanceOnly => "elaborationAcceptanceOnly"

def fromTag? : String → Option ExternalSupport
  | "firingRows" => some .firingRows
  | "elaborationRejectionClass" => some .elaborationRejectionClass
  | "elaborationAcceptanceOnly" => some .elaborationAcceptanceOnly
  | _ => none

end ExternalSupport

private inductive ExpectedResponseSource where
  | retainedProjection
  | projectDiagnostic
  | leanRuntimeProjection
  deriving Repr, DecidableEq

namespace ExpectedResponseSource

def tag : ExpectedResponseSource → String
  | .retainedProjection => "retainedProjection"
  | .projectDiagnostic => "projectDiagnostic"
  | .leanRuntimeProjection => "leanRuntimeProjection"

def fromTag? : String → Option ExpectedResponseSource
  | "retainedProjection" => some .retainedProjection
  | "projectDiagnostic" => some .projectDiagnostic
  | "leanRuntimeProjection" => some .leanRuntimeProjection
  | _ => none

end ExpectedResponseSource

private structure EvidenceLink where
  kind : EvidenceKind
  projection : System.FilePath
  caseId : String
  externalSupports : ExternalSupport
  expectedResponseSource : ExpectedResponseSource

private structure ConformanceCase where
  id : String
  request : System.FilePath
  expectedResponse : System.FilePath
  evidence : EvidenceLink
  covers : List String

private structure ConformanceSuite where
  id : String
  referenceSemanticsVersion : String
  protocolVersion : Nat
  manifestSchemaVersion : Nat
  kernelBehaviorVersion : String
  operation : String
  supportManifest : System.FilePath
  cases : List ConformanceCase

private def fail (message : String) : IO α :=
  throw (IO.userError message)

private def requiredJson (json : Json) (name context : String) : IO Json :=
  match json.getObjVal? name with
  | .ok value => pure value
  | .error _ => fail s!"{context}: missing member '{name}'"

private def required [FromJson α] (json : Json) (name context : String) : IO α := do
  let value ← requiredJson json name context
  match fromJson? value with
  | .ok decoded => pure decoded
  | .error _ => fail s!"{context}: member '{name}' has the wrong type"

private def readJsonFile (path : System.FilePath) : IO Json := do
  let input ← IO.FS.readFile path
  match A12Kernel.Reference.StrictJson.parse input with
  | .ok json => pure json
  | .error error => fail s!"invalid normalized JSON file '{path}': {repr error}"

private def requireObject (json : Json) (allowed : List String)
    (context : String) : IO Unit := do
  let object ← match json.getObj? with
    | .ok object => pure object
    | .error _ => fail s!"{context}: expected an object"
  for (name, _) in object.toList do
    if !allowed.contains name then
      fail s!"{context}: unknown member '{name}'"

private def parseEvidenceKind (tag context : String) : IO EvidenceKind :=
  match EvidenceKind.fromTag? tag with
  | some kind => pure kind
  | none => fail s!"{context}: unsupported evidence kind '{tag}'"

private def parseExternalSupport (tag context : String) : IO ExternalSupport :=
  match ExternalSupport.fromTag? tag with
  | some support => pure support
  | none => fail s!"{context}: unsupported external support '{tag}'"

private def parseExpectedResponseSource (tag context : String) :
    IO ExpectedResponseSource :=
  match ExpectedResponseSource.fromTag? tag with
  | some source => pure source
  | none => fail s!"{context}: unsupported expected-response source '{tag}'"

private def parseEvidence (json : Json) (context : String) : IO EvidenceLink := do
  requireObject json ["kind", "projection", "caseId", "externalSupports",
    "expectedResponseSource"] context
  let kindTag : String ← required json "kind" context
  let supportTag : String ← required json "externalSupports" context
  let sourceTag : String ← required json "expectedResponseSource" context
  pure {
    kind := ← parseEvidenceKind kindTag context
    projection := ← required json "projection" context
    caseId := ← required json "caseId" context
    externalSupports := ← parseExternalSupport supportTag context
    expectedResponseSource := ← parseExpectedResponseSource sourceTag context }

private def parseCase (json : Json) (index : Nat) : IO ConformanceCase := do
  let context := s!"suite case {index}"
  requireObject json ["id", "request", "expectedResponse", "evidence", "covers"] context
  pure {
    id := ← required json "id" context
    request := ← required json "request" context
    expectedResponse := ← required json "expectedResponse" context
    evidence := ← parseEvidence (← requiredJson json "evidence" context)
      s!"{context} evidence"
    covers := ← required json "covers" context }

private def firstDuplicate? [BEq α] : List α → Option α
  | [] => none
  | value :: rest =>
      if rest.contains value then some value else firstDuplicate? rest

private def parseSuite (json : Json) : IO ConformanceSuite := do
  let context := "conformance suite"
  requireObject json ["conformanceSchemaVersion", "suiteId", "referenceSemanticsVersion",
    "protocolVersion", "manifestSchemaVersion", "kernelBehaviorVersion", "operation",
    "supportManifest", "comparison", "cases"] context
  let schemaVersion : Nat ← required json "conformanceSchemaVersion" context
  if schemaVersion != 2 then
    fail s!"{context}: unsupported schema version {schemaVersion}"
  let comparison : String ← required json "comparison" context
  if comparison != "structuralJson" then
    fail s!"{context}: unsupported comparison '{comparison}'"
  let caseJson : List Json ← required json "cases" context
  if caseJson.isEmpty then fail s!"{context}: cases must not be empty"
  let cases ← caseJson.zipIdx.mapM fun (value, index) => parseCase value index
  match firstDuplicate? (cases.map (·.id)) with
  | some duplicate => fail s!"{context}: duplicate case id '{duplicate}'"
  | none => pure ()
  for testCase in cases do
    if testCase.covers.isEmpty then
      fail s!"{context}: case '{testCase.id}' has no coverage labels"
    if testCase.evidence.projection.toString.isEmpty || testCase.evidence.caseId.isEmpty then
      fail s!"{context}: case '{testCase.id}' has an incomplete evidence link"
  pure {
    id := ← required json "suiteId" context
    referenceSemanticsVersion := ← required json "referenceSemanticsVersion" context
    protocolVersion := ← required json "protocolVersion" context
    manifestSchemaVersion := ← required json "manifestSchemaVersion" context
    kernelBehaviorVersion := ← required json "kernelBehaviorVersion" context
    operation := ← required json "operation" context
    supportManifest := ← required json "supportManifest" context
    cases }

private def assertMember [FromJson α] [BEq α] [Repr α] (json : Json) (name context : String)
    (expected : α) : IO Unit := do
  let actual : α ← required json name context
  if actual != expected then
    fail s!"{context}: member '{name}' is {repr actual}, expected {repr expected}"

private def validateFixtureMetadata (suite : ConformanceSuite)
    (testCase : ConformanceCase) (request response : Json) : IO Unit := do
  let requestContext := s!"case '{testCase.id}' request"
  assertMember request "protocolVersion" requestContext suite.protocolVersion
  assertMember request "kernelBehaviorVersion" requestContext suite.kernelBehaviorVersion
  assertMember request "operation" requestContext suite.operation
  let responseContext := s!"case '{testCase.id}' expected response"
  assertMember response "protocolVersion" responseContext suite.protocolVersion
  assertMember response "kernelBehaviorVersion" responseContext suite.kernelBehaviorVersion

private def validateSupportManifestJson (suite : ConformanceSuite) (manifest : Json)
    (context : String) : IO Unit := do
  assertMember manifest "manifestSchemaVersion" context suite.manifestSchemaVersion
  assertMember manifest "referenceSemanticsVersion" context suite.referenceSemanticsVersion
  assertMember manifest "protocolVersion" context suite.protocolVersion
  assertMember manifest "kernelBehaviorVersion" context suite.kernelBehaviorVersion
  let operations : List Json ← required manifest "operations" context
  let taggedOperations ← operations.mapM fun operation => do
    let tag : String ← required operation "operation" s!"{context} operation"
    pure (operation, tag)
  let matching := taggedOperations.filter fun (_, tag) => tag == suite.operation
  let operation ← match matching with
    | [(operation, _)] => pure operation
    | [] => fail s!"{context}: operation '{suite.operation}' is absent"
    | _ => fail s!"{context}: operation '{suite.operation}' is duplicated"
  let accepted ← requiredJson operation "accepted"
    s!"{context} operation '{suite.operation}'"
  let boundary ← requiredJson accepted "externalEvidenceBoundary"
    s!"{context} operation '{suite.operation}' accepted"
  let boundaryContext :=
    s!"{context} operation '{suite.operation}' external evidence boundary"
  assertMember boundary "suiteId" boundaryContext suite.id
  assertMember boundary "claimScope" boundaryContext "finiteRetainedCasesOnly"
  let runtimeCaseCount := (suite.cases.filter fun testCase =>
    testCase.evidence.kind == .kernelRuntimeObservation).length
  let staticCaseCount := suite.cases.length - runtimeCaseCount
  assertMember boundary "retainedRuntimeCaseCount" boundaryContext runtimeCaseCount
  assertMember boundary "retainedStaticCaseCount" boundaryContext staticCaseCount

private def validateSupportManifest (suite : ConformanceSuite) : IO Unit := do
  let manifest ← readJsonFile suite.supportManifest
  validateSupportManifestJson suite manifest
    s!"conformance suite support manifest '{suite.supportManifest}'"

private def validateExpectedEvidenceScope (testCase : ConformanceCase)
    (response : Json) : IO Unit := do
  let context := s!"case '{testCase.id}' expected response"
  match testCase.evidence.kind, testCase.evidence.externalSupports,
      testCase.evidence.expectedResponseSource with
  | .kernelRuntimeObservation, .firingRows, .retainedProjection =>
      assertMember response "outcome" context "ok"
      let _ : List Nat ← required response "firingRows" context
  | .kernelStaticDiagnostic, .elaborationRejectionClass, .projectDiagnostic =>
      assertMember response "outcome" context "error"
      let diagnostic ← requiredJson response "diagnostic" context
      assertMember diagnostic "category" s!"{context} diagnostic" "elaboration"
  | .kernelStaticAcceptance, .elaborationAcceptanceOnly, .leanRuntimeProjection =>
      assertMember response "outcome" context "ok"
      let _ : List Nat ← required response "firingRows" context
  | kind, support, source =>
      fail s!"case '{testCase.id}': incompatible evidence classification '{kind.tag}', '{support.tag}', '{source.tag}'"

private def validateEvidenceLink (suite : ConformanceSuite)
    (testCase : ConformanceCase) : IO Unit := do
  let projection ← readJsonFile testCase.evidence.projection
  assertMember projection "kernelVersion" s!"case '{testCase.id}' evidence projection"
    suite.kernelBehaviorVersion
  let cases : List Json ← required projection "cases" s!"case '{testCase.id}' evidence projection"
  let ids ← cases.mapM fun evidenceCase =>
    required evidenceCase "id" s!"case '{testCase.id}' evidence projection case"
  if !ids.contains testCase.evidence.caseId then
    fail s!"case '{testCase.id}': evidence case '{testCase.evidence.caseId}' is absent from '{testCase.evidence.projection}'"

private def loadAndValidateCaseArtifacts (suite : ConformanceSuite)
    (testCase : ConformanceCase) : IO (String × Json) := do
  let input ← IO.FS.readFile testCase.request
  let request ← readJsonFile testCase.request
  let expected ← readJsonFile testCase.expectedResponse
  validateFixtureMetadata suite testCase request expected
  validateExpectedEvidenceScope testCase expected
  validateEvidenceLink suite testCase
  pure (input, expected)

private def invoke (candidate : System.FilePath) (input : String) : IO IO.Process.Output :=
  IO.Process.output { cmd := candidate.toString } (some input)

private def validateProcessOutput (testCase : ConformanceCase)
    (output : IO.Process.Output) : IO Json := do
  if output.exitCode != 0 then
    fail s!"case '{testCase.id}': candidate exited {output.exitCode}, expected 0"
  if !output.stderr.isEmpty then
    fail s!"case '{testCase.id}': candidate wrote stderr {repr output.stderr}"
  if !output.stdout.endsWith "\n" then
    fail s!"case '{testCase.id}': candidate response must end with a newline"
  match A12Kernel.Reference.StrictJson.parse output.stdout with
  | .ok json => pure json
  | .error error => fail s!"case '{testCase.id}': candidate emitted invalid normalized JSON: {repr error}"

private def runCase (candidate : System.FilePath) (suite : ConformanceSuite)
    (testCase : ConformanceCase) : IO Unit := do
  let (input, expected) ← loadAndValidateCaseArtifacts suite testCase
  let first ← invoke candidate input
  let firstJson ← validateProcessOutput testCase first
  let second ← invoke candidate input
  let secondJson ← validateProcessOutput testCase second
  if first.stdout != second.stdout || firstJson != secondJson then
    fail s!"case '{testCase.id}': repeated candidate output is not byte-deterministic"
  if firstJson != expected then
    fail s!"case '{testCase.id}': candidate JSON {firstJson.compress}, expected {expected.compress}"

private def expectFailure (label : String) (action : IO Unit) : IO Unit := do
  let unexpectedlySucceeded ← try
    action
    pure true
  catch _ =>
    pure false
  if unexpectedlySucceeded then
    fail s!"candidate conformance self-test '{label}' did not reject its mutation"

private def replaceFirstEvidenceMember (suiteJson : Json) (name : String)
    (value : Json) : IO Json := do
  let cases : List Json ← required suiteJson "cases" "candidate conformance self-test"
  match cases with
  | [] => fail "candidate conformance self-test: suite has no cases"
  | first :: rest =>
      let evidence ← requiredJson first "evidence"
        "candidate conformance self-test first case"
      let changed := first.setObjVal! "evidence" (evidence.setObjVal! name value)
      pure (suiteJson.setObjVal! "cases" (toJson (changed :: rest)))

private def replaceFirstCaseMember (suiteJson : Json) (name : String)
    (value : Json) : IO Json := do
  let cases : List Json ← required suiteJson "cases" "candidate conformance self-test"
  match cases with
  | [] => fail "candidate conformance self-test: suite has no cases"
  | first :: rest =>
      pure (suiteJson.setObjVal! "cases"
        (toJson (first.setObjVal! name value :: rest)))

private def replaceManifestBoundaryMember (manifest : Json) (operationName name : String)
    (value : Json) : IO Json := do
  let operations : List Json ← required manifest "operations"
    "candidate conformance self-test manifest"
  let operationTags ← operations.mapM fun operation =>
    required operation "operation" "candidate conformance self-test manifest operation"
  let matchingCount := (operationTags.filter fun tag => tag == operationName).length
  if matchingCount != 1 then
    fail s!"candidate conformance self-test: operation '{operationName}' occurs {matchingCount} times"
  let changed ← operations.mapM fun operation => do
    let tag : String ← required operation "operation"
      "candidate conformance self-test manifest operation"
    if tag != operationName then
      pure operation
    else
      let accepted ← requiredJson operation "accepted"
        "candidate conformance self-test manifest operation"
      let boundary ← requiredJson accepted "externalEvidenceBoundary"
        "candidate conformance self-test manifest accepted"
      pure (operation.setObjVal! "accepted"
        (accepted.setObjVal! "externalEvidenceBoundary"
          (boundary.setObjVal! name value)))
  pure (manifest.setObjVal! "operations" (toJson changed))

private def firstCase (suite : ConformanceSuite) : IO ConformanceCase :=
  match suite.cases with
  | [] => fail "candidate conformance self-test: suite has no cases"
  | testCase :: _ => pure testCase

private def runSelfTest (suitePath : System.FilePath) : IO Unit := do
  let suiteJson ← readJsonFile suitePath
  let canonicalSuite ← parseSuite suiteJson
  validateSupportManifest canonicalSuite
  let manifest ← readJsonFile canonicalSuite.supportManifest
  for testCase in canonicalSuite.cases do
    let _ ← loadAndValidateCaseArtifacts canonicalSuite testCase
    pure ()

  expectFailure "schema version" (do
    let _ ← parseSuite
      (suiteJson.setObjVal! "conformanceSchemaVersion" (toJson 1))
    pure ())

  expectFailure "reference semantics version" (do
    let changed ← parseSuite
      (suiteJson.setObjVal! "referenceSemanticsVersion" (toJson "self-test"))
    validateSupportManifest changed)

  expectFailure "manifest schema version" (do
    let changed ← parseSuite
      (suiteJson.setObjVal! "manifestSchemaVersion" (toJson 999))
    validateSupportManifest changed)

  expectFailure "protocol version" (do
    let changed ← parseSuite
      (suiteJson.setObjVal! "protocolVersion" (toJson 999))
    validateSupportManifest changed)

  expectFailure "kernel behavior version" (do
    let changed ← parseSuite
      (suiteJson.setObjVal! "kernelBehaviorVersion" (toJson "self-test"))
    validateSupportManifest changed)

  expectFailure "suite identity" (do
    let changed ← parseSuite
      (suiteJson.setObjVal! "suiteId" (toJson "self-test"))
    validateSupportManifest changed)

  expectFailure "absent operation" (do
    let changed ← parseSuite
      (suiteJson.setObjVal! "operation" (toJson "self-test"))
    validateSupportManifest changed)

  let operations : List Json ← required manifest "operations"
    "candidate conformance self-test manifest"
  let selectedOperations ← operations.filterM fun operation => do
    let tag : String ← required operation "operation"
      "candidate conformance self-test manifest operation"
    pure (tag == canonicalSuite.operation)
  let selectedOperation ← match selectedOperations with
    | [operation] => pure operation
    | _ => fail "candidate conformance self-test: canonical operation is not unique"
  let duplicatedOperationManifest := manifest.setObjVal! "operations"
    (toJson (operations ++ [selectedOperation]))
  expectFailure "duplicated operation"
    (validateSupportManifestJson canonicalSuite duplicatedOperationManifest
      "self-test support manifest")

  let changedScope ← replaceManifestBoundaryMember manifest canonicalSuite.operation
    "claimScope" (toJson "generalAcceptedInputs")
  expectFailure "finite claim scope"
    (validateSupportManifestJson canonicalSuite changedScope "self-test support manifest")

  let changedCountJson ← replaceFirstEvidenceMember suiteJson "kind"
    (toJson EvidenceKind.kernelStaticDiagnostic.tag)
  expectFailure "retained case counts" (do
    let changed ← parseSuite changedCountJson
    validateSupportManifest changed)

  let incompatibleJson ← replaceFirstEvidenceMember suiteJson "externalSupports"
    (toJson ExternalSupport.elaborationAcceptanceOnly.tag)
  let incompatibleSuite ← parseSuite incompatibleJson
  let incompatibleCase ← firstCase incompatibleSuite
  let incompatibleResponse ← readJsonFile incompatibleCase.expectedResponse
  expectFailure "evidence classification"
    (validateExpectedEvidenceScope incompatibleCase incompatibleResponse)

  let missingEvidenceJson ← replaceFirstEvidenceMember suiteJson "caseId"
    (toJson "self-test-missing-evidence")
  let missingEvidenceSuite ← parseSuite missingEvidenceJson
  let missingEvidenceCase ← firstCase missingEvidenceSuite
  expectFailure "evidence case ID"
    (validateEvidenceLink missingEvidenceSuite missingEvidenceCase)

  expectFailure "duplicate JSON member" (do
    match A12Kernel.Reference.StrictJson.parse
        "{\"suiteId\":\"first\",\"suiteId\":\"second\"}" with
    | .ok _ => pure ()
    | .error error => fail s!"strict parser rejected duplicate member as required: {repr error}")

  expectFailure "unknown suite member" (do
    let _ ← parseSuite (suiteJson.setObjVal! "unexpected" (toJson true))
    pure ())

  let unknownCaseJson ← replaceFirstCaseMember suiteJson "unexpected" (toJson true)
  expectFailure "unknown case member" (do
    let _ ← parseSuite unknownCaseJson
    pure ())

  let unknownEvidenceJson ← replaceFirstEvidenceMember suiteJson "unexpected" (toJson true)
  expectFailure "unknown evidence member" (do
    let _ ← parseSuite unknownEvidenceJson
    pure ())

private def run (args : List String) : IO UInt32 :=
  match args with
  | ["--candidate", candidate, "--suite", suitePath] => do
      let suite ← parseSuite (← readJsonFile suitePath)
      validateSupportManifest suite
      for testCase in suite.cases do
        runCase candidate suite testCase
      IO.println s!"candidate conformance '{suite.id}': {suite.cases.length}/{suite.cases.length} cases passed"
      pure 0
  | ["--self-test", "--suite", suitePath] => do
      runSelfTest suitePath
      IO.println "candidate conformance self-test: 16/16 guards passed"
      pure 0
  | _ => do
      let stderr ← IO.getStderr
      stderr.putStr "checkCandidateConformance: expected --candidate <path> --suite <path> or --self-test --suite <path>\n"
      stderr.flush
      pure 2

def main (args : List String) : IO UInt32 := do
  try
    run args
  catch error =>
    let stderr ← IO.getStderr
    stderr.putStr s!"checkCandidateConformance: {error}\n"
    stderr.flush
    pure 1
