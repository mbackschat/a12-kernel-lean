import A12Kernel.Differential.Generated
import A12Kernel.Process.Bounded
import A12Kernel.Process.Sha256
import Lean.Util.Path

/-! # Bounded generated differential runner

This process-side driver binds a closed generation profile to exact source revisions and executable bytes, runs the Lean reference and one independent candidate sequentially behind the project relay, and records the complete finite comparison. Agreement is only with the pinned Lean account over the generated profile; this run carries no external-kernel evidence.
-/

namespace A12Kernel.Differential.Runner

open Lean
open A12Kernel.Differential.Profile
open A12Kernel.Process
open A12Kernel.Reference

private def fail (message : String) : IO α :=
  throw (IO.userError message)

private structure RunConfig where
  profilePath : System.FilePath
  referenceRepo : System.FilePath
  referenceExecutable : String
  candidateRepo : System.FilePath
  candidateExecutable : String
  resultPath : System.FilePath

private structure LoadedProfile where
  profile : Profile
  cases : List GeneratedCase
  bytes : ByteArray

private structure Distribution where
  notFired : Nat := 0
  firedValue : Nat := 0
  firedOmission : Nat := 0
  unknown : Nat := 0
  deriving Repr, DecidableEq

private def Distribution.add (distribution : Distribution) : ProjectedVerdict → Distribution
  | .notFired => { distribution with notFired := distribution.notFired + 1 }
  | .firedValue => { distribution with firedValue := distribution.firedValue + 1 }
  | .firedOmission => { distribution with firedOmission := distribution.firedOmission + 1 }
  | .unknown => { distribution with unknown := distribution.unknown + 1 }

private def Distribution.asJson (distribution : Distribution) : Json := Json.mkObj [
  ("notFired", toJson distribution.notFired),
  ("fired.value", toJson distribution.firedValue),
  ("fired.omission", toJson distribution.firedOmission),
  ("unknown", toJson distribution.unknown)]

private structure SideSuccess where
  response : Json
  projection : ProjectedVerdict

private structure SideAttempt where
  outputBytes : Nat
  result : Except Json SideSuccess

private structure Disagreement where
  case : GeneratedCase
  reference : SideSuccess
  candidate : SideSuccess

private structure CampaignState where
  processesStarted : Nat := 0
  processInputBytes : Nat := 0
  processOutputBytes : Nat := 0
  elapsedMs : Nat := 0
  completedCases : Nat := 0
  referenceDistribution : Distribution := {}
  candidateDistribution : Distribution := {}
  disagreements : List Disagreement := []
  failure? : Option Json := none
  integrityFailure? : Option Json := none

private structure ArtifactDigests where
  profile : String
  runner : String
  relay : String
  reference : String
  candidate : String

private def CampaignState.hasFailure (state : CampaignState) : Bool :=
  state.failure?.isSome || state.integrityFailure?.isSome

private def maxProfileBytes : Nat := 65536

private def requireRegularFile (label : String) (path : System.FilePath) : IO Unit := do
  let metadata ← try
    path.metadata
  catch error =>
    fail s!"{label} '{path}' is unavailable: {error}"
  if metadata.type != .file then fail s!"{label} '{path}' is not a regular file"

private partial def readBoundedFile (label : String) (handle : IO.FS.Handle) (limit : Nat)
    (accumulator : ByteArray := ByteArray.empty) : IO ByteArray := do
  let remaining := limit + 1 - accumulator.size
  let chunk ← handle.read (USize.ofNat (min remaining 4096))
  if chunk.isEmpty then
    pure accumulator
  else
    let next := accumulator ++ chunk
    if next.size > limit then
      fail s!"{label} exceeds {limit} bytes"
    readBoundedFile label handle limit next

private def readBoundedPath (label : String) (path : System.FilePath) (limit : Nat) : IO ByteArray :=
  IO.FS.withFile path .read fun handle => readBoundedFile label handle limit

private def loadProfile (path : System.FilePath) : IO LoadedProfile := do
  requireRegularFile "profile" path
  let bytes ← readBoundedPath "profile" path maxProfileBytes
  let text ← match String.fromUTF8? bytes with
    | some text => pure text
    | none => fail s!"profile '{path}' is not UTF-8"
  let profile ← parseText text |> IO.ofExcept
  let cases ← generate profile |> IO.ofExcept
  pure { profile, cases, bytes }

private def generatedRequestBytes (cases : List GeneratedCase) : Nat :=
  (cases.map fun generated => generated.request.compress.utf8ByteSize).sum

private def generatedProcessInputBytes (loaded : LoadedProfile) : Nat :=
  (loaded.cases.map fun generated =>
    (generated.request.compress ++ "\n").utf8ByteSize * loaded.profile.execution.processesPerCase).sum

private def isPortableMetadataCharacter (character : Char) : Bool :=
  character.toNat < 0x80 && (character.isAlphanum || ['.', '_', '-'].contains character)

private def validateRelativeExecutable (value : String) : Except String Unit := do
  let path := System.FilePath.mk value
  if value.isEmpty then throw "executable path must not be empty"
  if value.utf8ByteSize > 1024 then throw "executable path exceeds 1024 UTF-8 bytes"
  if path.isAbsolute then throw "executable path must be relative to its pinned repository"
  if value.contains '\\' || value.contains ':' then
    throw "executable path must use portable '/' separators"
  let segments := value.splitOn "/"
  if segments.length > 64 then throw "executable path exceeds 64 segments"
  for segment in segments do
    if segment.isEmpty || segment == "." || segment == ".." then
      throw "executable path contains an empty, current-directory, or parent-directory segment"
    if segment.utf8ByteSize > 255 then throw "executable path segment exceeds 255 UTF-8 bytes"
    if !segment.toList.all isPortableMetadataCharacter then
      throw "executable path contains a non-portable character"

private def isAsciiDigit (character : Char) : Bool :=
  '0' <= character && character <= '9'

private def isDarwinComponent (component : String) : Bool :=
  if component == "darwin" then true
  else if !component.startsWith "darwin" then false
  else
    match (component.drop "darwin".length).toString.toList with
    | [] => false
    | first :: suffix => isAsciiDigit first && suffix.all fun character =>
        isAsciiDigit character || character == '.'

private def platformTargetMatches (platforms : List String) (target : String) : Bool :=
  match target.splitOn "-" with
  | [architecture, "apple", operatingSystem] =>
      platforms.contains "macos" && !architecture.isEmpty && isDarwinComponent operatingSystem
  | [architecture, vendor, "linux"] =>
      platforms.contains "linux" && !architecture.isEmpty && !vendor.isEmpty
  | [architecture, vendor, "linux", abi] =>
      platforms.contains "linux" && !architecture.isEmpty && !vendor.isEmpty && !abi.isEmpty
  | _ => false

private def componentsContained (root path : System.FilePath) : Bool :=
  List.isPrefixOf root.components path.components

private def componentsOverlap (left right : System.FilePath) : Bool :=
  componentsContained left right || componentsContained right left

private def requireContainedRegularFile (label : String) (repo path : System.FilePath) : IO Unit := do
  requireRegularFile label path
  let realRepo ← Lean.realPathNormalized repo
  let realPath ← Lean.realPathNormalized path
  if !componentsContained realRepo realPath then
    fail s!"{label} resolves outside its pinned repository"

private def executableAt (repo : System.FilePath) (relative : String) : IO System.FilePath := do
  validateRelativeExecutable relative |> IO.ofExcept
  let path := repo / relative
  requireContainedRegularFile "executable" repo path
  pure path

private def gitOutput (repo : System.FilePath) (arguments : Array String) : IO IO.Process.Output := do
  try
    IO.Process.output { cmd := "git", args := #["-C", repo.toString] ++ arguments }
  catch error =>
    fail s!"git preflight failed for '{repo}': {error}"

private def requirePinnedCleanRepo (label : String) (repo : System.FilePath)
    (expectedRevision : String) : IO Unit := do
  let topLevel ← gitOutput repo #["rev-parse", "--show-toplevel"]
  if topLevel.exitCode != 0 || !topLevel.stderr.isEmpty then
    fail s!"{label} repository root could not be read"
  let declaredRoot ← Lean.realPathNormalized repo
  let actualRoot ← Lean.realPathNormalized topLevel.stdout.trimAscii.toString
  if actualRoot != declaredRoot then
    fail s!"{label} repository path is not the Git worktree root"
  let head ← gitOutput repo #["rev-parse", "--verify", "HEAD"]
  if head.exitCode != 0 || !head.stderr.isEmpty then
    fail s!"{label} repository HEAD could not be read"
  let actualRevision := head.stdout.trimAscii.toString
  if actualRevision != expectedRevision then
    fail s!"{label} repository HEAD is {actualRevision}, expected {expectedRevision}"
  let status ← gitOutput repo
    #["status", "--porcelain=v1", "--untracked-files=all", "--ignore-submodules=none"]
  if status.exitCode != 0 || !status.stderr.isEmpty then
    fail s!"{label} repository cleanliness could not be checked"
  if !status.stdout.isEmpty then
    fail s!"{label} repository worktree is not clean"

private def requireIndependentRepositories (referenceRepo candidateRepo : System.FilePath) : IO Unit := do
  let referenceRoot ← Lean.realPathNormalized referenceRepo
  let candidateRoot ← Lean.realPathNormalized candidateRepo
  if componentsOverlap referenceRoot candidateRoot then
    fail "reference and candidate repositories must be distinct, non-overlapping Git roots"

private def relayExecutable : IO System.FilePath := do
  let directory ← IO.appDir
  let path := (directory / "a12-bounded-process-relay").addExtension
    System.FilePath.exeExtension
  requireRegularFile "bounded-process relay" path
  pure path

private def requireAbsentResult (path : System.FilePath) : IO Unit := do
  let metadata? ← try
    pure (some (← path.symlinkMetadata))
  catch error =>
    match error with
    | .noFileOrDirectory .. => pure none
    | _ => fail s!"result path '{path}' could not be inspected: {error}"
  if metadata?.isSome then fail s!"result path already exists: '{path}'"

private def requireResultDestination (path referenceRepo candidateRepo : System.FilePath) : IO Unit := do
  if !path.isAbsolute then fail "result path must be absolute"
  if path.toString.utf8ByteSize > 4096 then fail "result path exceeds 4096 UTF-8 bytes"
  let parent ← match path.parent with
    | some parent => pure parent
    | none => fail "result path has no parent"
  let parentMetadata ← try
    parent.symlinkMetadata
  catch error =>
    fail s!"result parent '{parent}' is unavailable: {error}"
  if parentMetadata.type == .symlink then fail "result parent must not be a symlink"
  if parentMetadata.type != .dir then fail "result parent must be an existing directory"
  let realParent ← Lean.realPathNormalized parent
  let referenceRoot ← Lean.realPathNormalized referenceRepo
  let candidateRoot ← Lean.realPathNormalized candidateRepo
  if componentsContained referenceRoot realParent || componentsContained candidateRoot realParent then
    fail "result parent must be outside both pinned repositories"
  requireAbsentResult path

private def captureJson (bytes : ByteArray) : Json :=
  match String.fromUTF8? bytes with
  | some content => Json.mkObj [
      ("bytes", toJson bytes.size),
      ("encoding", toJson "utf8"),
      ("content", toJson content)]
  | none => Json.mkObj [
      ("bytes", toJson bytes.size),
      ("encoding", toJson "byteArray"),
      ("content", toJson (bytes.toList.map UInt8.toNat))]

private def resultMessage (message : String) : String :=
  String.ofList (message.toList.take 1024)

private def killOutcomeJson : Bounded.KillOutcome → Json
  | .killed => Json.mkObj [("tag", toJson "killed")]
  | .alreadyGone => Json.mkObj [("tag", toJson "alreadyGone")]
  | .failed message => Json.mkObj [("tag", toJson "failed"), ("message", toJson (resultMessage message))]

private def boundedFailureKindJson : Bounded.FailureKind → Json
  | .timedOut => Json.mkObj [("tag", toJson "timedOut")]
  | .stdoutLimitExceeded => Json.mkObj [("tag", toJson "stdoutLimitExceeded")]
  | .stderrLimitExceeded => Json.mkObj [("tag", toJson "stderrLimitExceeded")]
  | .stdoutReadFailed message =>
      Json.mkObj [("tag", toJson "stdoutReadFailed"), ("message", toJson (resultMessage message))]
  | .stderrReadFailed message =>
      Json.mkObj [("tag", toJson "stderrReadFailed"), ("message", toJson (resultMessage message))]
  | .waitFailed message =>
      Json.mkObj [("tag", toJson "waitFailed"), ("message", toJson (resultMessage message))]
  | .relayExited exitCode =>
      Json.mkObj [("tag", toJson "relayExited"), ("exitCode", toJson exitCode.toNat)]
  | .relayStatusInvalid message =>
      Json.mkObj [("tag", toJson "relayStatusInvalid"), ("message", toJson (resultMessage message))]
  | .cleanupFailed => Json.mkObj [("tag", toJson "cleanupFailed")]

private def processFailure (side caseId stage : String) (details : Json) : Json := Json.mkObj [
  ("kind", toJson "processFailure"),
  ("side", toJson side),
  ("caseId", toJson caseId),
  ("stage", toJson stage),
  ("details", details)]

private def boundedFailureJson (side caseId : String) (failure : Bounded.Failure) : Json :=
  processFailure side caseId "boundedExecution" <| Json.mkObj [
    ("failure", boundedFailureKindJson failure.kind),
    ("relayExitCode", match failure.relayExitCode? with
      | some value => toJson value.toNat
      | none => Json.null),
    ("cleanup", Json.mkObj [
      ("kill", killOutcomeJson failure.cleanup.kill),
      ("tasksCompleted", toJson failure.cleanup.tasksCompleted),
      ("waitError", match failure.cleanup.waitError? with
        | some message => toJson (resultMessage message)
        | none => Json.null)]),
    ("stdout", captureJson failure.stdout.bytes),
    ("stderr", captureJson failure.stderr.bytes)]

private def contractFailureJson (side caseId stage message : String)
    (output : Bounded.Output) (response? : Option Json := none) : Json :=
  processFailure side caseId stage <| Json.mkObj [
    ("message", toJson (resultMessage message)),
    ("exitCode", toJson output.exitCode.toNat),
    ("stdout", captureJson output.stdout),
    ("stderr", captureJson output.stderr),
    ("response", response?.getD Json.null)]

private def validateOutput (profile : Profile) (side caseId : String)
    (output : Bounded.Output) : Except Json SideSuccess := do
  if output.exitCode != 0 then
    throw (contractFailureJson side caseId "exitStatus" "process returned a nonzero exit status" output)
  if !output.stderr.isEmpty then
    throw (contractFailureJson side caseId "stderr" "process wrote to stderr" output)
  let text ← match String.fromUTF8? output.stdout with
    | some text => pure text
    | none => throw (contractFailureJson side caseId "stdoutUtf8" "stdout is not UTF-8" output)
  if !text.endsWith "\n" then
    throw (contractFailureJson side caseId "stdoutNewline" "stdout does not end in one newline" output)
  let body := (text.dropEnd 1).toString
  if body.isEmpty || body.contains "\n" || body.contains "\r" then
    throw (contractFailureJson side caseId "stdoutNewline" "stdout is not exactly one JSON line" output)
  let response ← match StrictJson.parse body with
    | .ok response => pure response
    | .error error =>
        throw (contractFailureJson side caseId "responseJson"
          s!"stdout is not strict JSON: {repr error}" output)
  let projection ← match projectResponse profile response with
    | .ok projection => pure projection
    | .error error =>
        throw (contractFailureJson side caseId "responseProjection" error output (some response))
  pure { response, projection }

private def invokeSide (relay executable : System.FilePath) (profile : Profile)
    (side : String) (generated : GeneratedCase) : IO SideAttempt := do
  let input := generated.request.compress ++ "\n"
  let limits : Bounded.Limits := {
    timeoutMs := profile.bounds.processTimeoutMilliseconds
    cleanupMs := profile.bounds.processCleanupMilliseconds
    pollMs := profile.bounds.processPollMilliseconds
    inputBytes := profile.bounds.requestBytes + 1
    stdoutBytes := profile.bounds.processStdoutBytes
    stderrBytes := profile.bounds.processStderrBytes }
  try
    match ← Bounded.runViaRelay relay executable #[] input limits with
    | .error failure =>
        pure {
          outputBytes := failure.stdout.bytes.size + failure.stderr.bytes.size
          result := .error (boundedFailureJson side generated.id failure) }
    | .ok output =>
        pure {
          outputBytes := output.stdout.size + output.stderr.size
          result := validateOutput profile side generated.id output }
  catch error =>
    pure {
      outputBytes := 0
      result := .error (processFailure side generated.id "invocation"
        (Json.mkObj [("message", toJson (resultMessage (toString error)))])) }

private def budgetFailure (side caseId budget : String) (used maximum : Nat) : Json :=
  processFailure side caseId "aggregateBudget" <| Json.mkObj [
    ("budget", toJson budget),
    ("usedOrReserved", toJson used),
    ("maximum", toJson maximum)]

private def prepareInvocation (profile : Profile) (state : CampaignState)
    (side : String) (generated : GeneratedCase) : Except Json CampaignState := do
  let inputBytes := (generated.request.compress ++ "\n").utf8ByteSize
  let nextInput := state.processInputBytes + inputBytes
  if nextInput > profile.bounds.aggregateProcessInputBytes then
    throw (budgetFailure side generated.id "aggregateProcessInputBytes"
      nextInput profile.bounds.aggregateProcessInputBytes)
  let reservedOutput := state.processOutputBytes +
    profile.bounds.processStdoutBytes + profile.bounds.processStderrBytes
  if reservedOutput > profile.bounds.aggregateProcessOutputBytes then
    throw (budgetFailure side generated.id "aggregateProcessOutputBytes"
      reservedOutput profile.bounds.aggregateProcessOutputBytes)
  let reservedElapsed := state.elapsedMs + profile.bounds.processTimeoutMilliseconds +
    profile.bounds.processCleanupMilliseconds
  if reservedElapsed > profile.bounds.aggregateElapsedMilliseconds then
    throw (budgetFailure side generated.id "aggregateElapsedMilliseconds"
      reservedElapsed profile.bounds.aggregateElapsedMilliseconds)
  pure {
    state with
    processesStarted := state.processesStarted + 1
    processInputBytes := nextInput }

private def consumeAttempt (profile : Profile) (state : CampaignState) (side caseId : String)
    (attempt : SideAttempt) : CampaignState :=
  let outputBytes := state.processOutputBytes + attempt.outputBytes
  let state := { state with processOutputBytes := outputBytes }
  if outputBytes > profile.bounds.aggregateProcessOutputBytes then
    { state with failure? := some (budgetFailure side caseId "aggregateProcessOutputBytes"
        outputBytes profile.bounds.aggregateProcessOutputBytes) }
  else
    match attempt.result with
    | .error failure => { state with failure? := some failure }
    | .ok _ => state

private def updateCampaignElapsed (profile : Profile) (state : CampaignState)
    (campaignStartedAt : Nat) (side caseId : String) : IO CampaignState := do
  let elapsedMs := (← IO.monoMsNow) - campaignStartedAt
  let state := { state with elapsedMs }
  if elapsedMs > profile.bounds.aggregateElapsedMilliseconds && state.failure?.isNone then
    pure { state with failure? := some (budgetFailure side caseId "aggregateElapsedMilliseconds"
      elapsedMs profile.bounds.aggregateElapsedMilliseconds) }
  else
    pure state

private partial def runCases (relay reference candidate : System.FilePath) (profile : Profile)
    (campaignStartedAt : Nat) (remaining : List GeneratedCase)
    (state : CampaignState := {}) : IO CampaignState := do
  if state.failure?.isSome then return state
  match remaining with
  | [] => updateCampaignElapsed profile state campaignStartedAt "campaign" "complete"
  | generated :: rest =>
      let state ← updateCampaignElapsed profile state campaignStartedAt "reference" generated.id
      if state.failure?.isSome then return state
      let state ← match prepareInvocation profile state "reference" generated with
        | .ok state => pure state
        | .error failure => return { state with failure? := some failure }
      let referenceAttempt ← invokeSide relay reference profile "reference" generated
      let state := consumeAttempt profile state "reference" generated.id referenceAttempt
      let state ← updateCampaignElapsed profile state campaignStartedAt "reference" generated.id
      if state.failure?.isSome then return state
      let referenceResult ← match referenceAttempt.result with
        | .ok result => pure result
        | .error _ => fail "internal differential state lost a reference process failure"
      let state ← match prepareInvocation profile state "candidate" generated with
        | .ok state => pure state
        | .error failure => return { state with failure? := some failure }
      let candidateAttempt ← invokeSide relay candidate profile "candidate" generated
      let state := consumeAttempt profile state "candidate" generated.id candidateAttempt
      let state ← updateCampaignElapsed profile state campaignStartedAt "candidate" generated.id
      if state.failure?.isSome then return state
      let candidateResult ← match candidateAttempt.result with
        | .ok result => pure result
        | .error _ => fail "internal differential state lost a candidate process failure"
      let disagreement? := referenceResult.projection != candidateResult.projection
      let state := {
        state with
        completedCases := state.completedCases + 1
        referenceDistribution := state.referenceDistribution.add referenceResult.projection
        candidateDistribution := state.candidateDistribution.add candidateResult.projection
        disagreements := if disagreement? then state.disagreements ++ [{
          case := generated, reference := referenceResult, candidate := candidateResult }]
        else state.disagreements }
      runCases relay reference candidate profile campaignStartedAt rest state

private def metricsJson (metrics : Metrics) : Json := Json.mkObj [
  ("fields", toJson metrics.fields),
  ("cells", toJson metrics.cells),
  ("conditionDepth", toJson metrics.conditionDepth),
  ("conditionNodes", toJson metrics.conditionNodes)]

private def sideJson (side : SideSuccess) : Json := Json.mkObj [
  ("projection", toJson side.projection.tag),
  ("response", side.response)]

private def disagreementJson (disagreement : Disagreement) : Json := Json.mkObj [
  ("caseId", toJson disagreement.case.id),
  ("family", toJson disagreement.case.family.tag),
  ("metrics", metricsJson disagreement.case.metrics),
  ("request", disagreement.case.request),
  ("reference", sideJson disagreement.reference),
  ("candidate", sideJson disagreement.candidate)]

private def sameProjectedPair (left right : Disagreement) : Bool :=
  left.reference.projection == right.reference.projection &&
    left.candidate.projection == right.candidate.projection

private def witnessAtMost (left right : Disagreement) : Bool :=
  if left.case.metrics.conditionNodes != right.case.metrics.conditionNodes then
    left.case.metrics.conditionNodes < right.case.metrics.conditionNodes
  else
    let leftBytes := left.case.request.compress.utf8ByteSize
    let rightBytes := right.case.request.compress.utf8ByteSize
    if leftBytes != rightBytes then leftBytes < rightBytes else left.case.id <= right.case.id

private def minimalWitnesses (disagreements : List Disagreement) : List Disagreement :=
  let selected := disagreements.foldl (init := []) fun witnesses disagreement =>
    match witnesses.find? (sameProjectedPair disagreement) with
    | none => witnesses ++ [disagreement]
    | some current =>
        if witnessAtMost disagreement current then
          witnesses.map fun witness => if sameProjectedPair witness disagreement then disagreement else witness
        else witnesses
  selected.mergeSort witnessAtMost

private def witnessJson (disagreement : Disagreement) : Json := Json.mkObj [
  ("referenceProjection", toJson disagreement.reference.projection.tag),
  ("candidateProjection", toJson disagreement.candidate.projection.tag),
  ("caseId", toJson disagreement.case.id),
  ("conditionNodes", toJson disagreement.case.metrics.conditionNodes),
  ("requestBytes", toJson disagreement.case.request.compress.utf8ByteSize)]

private def compatibilityJson (profile : Profile) : Json := Json.mkObj [
  ("capabilityId", toJson profile.compatibility.capabilityId),
  ("operation", toJson profile.compatibility.operation),
  ("referenceSemanticsVersion", toJson profile.compatibility.referenceSemanticsVersion),
  ("protocolVersion", toJson profile.compatibility.protocolVersion),
  ("manifestSchemaVersion", toJson profile.compatibility.manifestSchemaVersion),
  ("kernelBehaviorVersion", toJson profile.compatibility.kernelBehaviorVersion)]

private def budgetsJson (profile : Profile) (state : CampaignState)
    (generatedRequestBytes plannedProcessInputBytes : Nat) : Json := Json.mkObj [
  ("declared", Json.mkObj [
    ("cases", toJson profile.bounds.cases),
    ("requestBytes", toJson profile.bounds.requestBytes),
    ("aggregateRequestBytes", toJson profile.bounds.aggregateRequestBytes),
    ("aggregateProcessInputBytes", toJson profile.bounds.aggregateProcessInputBytes),
    ("processTimeoutMilliseconds", toJson profile.bounds.processTimeoutMilliseconds),
    ("processCleanupMilliseconds", toJson profile.bounds.processCleanupMilliseconds),
    ("processPollMilliseconds", toJson profile.bounds.processPollMilliseconds),
    ("aggregateElapsedMilliseconds", toJson profile.bounds.aggregateElapsedMilliseconds),
    ("processStdoutBytes", toJson profile.bounds.processStdoutBytes),
    ("processStderrBytes", toJson profile.bounds.processStderrBytes),
    ("aggregateProcessOutputBytes", toJson profile.bounds.aggregateProcessOutputBytes),
    ("resultBytes", toJson profile.bounds.resultBytes)]),
  ("usage", Json.mkObj [
    ("generatedRequestBytes", toJson generatedRequestBytes),
    ("plannedProcessInputBytes", toJson plannedProcessInputBytes),
    ("processInputBytes", toJson state.processInputBytes),
    ("processOutputBytes", toJson state.processOutputBytes),
    ("elapsedMilliseconds", toJson state.elapsedMs)])]

private def artifactJson (path? : Option String) (sha256 : String) : Json := Json.mkObj <|
  (match path? with | some path => [("path", toJson path)] | none => []) ++
    [("sha256", toJson sha256)]

private def postflightIntegrityFailure? (loaded : LoadedProfile) (config : RunConfig)
    (runner relay reference candidate : System.FilePath) (digests : ArtifactDigests) :
    IO (Option Json) := do
  try
    requirePinnedCleanRepo "reference" config.referenceRepo loaded.profile.revisions.reference
    requirePinnedCleanRepo "candidate" config.candidateRepo loaded.profile.revisions.candidate
    requireIndependentRepositories config.referenceRepo config.candidateRepo
    requireContainedRegularFile "generated-differential runner" config.referenceRepo runner
    requireContainedRegularFile "bounded-process relay" config.referenceRepo relay
    requireContainedRegularFile "reference executable" config.referenceRepo reference
    requireContainedRegularFile "candidate executable" config.candidateRepo candidate
    if (← readBoundedPath "profile" config.profilePath maxProfileBytes) != loaded.bytes then
      fail "profile bytes changed during execution"
    for (label, path, expected) in [
        ("profile", config.profilePath, digests.profile),
        ("runner", runner, digests.runner),
        ("relay", relay, digests.relay),
        ("reference", reference, digests.reference),
        ("candidate", candidate, digests.candidate)] do
      if (← Sha256.file path) != expected then fail s!"{label} digest changed during execution"
    pure none
  catch _ =>
    pure (some <| Json.mkObj [
      ("kind", toJson "inputIntegrityFailure"),
      ("stage", toJson "postflight"),
      ("message", toJson "a pinned revision, worktree, profile, or executable changed or became unreadable during execution")])

private def resultJson (loaded : LoadedProfile) (config : RunConfig) (digests : ArtifactDigests)
    (state : CampaignState) : Json :=
  let outcome := if state.integrityFailure?.isSome then "integrityFailure"
    else if state.failure?.isSome then "processFailure"
    else if state.disagreements.isEmpty then "agree" else "disagreement"
  let generatedBytes := generatedRequestBytes loaded.cases
  let plannedInputBytes := generatedProcessInputBytes loaded
  Json.mkObj [
    ("schemaVersion", toJson 1),
    ("profileSchemaVersion", toJson schemaVersion),
    ("profileId", toJson loaded.profile.id),
    ("responseProjection", toJson loaded.profile.responseProjection.tag),
    ("observableVerdicts", toJson loaded.profile.observableVerdicts),
    ("compatibility", compatibilityJson loaded.profile),
    ("revisions", Json.mkObj [
      ("referenceRepository", toJson loaded.profile.revisions.referenceRepository),
      ("reference", toJson loaded.profile.revisions.reference),
      ("candidateRepository", toJson loaded.profile.revisions.candidateRepository),
      ("candidate", toJson loaded.profile.revisions.candidate)]),
    ("execution", Json.mkObj [
      ("platformTarget", toJson System.Platform.target),
      ("strategy", toJson loaded.profile.execution.strategy),
      ("jobs", toJson loaded.profile.execution.jobs)]),
    ("artifacts", Json.mkObj [
      ("profile", artifactJson none digests.profile),
      ("runner", artifactJson none digests.runner),
      ("relay", artifactJson none digests.relay),
      ("reference", artifactJson (some config.referenceExecutable) digests.reference),
      ("candidate", artifactJson (some config.candidateExecutable) digests.candidate)]),
    ("claim", Json.mkObj [
      ("class", toJson "finiteLeanAccountDifferential"),
      ("scope", toJson "generatedProfileCasesOnly"),
      ("leanAccountAgreement", toJson (outcome == "agree")),
      ("kernelEvidence", toJson "none"),
      ("externalKernelCorrespondence", toJson false)]),
    ("outcome", toJson outcome),
    ("budgets", budgetsJson loaded.profile state generatedBytes plannedInputBytes),
    ("counts", Json.mkObj [
      ("generatedCases", toJson loaded.cases.length),
      ("completedCases", toJson state.completedCases),
      ("agreements", toJson (state.completedCases - state.disagreements.length)),
      ("disagreements", toJson state.disagreements.length),
      ("processesStarted", toJson state.processesStarted)]),
    ("distribution", Json.mkObj [
      ("reference", state.referenceDistribution.asJson),
      ("candidate", state.candidateDistribution.asJson)]),
    ("disagreements", Json.arr (state.disagreements.map disagreementJson).toArray),
    ("minimalWitnesses", Json.arr (minimalWitnesses state.disagreements |>.map witnessJson).toArray),
    ("failure", state.failure?.getD Json.null),
    ("integrityFailure", state.integrityFailure?.getD Json.null)]

/-! ### Retained agreement-result validation

The retained-result gate accepts only a complete green agreement receipt. It checks that Git-reviewed historical record for exact profile identity and internal consistency without authenticating the historical execution or rebuilding and rehashing its platform-specific executables; disagreement and failure records remain run outputs for immediate classification rather than admitted retained receipts.
-/

private structure ResultUsage where
  generatedRequestBytes : Nat
  plannedProcessInputBytes : Nat
  processInputBytes : Nat
  processOutputBytes : Nat
  elapsedMilliseconds : Nat

private structure ResultCounts where
  generatedCases : Nat
  completedCases : Nat
  agreements : Nat
  disagreements : Nat
  processesStarted : Nat

private def resultChild (context name : String) : String :=
  if context == "$" then s!"$.{name}" else s!"{context}.{name}"

private def resultRequireObject (json : Json) (context : String) (allowed : List String) :
    Except String Unit := do
  let object ← match json.getObj? with
    | .ok object => pure object
    | .error _ => throw s!"result {context}: expected object"
  for (name, _) in object.toList do
    if !allowed.contains name then throw s!"result {resultChild context name}: unknown member"

private def resultRequiredJson (json : Json) (context name : String) : Except String Json :=
  match json.getObjVal? name with
  | .ok value => pure value
  | .error _ => throw s!"result {resultChild context name}: missing member"

private def resultRequired [FromJson α] (json : Json) (context name : String) : Except String α := do
  let value ← resultRequiredJson json context name
  match fromJson? value with
  | .ok decoded => pure decoded
  | .error _ => throw s!"result {resultChild context name}: wrong type"

private def resultRequireEqual [BEq α] (context : String) (actual expected : α) :
    Except String Unit :=
  if actual == expected then pure ()
  else throw s!"result {context}: value does not match the bound profile or schema"

private def parseResultDistribution (json : Json) (context : String) : Except String Distribution := do
  resultRequireObject json context ["notFired", "fired.value", "fired.omission", "unknown"]
  pure {
    notFired := ← resultRequired json context "notFired"
    firedValue := ← resultRequired json context "fired.value"
    firedOmission := ← resultRequired json context "fired.omission"
    unknown := ← resultRequired json context "unknown" }

private def Distribution.total (distribution : Distribution) : Nat :=
  distribution.notFired + distribution.firedValue + distribution.firedOmission +
    distribution.unknown

private def expectedReferenceDistribution (profile : Profile) (cases : List GeneratedCase) :
    Except String Distribution := do
  let mut distribution : Distribution := {}
  for generated in cases do
    distribution := distribution.add (← evaluateReference profile generated)
  pure distribution

private def validateCompatibilityRecord (profile : Profile) (json : Json) : Except String Unit := do
  let context := "$.compatibility"
  resultRequireObject json context ["capabilityId", "operation", "referenceSemanticsVersion",
    "protocolVersion", "manifestSchemaVersion", "kernelBehaviorVersion"]
  resultRequireEqual s!"{context}.capabilityId" (← resultRequired json context "capabilityId")
    profile.compatibility.capabilityId
  resultRequireEqual s!"{context}.operation" (← resultRequired json context "operation")
    profile.compatibility.operation
  resultRequireEqual s!"{context}.referenceSemanticsVersion"
    (← resultRequired json context "referenceSemanticsVersion")
    profile.compatibility.referenceSemanticsVersion
  resultRequireEqual s!"{context}.protocolVersion" (← resultRequired json context "protocolVersion")
    profile.compatibility.protocolVersion
  resultRequireEqual s!"{context}.manifestSchemaVersion"
    (← resultRequired json context "manifestSchemaVersion") profile.compatibility.manifestSchemaVersion
  resultRequireEqual s!"{context}.kernelBehaviorVersion"
    (← resultRequired json context "kernelBehaviorVersion") profile.compatibility.kernelBehaviorVersion

private def validateRevisionRecord (profile : Profile) (json : Json) : Except String Unit := do
  let context := "$.revisions"
  resultRequireObject json context ["referenceRepository", "reference", "candidateRepository", "candidate"]
  resultRequireEqual s!"{context}.referenceRepository"
    (← resultRequired json context "referenceRepository") profile.revisions.referenceRepository
  resultRequireEqual s!"{context}.reference" (← resultRequired json context "reference")
    profile.revisions.reference
  resultRequireEqual s!"{context}.candidateRepository"
    (← resultRequired json context "candidateRepository") profile.revisions.candidateRepository
  resultRequireEqual s!"{context}.candidate" (← resultRequired json context "candidate")
    profile.revisions.candidate

private def validateDeclaredBudgets (profile : Profile) (json : Json) : Except String Unit := do
  let context := "$.budgets.declared"
  resultRequireObject json context ["cases", "requestBytes", "aggregateRequestBytes",
    "aggregateProcessInputBytes", "processTimeoutMilliseconds", "processCleanupMilliseconds",
    "processPollMilliseconds", "aggregateElapsedMilliseconds", "processStdoutBytes",
    "processStderrBytes", "aggregateProcessOutputBytes", "resultBytes"]
  for (name, expected) in [
      ("cases", profile.bounds.cases),
      ("requestBytes", profile.bounds.requestBytes),
      ("aggregateRequestBytes", profile.bounds.aggregateRequestBytes),
      ("aggregateProcessInputBytes", profile.bounds.aggregateProcessInputBytes),
      ("processTimeoutMilliseconds", profile.bounds.processTimeoutMilliseconds),
      ("processCleanupMilliseconds", profile.bounds.processCleanupMilliseconds),
      ("processPollMilliseconds", profile.bounds.processPollMilliseconds),
      ("aggregateElapsedMilliseconds", profile.bounds.aggregateElapsedMilliseconds),
      ("processStdoutBytes", profile.bounds.processStdoutBytes),
      ("processStderrBytes", profile.bounds.processStderrBytes),
      ("aggregateProcessOutputBytes", profile.bounds.aggregateProcessOutputBytes),
      ("resultBytes", profile.bounds.resultBytes)] do
    resultRequireEqual s!"{context}.{name}" (← resultRequired json context name) expected

private def parseResultUsage (json : Json) : Except String ResultUsage := do
  let context := "$.budgets.usage"
  resultRequireObject json context ["generatedRequestBytes", "plannedProcessInputBytes",
    "processInputBytes", "processOutputBytes", "elapsedMilliseconds"]
  pure {
    generatedRequestBytes := ← resultRequired json context "generatedRequestBytes"
    plannedProcessInputBytes := ← resultRequired json context "plannedProcessInputBytes"
    processInputBytes := ← resultRequired json context "processInputBytes"
    processOutputBytes := ← resultRequired json context "processOutputBytes"
    elapsedMilliseconds := ← resultRequired json context "elapsedMilliseconds" }

private def parseResultCounts (json : Json) : Except String ResultCounts := do
  let context := "$.counts"
  resultRequireObject json context ["generatedCases", "completedCases", "agreements",
    "disagreements", "processesStarted"]
  pure {
    generatedCases := ← resultRequired json context "generatedCases"
    completedCases := ← resultRequired json context "completedCases"
    agreements := ← resultRequired json context "agreements"
    disagreements := ← resultRequired json context "disagreements"
    processesStarted := ← resultRequired json context "processesStarted" }

private def validateResultJson (loaded : LoadedProfile) (profileDigest : String) (json : Json) :
    Except String Unit := do
  resultRequireObject json "$" ["schemaVersion", "profileSchemaVersion", "profileId",
    "responseProjection", "observableVerdicts", "compatibility", "revisions", "execution",
    "artifacts", "claim", "outcome", "budgets", "counts", "distribution", "disagreements",
    "minimalWitnesses", "failure", "integrityFailure"]
  resultRequireEqual "$.schemaVersion" (← resultRequired json "$" "schemaVersion") 1
  resultRequireEqual "$.profileSchemaVersion" (← resultRequired json "$" "profileSchemaVersion")
    schemaVersion
  resultRequireEqual "$.profileId" (← resultRequired json "$" "profileId") loaded.profile.id
  resultRequireEqual "$.responseProjection" (← resultRequired json "$" "responseProjection")
    loaded.profile.responseProjection.tag
  resultRequireEqual "$.observableVerdicts" (← resultRequired json "$" "observableVerdicts")
    loaded.profile.observableVerdicts
  validateCompatibilityRecord loaded.profile (← resultRequiredJson json "$" "compatibility")
  validateRevisionRecord loaded.profile (← resultRequiredJson json "$" "revisions")

  let execution ← resultRequiredJson json "$" "execution"
  resultRequireObject execution "$.execution" ["platformTarget", "strategy", "jobs"]
  let platformTarget : String ← resultRequired execution "$.execution" "platformTarget"
  if platformTarget.isEmpty || platformTarget.utf8ByteSize > 255 ||
      !platformTarget.toList.all isPortableMetadataCharacter then
    throw "result $.execution.platformTarget: must be a portable nonempty target of at most 255 bytes"
  if !platformTargetMatches loaded.profile.execution.platforms platformTarget then
    throw "result $.execution.platformTarget: target is outside the profile's declared platforms"
  resultRequireEqual "$.execution.strategy" (← resultRequired execution "$.execution" "strategy")
    loaded.profile.execution.strategy
  resultRequireEqual "$.execution.jobs" (← resultRequired execution "$.execution" "jobs")
    loaded.profile.execution.jobs

  let artifacts ← resultRequiredJson json "$" "artifacts"
  resultRequireObject artifacts "$.artifacts" ["profile", "runner", "relay", "reference", "candidate"]
  for name in ["profile", "runner", "relay", "reference", "candidate"] do
    let artifact ← resultRequiredJson artifacts "$.artifacts" name
    let allowed := if name == "reference" || name == "candidate" then ["path", "sha256"] else ["sha256"]
    let context := s!"$.artifacts.{name}"
    resultRequireObject artifact context allowed
    let digest : String ← resultRequired artifact context "sha256"
    if !Sha256.isDigest digest then throw s!"result {context}.sha256: expected lowercase SHA-256"
    if name == "profile" then resultRequireEqual s!"{context}.sha256" digest profileDigest
    if name == "reference" || name == "candidate" then
      validateRelativeExecutable (← resultRequired artifact context "path")

  let budgets ← resultRequiredJson json "$" "budgets"
  resultRequireObject budgets "$.budgets" ["declared", "usage"]
  validateDeclaredBudgets loaded.profile (← resultRequiredJson budgets "$.budgets" "declared")
  let usage ← parseResultUsage (← resultRequiredJson budgets "$.budgets" "usage")
  let generatedBytes := generatedRequestBytes loaded.cases
  let plannedInput := generatedProcessInputBytes loaded
  resultRequireEqual "$.budgets.usage.generatedRequestBytes" usage.generatedRequestBytes generatedBytes
  resultRequireEqual "$.budgets.usage.plannedProcessInputBytes" usage.plannedProcessInputBytes plannedInput
  resultRequireEqual "$.budgets.usage.processInputBytes" usage.processInputBytes plannedInput
  if usage.processOutputBytes > loaded.profile.bounds.aggregateProcessOutputBytes then
    throw "result $.budgets.usage.processOutputBytes: exceeds declared bound"
  if usage.elapsedMilliseconds > loaded.profile.bounds.aggregateElapsedMilliseconds then
    throw "result $.budgets.usage.elapsedMilliseconds: exceeds declared bound"

  let counts ← parseResultCounts (← resultRequiredJson json "$" "counts")
  resultRequireEqual "$.counts.generatedCases" counts.generatedCases loaded.cases.length
  resultRequireEqual "$.counts.completedCases" counts.completedCases loaded.cases.length
  resultRequireEqual "$.counts.agreements" counts.agreements loaded.cases.length
  resultRequireEqual "$.counts.disagreements" counts.disagreements 0
  resultRequireEqual "$.counts arithmetic" (counts.agreements + counts.disagreements)
    counts.completedCases
  resultRequireEqual "$.counts.processesStarted" counts.processesStarted
    (loaded.cases.length * loaded.profile.execution.processesPerCase)
  let disagreements : List Json ← resultRequired json "$" "disagreements"
  if !disagreements.isEmpty then throw "result $.disagreements: retained agreement receipt must be empty"
  let witnesses : List Json ← resultRequired json "$" "minimalWitnesses"
  if !witnesses.isEmpty then throw "result $.minimalWitnesses: retained agreement receipt must be empty"

  let distribution ← resultRequiredJson json "$" "distribution"
  resultRequireObject distribution "$.distribution" ["reference", "candidate"]
  let referenceDistribution ← parseResultDistribution
    (← resultRequiredJson distribution "$.distribution" "reference") "$.distribution.reference"
  let candidateDistribution ← parseResultDistribution
    (← resultRequiredJson distribution "$.distribution" "candidate") "$.distribution.candidate"
  resultRequireEqual "$.distribution.reference total" referenceDistribution.total counts.completedCases
  resultRequireEqual "$.distribution.candidate total" candidateDistribution.total counts.completedCases
  let expectedReference ← expectedReferenceDistribution loaded.profile loaded.cases
  resultRequireEqual "$.distribution.reference" referenceDistribution expectedReference
  resultRequireEqual "$.distribution.candidate" candidateDistribution expectedReference
  resultRequireEqual "$.outcome" (← resultRequired json "$" "outcome") "agree"
  resultRequireEqual "$.failure" (← resultRequiredJson json "$" "failure") Json.null
  resultRequireEqual "$.integrityFailure" (← resultRequiredJson json "$" "integrityFailure") Json.null

  let claim ← resultRequiredJson json "$" "claim"
  resultRequireObject claim "$.claim" ["class", "scope", "leanAccountAgreement",
    "kernelEvidence", "externalKernelCorrespondence"]
  resultRequireEqual "$.claim.class" (← resultRequired claim "$.claim" "class")
    "finiteLeanAccountDifferential"
  resultRequireEqual "$.claim.scope" (← resultRequired claim "$.claim" "scope")
    "generatedProfileCasesOnly"
  resultRequireEqual "$.claim.kernelEvidence" (← resultRequired claim "$.claim" "kernelEvidence") "none"
  resultRequireEqual "$.claim.externalKernelCorrespondence"
    (← resultRequired claim "$.claim" "externalKernelCorrespondence") false
  resultRequireEqual "$.claim.leanAccountAgreement"
    (← resultRequired claim "$.claim" "leanAccountAgreement") true

private def parseAndValidateResult (loaded : LoadedProfile) (profileDigest : String)
    (bytes : ByteArray) : Except String Unit := do
  let input ← match String.fromUTF8? bytes with
    | some input => pure input
    | none => throw "result is not UTF-8"
  let json ← match StrictJson.parse input with
    | .ok json => pure json
    | .error error => throw s!"invalid result JSON: {repr error}"
  validateResultJson loaded profileDigest json

private def checkResult (profilePath resultPath : System.FilePath) : IO Unit := do
  let loaded ← loadProfile profilePath
  requireRegularFile "result" resultPath
  let bytes ← readBoundedPath "result" resultPath loaded.profile.bounds.resultBytes
  let profileDigest ← Sha256.file profilePath
  parseAndValidateResult loaded profileDigest bytes |> IO.ofExcept
  IO.println s!"generated differential agreement-result check: {loaded.cases.length}/{loaded.profile.bounds.cases} cases bound to profile sha256={profileDigest}; no historical executable digest replay"

private def writeResult (path : System.FilePath) (maximumBytes : Nat) (json : Json) : IO Unit := do
  let content := json.compress ++ "\n"
  if content.utf8ByteSize > maximumBytes then
    fail s!"result requires {content.utf8ByteSize} bytes, profile permits {maximumBytes}"
  IO.FS.withFile path .writeNew fun handle => do
    handle.write content.toUTF8
    handle.flush

private def checkProfile (path : System.FilePath) : IO Unit := do
  let loaded ← loadProfile path
  let profileDigest ← Sha256.file path
  IO.println s!"generated differential profile check: {loaded.cases.length}/{loaded.profile.bounds.cases} cases; request bytes={generatedRequestBytes loaded.cases}/{loaded.profile.bounds.aggregateRequestBytes}; dual-process input bytes={generatedProcessInputBytes loaded}/{loaded.profile.bounds.aggregateProcessInputBytes}; result bytes≤{loaded.profile.bounds.resultBytes}; sha256={profileDigest}"

private def run (config : RunConfig) : IO UInt32 := do
  if !Bounded.supportedHost then
    fail s!"generated differential supports only macOS and Linux, found '{System.Platform.target}'"
  let loaded ← loadProfile config.profilePath
  let plannedInputBytes := generatedProcessInputBytes loaded
  if plannedInputBytes > loaded.profile.bounds.aggregateProcessInputBytes then
    fail "generated dual-process inputs exceed the aggregate process-input budget"
  requirePinnedCleanRepo "reference" config.referenceRepo loaded.profile.revisions.reference
  requirePinnedCleanRepo "candidate" config.candidateRepo loaded.profile.revisions.candidate
  requireIndependentRepositories config.referenceRepo config.candidateRepo
  requireResultDestination config.resultPath config.referenceRepo config.candidateRepo
  let reference ← executableAt config.referenceRepo config.referenceExecutable
  let candidate ← executableAt config.candidateRepo config.candidateExecutable
  let relay ← relayExecutable
  let runner ← IO.appPath
  requireContainedRegularFile "generated-differential runner" config.referenceRepo runner
  requireContainedRegularFile "bounded-process relay" config.referenceRepo relay
  let digests : ArtifactDigests := {
    profile := ← Sha256.file config.profilePath
    runner := ← Sha256.file runner
    relay := ← Sha256.file relay
    reference := ← Sha256.file reference
    candidate := ← Sha256.file candidate }
  let campaignStartedAt ← IO.monoMsNow
  let state ← runCases relay reference candidate loaded.profile campaignStartedAt loaded.cases
  let integrityFailure? ← postflightIntegrityFailure? loaded config
    runner relay reference candidate digests
  let state := { state with integrityFailure? }
  requireResultDestination config.resultPath config.referenceRepo config.candidateRepo
  writeResult config.resultPath loaded.profile.bounds.resultBytes
    (resultJson loaded config digests state)
  if state.hasFailure then
    IO.eprintln s!"generated differential failed after {state.completedCases}/{loaded.cases.length} completed cases; result: {config.resultPath}"
    pure 1
  else if !state.disagreements.isEmpty then
    IO.eprintln s!"generated differential found {state.disagreements.length} disagreements in {state.completedCases} cases; result: {config.resultPath}"
    pure 1
  else
    IO.println s!"generated differential: {state.completedCases}/{loaded.cases.length} finite Lean-account cases agree; no kernel evidence; result: {config.resultPath}"
    pure 0

private def testCase (id : String) (nodes requestPad : Nat) : GeneratedCase := {
  id
  family := .verdictAlgebra
  request := Json.mkObj [("pad", toJson (String.ofList (List.replicate requestPad 'x')))]
  metrics := { fields := 3, cells := 0, conditionDepth := nodes, conditionNodes := nodes } }

private def testSide (projection : ProjectedVerdict) : SideSuccess := {
  response := Json.mkObj [("test", toJson true)]
  projection }

private def testProfile : Profile := {
  id := profileId
  compatibility := {
    capabilityId := "flat-validation-empty-logic-v1"
    operation := Support.Operation.flatValidationEvaluateFull.tag
    referenceSemanticsVersion := Support.referenceSemanticsVersion
    protocolVersion := Support.protocolVersion
    manifestSchemaVersion := Support.manifestSchemaVersion
    kernelBehaviorVersion := Support.kernelBehaviorVersion }
  revisions := {
    referenceRepository := "a12-kernel-lean"
    reference := String.ofList (List.replicate 40 '0')
    candidateRepository := "a12-kernel-rust-spike"
    candidate := String.ofList (List.replicate 40 '1') }
  responseProjection := .flatVerdictV1
  observableVerdicts := ProjectedVerdict.all.map ProjectedVerdict.tag
  bounds := {
    cases := expectedCaseCount
    requestBytes := 4096
    fields := 3
    cells := 2
    conditionDepth := 2
    conditionNodes := 3
    aggregateRequestBytes := 65536
    aggregateProcessInputBytes := 131072
    processTimeoutMilliseconds := 2000
    processCleanupMilliseconds := 1000
    processPollMilliseconds := 5
    aggregateElapsedMilliseconds := 30000
    processStdoutBytes := 4096
    processStderrBytes := 4096
    aggregateProcessOutputBytes := 524288
    resultBytes := 1048576 }
  execution := {
    strategy := "sequentialDualProcessViaProjectRelay"
    processGroupContract := "lean4.31-posix-setsid-sigkill"
    platforms := ["macos", "linux"]
    workingDirectory := "inherited"
    environment := "inherited"
    jobs := 1
    processesPerCase := 2 }
  generator := {
    strategy := "exhaustiveFiniteMatrices"
    group := "GeneratedForm"
    fieldOrder := ["N", "B", "C"]
    cellStateOrder := ["sparseEmpty", "parsedBooleanTrue", "rejectedMalformed"]
    leafOrder := ["numberEqualZero", "booleanEqualTrue", "confirmNotEqualTrue", "booleanNotFilled"]
    verdictAtomOrder := ["notFired", "value", "omission", "unknown"]
    rowGateAtomOrder := ["ineligible", "eligible"]
    connectiveOrder := ["and", "or"] }
  }

private def testOutput (stdout : String) (stderr : String := "")
    (exitCode : UInt32 := 0) : Bounded.Output := {
  exitCode
  elapsedMs := 1
  stdout := stdout.toUTF8
  stderr := stderr.toUTF8 }

private def expectOutputFailure (label : String) (output : Bounded.Output) : Except String Unit :=
  match validateOutput testProfile "candidate" "self-test" output with
  | .error _ => pure ()
  | .ok _ => throw s!"output contract accepted {label}"

private def checkOutputContract : Except String Unit := do
  let response := Json.mkObj [
    ("protocolVersion", toJson Support.protocolVersion),
    ("kernelBehaviorVersion", toJson Support.kernelBehaviorVersion),
    ("outcome", toJson "ok"),
    ("verdict", Json.mkObj [("tag", toJson "notFired")])]
  match validateOutput testProfile "candidate" "self-test" (testOutput (response.compress ++ "\n")) with
  | .ok success =>
      if success.projection != .notFired then throw "output contract changed the projected verdict"
  | .error _ => throw "output contract rejected one canonical response line"
  expectOutputFailure "stdout without a newline" (testOutput response.compress)
  expectOutputFailure "two stdout lines" (testOutput (response.compress ++ "\n\n"))
  expectOutputFailure "stderr output" (testOutput (response.compress ++ "\n") "diagnostic\n")
  expectOutputFailure "a nonzero status" (testOutput (response.compress ++ "\n") "" 1)
  expectOutputFailure "duplicate response members"
    (testOutput ("{\"protocolVersion\":1,\"protocolVersion\":1,\"kernelBehaviorVersion\":\"" ++
      Support.kernelBehaviorVersion ++ "\",\"outcome\":\"ok\",\"verdict\":{\"tag\":\"notFired\"}}\n"))

private def checkCleanupSerialization : Except String Unit := do
  let empty : Bounded.Capture := { bytes := ByteArray.empty, exceeded := false }
  let failure : Bounded.Failure := {
    kind := .cleanupFailed
    cleanup := { kill := .alreadyGone, tasksCompleted := true, waitError? := some "wait failed" }
    elapsedMs := 1
    relayExitCode? := none
    stdout := empty
    stderr := empty }
  let json := boundedFailureJson "candidate" "self-test" failure
  let details ← match json.getObjVal? "details" with
    | .ok value => pure value
    | .error _ => throw "bounded failure serialization omitted details"
  let cleanup ← match details.getObjVal? "cleanup" with
    | .ok value => pure value
    | .error _ => throw "bounded failure serialization omitted cleanup"
  match cleanup.getObjVal? "waitError" with
  | .ok (.str "wait failed") => pure ()
  | _ => throw "bounded failure serialization omitted the cleanup wait error"

private def checkWitnessSelection : Except String Unit := do
  let first : Disagreement := {
    case := testCase "z-large" 3 4
    reference := testSide .notFired
    candidate := testSide .unknown }
  let second : Disagreement := {
    case := testCase "b-small" 1 8
    reference := testSide .notFired
    candidate := testSide .unknown }
  let third : Disagreement := {
    case := testCase "a-other" 1 1
    reference := testSide .firedValue
    candidate := testSide .unknown }
  let selected := minimalWitnesses [first, second, third]
  if selected.map (fun witness => witness.case.id) != ["a-other", "b-small"] then
    throw "minimal witnesses are not selected and ordered by nodes, bytes, and id"

private def checkResultFailureClassification : Except String Unit := do
  let loaded : LoadedProfile := { profile := testProfile, cases := [], bytes := ByteArray.empty }
  let config : RunConfig := {
    profilePath := "/profile.json"
    referenceRepo := "/reference"
    referenceExecutable := "reference"
    candidateRepo := "/candidate"
    candidateExecutable := "candidate"
    resultPath := "/result.json" }
  let digests : ArtifactDigests := {
    profile := "profile"
    runner := "runner"
    relay := "relay"
    reference := "reference"
    candidate := "candidate" }
  let processFailureValue := Json.mkObj [("kind", toJson "process")]
  let integrityFailureValue := Json.mkObj [("kind", toJson "integrity")]
  let processResult := resultJson loaded config digests { failure? := some processFailureValue }
  let integrityResult := resultJson loaded config digests {
    failure? := some processFailureValue
    integrityFailure? := some integrityFailureValue }
  match processResult.getObjVal? "outcome", integrityResult.getObjVal? "outcome",
      integrityResult.getObjVal? "failure", integrityResult.getObjVal? "integrityFailure" with
  | .ok (.str "processFailure"), .ok (.str "integrityFailure"),
      .ok processFailure, .ok integrityFailure =>
      if processFailure != processFailureValue || integrityFailure != integrityFailureValue then
        throw "result failure fields changed their distinct records"
  | _, _, _, _ => throw "result outcome does not distinguish process and integrity failures"

private def checkCanonicalResultBudget : Except String Unit := do
  let cases ← generate testProfile
  let side := testSide .notFired
  let disagreements := cases.map fun generated => {
    case := generated
    reference := side
    candidate := side }
  let worstText := String.ofList (List.replicate testProfile.bounds.processStdoutBytes '\u0000')
  let worstOutput := testOutput worstText worstText
  let failure := contractFailureJson "candidate" "last-case" "responseProjection"
    "contract failure" worstOutput (some (Json.str worstText))
  let state : CampaignState := {
    completedCases := cases.length
    disagreements
    failure? := some failure }
  let result := resultJson {
    profile := testProfile
    cases
    bytes := ByteArray.empty } {
    profilePath := "/profile.json"
    referenceRepo := "/reference"
    referenceExecutable := "reference"
    candidateRepo := "/candidate"
    candidateExecutable := "candidate"
    resultPath := "/result.json" } {
    profile := "profile"
    runner := "runner"
    relay := "relay"
    reference := "reference"
    candidate := "candidate" } state
  let resultBytes := (result.compress ++ "\n").utf8ByteSize
  if resultBytes > testProfile.bounds.resultBytes then
    throw s!"canonical all-disagreement plus late-failure result requires {resultBytes} bytes"

private def replaceResultObjectMember (root : Json) (objectName memberName : String)
    (value : Json) : Except String Json := do
  let object ← resultRequiredJson root "$" objectName
  pure (root.setObjVal! objectName (object.setObjVal! memberName value))

private def replaceArtifactDigest (root : Json) (name digest : String) : Except String Json := do
  let artifacts ← resultRequiredJson root "$" "artifacts"
  let artifact ← resultRequiredJson artifacts "$.artifacts" name
  pure (root.setObjVal! "artifacts"
    (artifacts.setObjVal! name (artifact.setObjVal! "sha256" (toJson digest))))

private def expectResultValidationFailure (label : String) (result : Except String Unit) :
    Except String Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw s!"result validator accepted {label}"

private def canonicalGreenResult : Except String (LoadedProfile × String × Json) := do
  let cases ← generate testProfile
  let distribution ← expectedReferenceDistribution testProfile cases
  let profileDigest := String.ofList (List.replicate 64 'a')
  let executableDigest := String.ofList (List.replicate 64 'b')
  let loaded : LoadedProfile := { profile := testProfile, cases, bytes := ByteArray.empty }
  let config : RunConfig := {
    profilePath := "/profile.json"
    referenceRepo := "/reference"
    referenceExecutable := ".lake/build/bin/a12-kernel-reference"
    candidateRepo := "/candidate"
    candidateExecutable := "target/debug/a12-kernel-rust-spike"
    resultPath := "/result.json" }
  let state : CampaignState := {
    processesStarted := cases.length * testProfile.execution.processesPerCase
    processInputBytes := generatedProcessInputBytes loaded
    processOutputBytes := 0
    elapsedMs := 1
    completedCases := cases.length
    referenceDistribution := distribution
    candidateDistribution := distribution }
  let result := resultJson loaded config {
    profile := profileDigest
    runner := executableDigest
    relay := executableDigest
    reference := executableDigest
    candidate := executableDigest } state
  pure (loaded, profileDigest, result)

private def checkResultValidation : IO Unit := do
  let (loaded, profileDigest, canonical) ← canonicalGreenResult |> IO.ofExcept
  validateResultJson loaded profileDigest canonical |> IO.ofExcept
  let mutations : List (String × Except String Json) := [
    ("an outcome mutation", pure (canonical.setObjVal! "outcome" (toJson "disagreement"))),
    ("a revision mutation", replaceResultObjectMember canonical "revisions" "candidate"
      (toJson (String.ofList (List.replicate 40 '0')))),
    ("an excluded platform mutation", replaceResultObjectMember canonical "execution"
      "platformTarget" (toJson "x86_64-pc-windows-msvc")),
    ("a platform-name-only mutation", replaceResultObjectMember canonical "execution"
      "platformTarget" (toJson "linux")),
    ("a trailing-platform-token mutation", replaceResultObjectMember canonical "execution"
      "platformTarget" (toJson "x86_64-pc-windows-linux")),
    ("a contradictory platform mutation", replaceResultObjectMember canonical "execution"
      "platformTarget" (toJson "x86_64-apple-darwin-linux")),
    ("a count mutation", replaceResultObjectMember canonical "counts" "completedCases" (toJson 51)),
    ("a claim mutation", replaceResultObjectMember canonical "claim" "kernelEvidence" (toJson "retained")),
    ("a failure mutation", pure (canonical.setObjVal! "failure" (Json.mkObj [("kind", toJson "processFailure")]))),
    ("a disagreement mutation", pure (canonical.setObjVal! "disagreements" (toJson [Json.mkObj []]))),
    ("a witness mutation", pure (canonical.setObjVal! "minimalWitnesses" (toJson [Json.mkObj []]))),
    ("a profile digest mutation", replaceArtifactDigest canonical "profile"
      (String.ofList (List.replicate 64 'c'))),
    ("an artifact digest mutation", replaceArtifactDigest canonical "runner" "not-a-digest"),
    ("an unknown top-level member", pure (canonical.setObjVal! "unexpected" (toJson true)))]
  for (label, mutation) in mutations do
    let mutated ← mutation |> IO.ofExcept
    expectResultValidationFailure label (validateResultJson loaded profileDigest mutated) |> IO.ofExcept
  let canonicalText := canonical.compress
  let duplicateText := "{\"schemaVersion\":1," ++ (canonicalText.drop 1).toString
  expectResultValidationFailure "a duplicate JSON member"
    (parseAndValidateResult loaded profileDigest duplicateText.toUTF8) |> IO.ofExcept
  expectResultValidationFailure "truncated JSON"
    (parseAndValidateResult loaded profileDigest (canonicalText.dropEnd 1).toString.toUTF8) |> IO.ofExcept
  IO.FS.withTempDir fun directory => do
    let path := directory / "oversized-result.json"
    IO.FS.writeBinFile path (ByteArray.mk <| Array.replicate (testProfile.bounds.resultBytes + 1) 0)
    let accepted ← try
      readBoundedPath "result" path testProfile.bounds.resultBytes *> pure true
    catch _ => pure false
    if accepted then fail "result validator accepted an oversized result read"

private def expectIoFailure (label : String) (action : IO Unit) : IO Unit := do
  let accepted ← try action *> pure true catch _ => pure false
  if accepted then fail s!"runner guard accepted {label}"

private def checkBoundedProfileRead : IO Unit :=
  IO.FS.withTempDir fun directory => do
    let path := directory / "oversized-profile.json"
    IO.FS.writeBinFile path (ByteArray.mk <| Array.replicate (maxProfileBytes + 1) 0)
    expectIoFailure "an oversized postflight profile read"
      (readBoundedPath "profile" path maxProfileBytes *> pure ())

private def checkRepositoryAndResultPaths : IO Unit := do
  let root := System.FilePath.mk "/repo"
  if !componentsContained root (System.FilePath.mk "/repo/.lake/build/bin/runner") ||
      componentsContained root (System.FilePath.mk "/repository/runner") then
    fail "component containment does not respect path boundaries"
  if componentsOverlap root (System.FilePath.mk "/candidate") ||
      !componentsOverlap root (System.FilePath.mk "/repo/nested") then
    fail "repository overlap guard changed"
  IO.FS.withTempDir fun directory => do
    let referenceRepo := directory / "reference"
    let candidateRepo := directory / "candidate"
    let resultDirectory := directory / "results"
    IO.FS.createDir referenceRepo
    IO.FS.createDir candidateRepo
    IO.FS.createDir resultDirectory
    let resultPath := resultDirectory / "result.json"
    requireResultDestination resultPath referenceRepo candidateRepo
    expectIoFailure "a result inside the reference repository"
      (requireResultDestination (referenceRepo / "result.json") referenceRepo candidateRepo)
    expectIoFailure "a relative result path"
      (requireResultDestination "result.json" referenceRepo candidateRepo)
    writeResult resultPath 1024 (Json.mkObj [("selfTest", toJson true)])
    expectIoFailure "an existing result path"
      (requireResultDestination resultPath referenceRepo candidateRepo)
    expectIoFailure "a result overwrite"
      (writeResult resultPath 1024 (Json.mkObj [("selfTest", toJson false)]))

def selfTest : IO Unit := do
  A12Kernel.Differential.Generated.selfTest
  checkResultValidation
  checkWitnessSelection |> IO.ofExcept
  checkOutputContract |> IO.ofExcept
  checkCleanupSerialization |> IO.ofExcept
  checkResultFailureClassification |> IO.ofExcept
  checkCanonicalResultBudget |> IO.ofExcept
  checkBoundedProfileRead
  validateRelativeExecutable ".lake/build/bin/a12-kernel-reference" |> IO.ofExcept
  for invalid in ["", "../candidate", "/absolute/candidate", "target//candidate", "target/candidate name"] do
    if (validateRelativeExecutable invalid).isOk then
      fail s!"relative executable guard accepted '{invalid}'"
  checkRepositoryAndResultPaths
  IO.println "generated differential runner self-test: profile, strict retained-result validation, output contract, cleanup record, witness ordering, repository containment, and result publication passed"

private def usage : String :=
  "usage: checkGeneratedDifferential --self-test | --check-profile PROFILE | --check-result PROFILE RESULT | --run --profile PROFILE --reference-repo REPO --reference EXE --candidate-repo REPO --candidate EXE --result RESULT"

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | ["--self-test"] =>
      try selfTest *> pure 0
      catch error => IO.eprintln s!"generated differential self-test failed: {error}" *> pure 1
  | ["--check-profile", profile] =>
      try checkProfile profile *> pure 0
      catch error => IO.eprintln s!"generated differential profile check failed: {error}" *> pure 1
  | ["--check-result", profile, result] =>
      try checkResult profile result *> pure 0
      catch error => IO.eprintln s!"generated differential result check failed: {error}" *> pure 1
  | ["--run", "--profile", profile, "--reference-repo", referenceRepo,
      "--reference", reference, "--candidate-repo", candidateRepo,
      "--candidate", candidate, "--result", result] =>
      try
        run {
          profilePath := profile
          referenceRepo
          referenceExecutable := reference
          candidateRepo
          candidateExecutable := candidate
          resultPath := result }
      catch error =>
        IO.eprintln s!"generated differential failed before a result could be written: {error}"
        pure 1
  | _ => IO.eprintln usage *> pure 2

end A12Kernel.Differential.Runner
