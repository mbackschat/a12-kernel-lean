import A12Kernel.Qualification.RustPacket

/-! # Strict mutation qualification verification

The checker treats packet, result, and candidate paths as three explicit roots. It validates the closed packet index, exact payload tree, frozen Git bytes and modes, patch transformations, closed result record, command policy, raw-log bytes, observer output, and the declared path-and-byte restoration projection.
-/

namespace A12Kernel.Qualification.Checker

open Lean
open A12Kernel.Evidence.FlatProtocolBridge
open A12Kernel.Qualification.Artifact
open A12Kernel.Qualification.Packet

private def maxJsonBytes : Nat := 4 * 1024 * 1024
private def maxArtifactBytes : Nat := 16 * 1024 * 1024
private def maxTreeFiles : Nat := 512
private def maxTreeDepth : Nat := 16

private def fail (message : String) : IO α :=
  throw (IO.userError message)

private def requireRegularFile (path : System.FilePath) : IO Unit := do
  let metadata ← path.symlinkMetadata
  if metadata.type != .file then
    fail s!"qualification artifact '{path}' is not a regular non-symlink file"

private def requireBoundedRegularFile (path : System.FilePath) (label : String)
    (limit : Nat := maxArtifactBytes) : IO Unit := do
  requireRegularFile path
  let metadata ← path.symlinkMetadata
  if metadata.byteSize > UInt64.ofNat limit then
    fail s!"{label} exceeds the {limit}-byte qualification limit"

private def readBoundedText (path : System.FilePath) (label : String) : IO String := do
  requireRegularFile path
  let metadata ← path.symlinkMetadata
  if metadata.byteSize > UInt64.ofNat maxJsonBytes then
    fail s!"{label} exceeds the {maxJsonBytes}-byte qualification limit"
  IO.FS.readFile path

private partial def collectFilesFrom (current : System.FilePath)
    (relativePrefix : String := "") (depth : Nat := 0)
    (ignoredRootDirectory? : Option String := none) : IO (List PortablePath) := do
  if depth > maxTreeDepth then
    fail s!"qualification artifact tree exceeds depth {maxTreeDepth} at '{relativePrefix}'"
  let entries := (← current.readDir).toList.mergeSort fun left right =>
    left.fileName ≤ right.fileName
  let mut files : List PortablePath := []
  for entry in entries do
    let relative := if relativePrefix.isEmpty then entry.fileName
      else s!"{relativePrefix}/{entry.fileName}"
    let portable ← match PortablePath.parse relative with
      | .ok path => pure path
      | .error error => fail s!"unsafe qualification artifact path '{relative}': {error}"
    let metadata ← entry.path.symlinkMetadata
    match metadata.type with
    | .file => files := files ++ [portable]
    | .dir =>
        if depth == 0 && ignoredRootDirectory? == some entry.fileName then
          pure ()
        else
          let nested ← collectFilesFrom entry.path relative (depth + 1) ignoredRootDirectory?
          if nested.isEmpty then
            fail s!"qualification artifact tree contains empty directory '{relative}'"
          files := files ++ nested
    | .symlink => fail s!"qualification artifact tree contains symlink '{relative}'"
    | .other => fail s!"qualification artifact tree contains non-regular path '{relative}'"
  pure files

private def collectFiles (root : System.FilePath) : IO (List PortablePath) := do
  let metadata ← root.symlinkMetadata
  if metadata.type != .dir then fail s!"qualification root '{root}' is not a directory"
  let files ← collectFilesFrom root
  if files.length > maxTreeFiles then
    fail s!"qualification artifact tree contains more than {maxTreeFiles} files"
  pure files

private def collectCandidateFiles (root : System.FilePath) : IO (List PortablePath) := do
  let metadata ← root.symlinkMetadata
  if metadata.type != .dir then fail s!"candidate root '{root}' is not a directory"
  let files ← collectFilesFrom root "" 0 (some "target")
  if files.length > maxTreeFiles then
    fail s!"candidate source tree contains more than {maxTreeFiles} non-build-output files"
  pure files

private def verifyFileDigest (root : System.FilePath) (file : FileDigest) : IO Unit := do
  let path := root / file.path.toString
  requireBoundedRegularFile path s!"qualification payload '{file.path}'"
  let actual ← A12Kernel.Process.Sha256.file path
  if actual != file.sha256.toString then
    fail s!"qualification artifact digest mismatch for '{file.path}': expected {file.sha256}, found {actual}"

private def expectedObservationJson (mutation : MutationDescriptor) : Json :=
  ({
    exercise := mutation.mechanism.exercise
    caseResults := A12Kernel.Qualification.MutationResult.expectedMutationCaseResults mutation
    algebraResults := A12Kernel.Qualification.MutationResult.expectedMutationAlgebraResults mutation
  } : A12Kernel.Qualification.MutationResult.Observation).asJson

private def readStrictJsonFile (path : System.FilePath) (label : String) : IO Json := do
  let input ← readBoundedText path label
  match A12Kernel.Reference.StrictJson.parse input with
  | .ok json => pure json
  | .error error => fail s!"invalid strict {label} JSON '{path}': {repr error}"

private def validateExpectedObservations (packetRoot : System.FilePath)
    (index : Index) : IO Unit := do
  let baseline ← readStrictJsonFile
    (packetRoot / index.expectedBaselineObservation.path.toString)
    "natural baseline expected observation"
  if baseline != A12Kernel.Qualification.RustPacket.expectedBaselineObservationJson then
    fail "natural baseline expected-observation payload differs from the typed semantics"
  for (artifact, mutation) in index.mutations.zip mutationPlan.mutations do
    let actual ← readStrictJsonFile (packetRoot / artifact.expectedObservation.path.toString)
      s!"mutation {mutation.mechanism.exercise} expected observation"
    let expected := expectedObservationJson mutation
    if actual != expected then
      fail s!"mutation {mutation.mechanism.exercise} expected-observation payload differs from the typed plan"

private def validateCommandPolicy (index : Index) : IO Unit := do
  if index.naturalGateCommands != A12Kernel.Qualification.RustPacket.expectedNaturalCommands then
    fail "qualification packet natural-gate command policy differs from the source-owned policy"
  if index.finalRestorationGateCommands !=
      A12Kernel.Qualification.RustPacket.expectedFinalCommands then
    fail "qualification packet final-gate command policy differs from the source-owned policy"
  for (artifact, mutation) in index.mutations.zip mutationPlan.mutations do
    if artifact.commands != A12Kernel.Qualification.RustPacket.expectedMutationCommands mutation then
      fail s!"qualification packet command policy differs for mutation {mutation.mechanism.exercise}"

private def validateAuxiliaryContents (packetRoot : System.FilePath) (index : Index) : IO Unit := do
  let expected ← A12Kernel.Qualification.RustPacket.expectedAuxiliaryContents index |> IO.ofExcept
  if expected.map (·.path) != index.auxiliaryFiles.map (·.path) then
    fail "qualification packet auxiliary role inventory differs from the source-owned layout"
  for file in expected do
    let path := packetRoot / file.path.toString
    requireBoundedRegularFile path s!"qualification auxiliary '{file.path}'"
    if (← IO.FS.readFile path) != file.content then
      fail s!"qualification auxiliary '{file.path}' differs from its source-owned content"

private def expectedPacketPaths (index : Index) : List String :=
  ("PACKET.json" :: index.payloadFiles.map (·.path.toString)).mergeSort

private def verifyExactTree (root : System.FilePath) (expected : List String)
    (label : String) : IO Unit := do
  let actual := (← collectFiles root).map (·.toString)
  let expected := expected.mergeSort
  if actual != expected then
    let missing := expected.filter fun path => !actual.contains path
    let extra := actual.filter fun path => !expected.contains path
    fail s!"{label} file tree is not exact; missing={repr missing}, extra={repr extra}"

private def packetPlanMatchesSource (projectRoot packetRoot : System.FilePath)
    (index : Index) : IO Unit := do
  let sourcePath := projectRoot / "reference/flat-validation-empty-logic-v1.mutation-plan.json"
  let source ← readBoundedText sourcePath "source mutation plan"
  let packet ← readBoundedText (packetRoot / index.mutationPlan.path.toString)
    "packet mutation plan"
  if packet != source then
    fail "qualification packet mutation-plan bytes differ from the source-owned generated plan"
  let generated ← match mutationPlan.asJson capability with
    | .ok json => pure json
    | .error error => fail s!"typed mutation plan is invalid: {error}"
  let packetJson ← readStrictJsonFile (packetRoot / index.mutationPlan.path.toString)
    "packet mutation plan"
  if packetJson != generated then
    fail "qualification packet mutation plan differs structurally from the typed plan"

private def observerMatchesSource (projectRoot packetRoot : System.FilePath)
    (index : Index) : IO Unit := do
  let source ← IO.FS.readFile
    (projectRoot / "A12Kernel/Qualification/Assets/flat_validation_observer.rs")
  let packet ← IO.FS.readFile (packetRoot / index.observer.path.toString)
  if packet != source then
    fail "qualification packet observer bytes differ from the source-owned observer"

/-- Require the packet's observer and semantic patch bytes to equal the projection reconstructed from tracked mutation edits, the frozen natural library, and the tracked observer. -/
def validateSourceOwnedPatches (projectRoot packetRoot : System.FilePath)
    (index : Index) : IO Unit := do
  let baselineLibrary ← match index.baselineSourceFiles.filter
      (·.candidatePath.toString == "src/lib.rs") with
    | [source] => IO.FS.readFile (packetRoot / source.packetPath.toString)
    | [] => fail "qualification packet baseline has no src/lib.rs"
    | _ => fail "qualification packet baseline has duplicate src/lib.rs entries"
  let observer ← IO.FS.readFile
    (projectRoot / "A12Kernel/Qualification/Assets/flat_validation_observer.rs")
  let expectedObserverPatch ←
    A12Kernel.Qualification.RustPacket.sourceOwnedObserverPatch observer |> IO.ofExcept
  let actualObserverPatch ← IO.FS.readFile
    (packetRoot / index.baselineObserverPatch.path.toString)
  if actualObserverPatch != expectedObserverPatch then
    fail "qualification packet observer-only patch differs from the source-owned projection"
  let expectedMutations ←
    A12Kernel.Qualification.RustPacket.sourceOwnedMutationProjections
      baselineLibrary observer |> IO.ofExcept
  if expectedMutations.length != index.mutations.length then
    fail "qualification packet mutation count differs from the source-owned patch projection"
  for (expected, artifact) in expectedMutations.zip index.mutations do
    let actual ← IO.FS.readFile (packetRoot / artifact.patch.path.toString)
    if actual != expected.patch then
      fail s!"qualification packet mutation {artifact.exercise} patch differs from the source-owned projection"

def copyBaseline (packetRoot destination : System.FilePath) (index : Index) : IO Unit := do
  IO.FS.createDirAll destination
  for source in index.baselineSourceFiles do
    let target := destination / source.candidatePath.toString
    if let some parent := target.parent then IO.FS.createDirAll parent
    let bytes ← IO.FS.readBinFile (packetRoot / source.packetPath.toString)
    IO.FS.writeBinFile target bytes
    if source.executable then
      IO.setAccessRights target {
        user := { read := true, write := true, execution := true }
        group := { read := true, execution := true }
        other := { read := true, execution := true } }

def candidateInventory (root : System.FilePath) : IO (List FileDigest) := do
  let paths ← collectCandidateFiles root
  paths.mapM fun path => do
    let sha256 ← Digest.parse (← A12Kernel.Process.Sha256.file (root / path.toString))
      |> IO.ofExcept
    pure { path, sha256 }

private def runGitApply (candidate patch : System.FilePath) (args : Array String)
    (label : String) : IO Unit := do
  let output ← IO.Process.output {
    cmd := "git"
    args := args ++ #[patch.toString]
    cwd := some candidate }
  if output.exitCode != 0 then
    fail s!"{label} failed with exit {output.exitCode}: {output.stderr.trimAscii.toString}"

private def validatePatches (packetRoot : System.FilePath) (index : Index) : IO Unit :=
  IO.FS.withTempDir fun temporary => do
    let packetRoot ← IO.FS.realPath packetRoot
    let candidate := temporary / "candidate"
    copyBaseline packetRoot candidate index
    let baseline := index.baselineResultFiles
    if (← candidateInventory candidate) != baseline then
      fail "qualification packet copied baseline does not match its source inventory"
    let baselineObserverPatch := packetRoot / index.baselineObserverPatch.path.toString
    runGitApply candidate baselineObserverPatch #["apply", "--check"]
      "baseline observer patch precheck"
    runGitApply candidate baselineObserverPatch #["apply", "--whitespace=nowarn"]
      "baseline observer patch application"
    if (← candidateInventory candidate) != index.instrumentedBaselineSourceFiles then
      fail "baseline observer patch does not produce the indexed instrumented inventory"
    runGitApply candidate baselineObserverPatch #["apply", "--reverse", "--check"]
      "baseline observer reverse-patch precheck"
    runGitApply candidate baselineObserverPatch
      #["apply", "--reverse", "--whitespace=nowarn"]
      "baseline observer reverse-patch application"
    if (← candidateInventory candidate) != baseline then
      fail "baseline observer reverse patch does not restore the baseline"
    for artifact in index.mutations do
      let patch := packetRoot / artifact.patch.path.toString
      runGitApply candidate patch #["apply", "--check"]
        s!"mutation {artifact.exercise} patch precheck"
      runGitApply candidate patch #["apply", "--whitespace=nowarn"]
        s!"mutation {artifact.exercise} patch application"
      if (← candidateInventory candidate) != artifact.mutatedSourceFiles then
        fail s!"mutation {artifact.exercise} patch does not produce the indexed mutant inventory"
      runGitApply candidate patch #["apply", "--reverse", "--check"]
        s!"mutation {artifact.exercise} reverse-patch precheck"
      runGitApply candidate patch #["apply", "--reverse", "--whitespace=nowarn"]
        s!"mutation {artifact.exercise} reverse-patch application"
      if (← candidateInventory candidate) != baseline then
        fail s!"mutation {artifact.exercise} reverse patch does not restore the baseline"

def readAndVerifyPacket (projectRoot candidateRoot packetIndexPath : System.FilePath)
    (allowDirtySource : Bool := false) : IO Index := do
  requireRegularFile packetIndexPath
  if packetIndexPath.fileName != some "PACKET.json" then
    fail "qualification packet index must be named PACKET.json"
  let packetRoot ← match packetIndexPath.parent with
    | some parent => pure parent
    | none => fail "qualification packet index has no parent directory"
  let input ← readBoundedText packetIndexPath "qualification packet"
  let index ← match Packet.parseText input with
    | .ok index => pure index
    | .error error => fail error
  A12Kernel.Qualification.RustPacket.verifySourceCheckout projectRoot index allowDirtySource
  verifyExactTree packetRoot (expectedPacketPaths index) "qualification packet"
  for file in index.payloadFiles do verifyFileDigest packetRoot file
  validateAuxiliaryContents packetRoot index
  packetPlanMatchesSource projectRoot packetRoot index
  observerMatchesSource projectRoot packetRoot index
  validateExpectedObservations packetRoot index
  validateCommandPolicy index
  A12Kernel.Qualification.RustPacket.verifyFrozenBaseline candidateRoot packetRoot index
  validateSourceOwnedPatches projectRoot packetRoot index
  validatePatches packetRoot index
  pure index

private def expectedResultPacket (packetIndexPath : System.FilePath) (index : Index)
    (assuranceClass : A12Kernel.Qualification.MutationResult.AssuranceClass) :
    IO A12Kernel.Qualification.MutationResult.ExpectedPacket := do
  let packetIndexSha256 ← match Digest.parse
      (← A12Kernel.Process.Sha256.file packetIndexPath) with
    | .ok digest => pure digest
    | .error error => fail s!"invalid packet-index digest: {error}"
  pure {
    packetId := index.id
    packetIndexSha256
    sourceRevision := index.sourceRevision
    candidateBaseRevision := index.candidateBaseRevision
    assuranceClass
    isolationBoundary := index.executionProfile.isolationBoundary
    mutationPlanSha256 := index.mutationPlan.sha256
    baselineImplementationRevision := index.baselineRevision
    baselineSourceFiles := index.baselineResultFiles
    toolchain := index.toolchain.map fun toolchain => {
      name := toolchain.name, version := toolchain.version }
    patches := index.mutations.map (·.patch) }

private def commandMatches (actual : A12Kernel.Qualification.MutationResult.CommandRecord)
    (expected : CommandSpec) : Bool :=
  actual.id == expected.id && actual.argv == expected.argv &&
    actual.exitStatus == expected.expectedExitStatus

private def validateCommands
    (actual : List A12Kernel.Qualification.MutationResult.CommandRecord)
    (expected : List CommandSpec) (context : String) : IO Unit := do
  if actual.length != expected.length ||
      !(actual.zip expected).all fun (actual, expected) => commandMatches actual expected then
    fail s!"{context}: recorded commands differ from the packet command policy"

private def allCommands (result : A12Kernel.Qualification.MutationResult.Result) :
    List A12Kernel.Qualification.MutationResult.CommandRecord :=
  result.naturalGate.commands ++ result.mutations.flatMap (·.commands) ++
    result.finalRestorationGate.commands

private def validateGlobalLogPaths
    (commands : List A12Kernel.Qualification.MutationResult.CommandRecord) : IO Unit := do
  let paths := commands.flatMap fun command => [command.stdoutLog, command.stderrLog]
  let pathTexts := paths.map (·.toString)
  if pathTexts.length != pathTexts.eraseDups.length then
    fail "qualification result reuses a command-log path across phases"
  let resultPath ← PortablePath.parse "RESULT.json" |> IO.ofExcept
  match validatePathSet (resultPath :: paths) with
  | .ok _ => pure ()
  | .error error => fail s!"qualification result has conflicting global paths: {error}"

private def resultLogFiles (result : A12Kernel.Qualification.MutationResult.Result) :
    List FileDigest :=
  result.naturalGate.rawLogs ++ result.mutations.flatMap (·.rawLogs) ++
    result.finalRestorationGate.rawLogs

private def verifyResultLog (resultRoot : System.FilePath)
    (file : FileDigest) : IO Unit := do
  let path := resultRoot / file.path.toString
  requireBoundedRegularFile path s!"qualification result log '{file.path}'"
  let actual ← A12Kernel.Process.Sha256.file path
  if actual != file.sha256.toString then
    fail s!"qualification result log digest mismatch for '{file.path}'"

private def commandById (commands : List A12Kernel.Qualification.MutationResult.CommandRecord)
    (id context : String) : IO A12Kernel.Qualification.MutationResult.CommandRecord :=
  match commands.filter (·.id == id) with
  | [command] => pure command
  | [] => fail s!"{context}: missing command '{id}'"
  | _ => fail s!"{context}: duplicate command '{id}'"

private def validateToolchainLogs (resultRoot : System.FilePath) (index : Index)
    (result : A12Kernel.Qualification.MutationResult.Result) : IO Unit := do
  for toolchain in index.toolchain do
    let command ← commandById result.naturalGate.commands s!"{toolchain.name}-version"
      "natural gate"
    let stdout ← IO.FS.readFile (resultRoot / command.stdoutLog.toString)
    let stderr ← IO.FS.readFile (resultRoot / command.stderrLog.toString)
    if stdout.trimAscii.toString != toolchain.version then
      fail s!"qualification result {toolchain.name} log differs from the packet identity"
    if !stderr.isEmpty then
      fail s!"qualification result {toolchain.name} command wrote stderr"

private def validateObserverLogs (packetRoot resultRoot : System.FilePath) (index : Index)
    (result : A12Kernel.Qualification.MutationResult.Result) : IO Unit := do
  let baselineCommand ← commandById result.naturalGate.commands "observe-baseline" "natural gate"
  let baselineActual ← readStrictJsonFile
    (resultRoot / baselineCommand.stdoutLog.toString) "natural baseline observer output"
  let baselineObservation ←
    A12Kernel.Qualification.MutationResult.parseObservationJson baselineActual |> IO.ofExcept
  if baselineObservation.exercise != 0 then
    fail s!"natural baseline observer reported exercise {baselineObservation.exercise}, expected 0"
  let baselineExpected ← readStrictJsonFile
    (packetRoot / index.expectedBaselineObservation.path.toString)
    "natural baseline expected observation"
  if baselineActual != baselineExpected then
    fail "natural baseline observer log differs from the packet expectation"
  let baselineStderr ← IO.FS.readFile (resultRoot / baselineCommand.stderrLog.toString)
  if !baselineStderr.isEmpty then fail "natural baseline observer wrote stderr"
  for (artifact, record) in index.mutations.zip result.mutations do
    let command ← commandById record.commands "observe" s!"mutation {artifact.exercise}"
    let actual ← readStrictJsonFile (resultRoot / command.stdoutLog.toString)
      s!"mutation {artifact.exercise} observer output"
    let observation ←
      A12Kernel.Qualification.MutationResult.parseObservationJson actual |> IO.ofExcept
    if observation.exercise != artifact.exercise then
      fail s!"mutation {artifact.exercise} observer reported exercise {observation.exercise}"
    if observation.caseResults != record.observedCaseResults then
      fail s!"mutation {artifact.exercise} recorded case results differ from captured observer output"
    if observation.algebraResults != record.observedAlgebraResults then
      fail s!"mutation {artifact.exercise} recorded algebra results differ from captured observer output"
    let expected ← readStrictJsonFile (packetRoot / artifact.expectedObservation.path.toString)
      s!"mutation {artifact.exercise} expected observation"
    if actual != expected then
      fail s!"mutation {artifact.exercise} observer log differs from the packet expectation"
    let stderr ← IO.FS.readFile (resultRoot / command.stderrLog.toString)
    if !stderr.isEmpty then
      fail s!"mutation {artifact.exercise} observer wrote stderr"

private def inventoryManifestPath (command : CommandSpec) : IO PortablePath := do
  let argument ← match command.argv.reverse with
    | value :: _ => pure value
    | [] => fail s!"inventory command '{command.id}' has no manifest argument"
  let packetPrefix := "../packet/"
  if !argument.startsWith packetPrefix then
    fail s!"inventory command '{command.id}' does not use a packet-relative manifest"
  let relative := argument.drop packetPrefix.length |>.toString
  match PortablePath.parse relative with
  | .ok path => pure path
  | .error error => fail s!"inventory command '{command.id}' has an unsafe manifest: {error}"

private def validateInventoryCommand (packetRoot resultRoot : System.FilePath)
    (actual : A12Kernel.Qualification.MutationResult.CommandRecord)
    (expected : CommandSpec) : IO Unit := do
  if !expected.id.endsWith "inventory" then pure () else
    let manifest ← inventoryManifestPath expected
    let expectedStdout ← IO.FS.readFile (packetRoot / manifest.toString)
    let actualStdout ← IO.FS.readFile (resultRoot / actual.stdoutLog.toString)
    if actualStdout != expectedStdout then
      fail s!"inventory command '{expected.id}' stdout differs from its packet manifest"
    let stderr ← IO.FS.readFile (resultRoot / actual.stderrLog.toString)
    if !stderr.isEmpty then fail s!"inventory command '{expected.id}' wrote stderr"

private def validateInventoryLogs (packetRoot resultRoot : System.FilePath) (index : Index)
    (result : A12Kernel.Qualification.MutationResult.Result) : IO Unit := do
  for (actual, expected) in result.naturalGate.commands.zip index.naturalGateCommands do
    validateInventoryCommand packetRoot resultRoot actual expected
  for (record, artifact) in result.mutations.zip index.mutations do
    for (actual, expected) in record.commands.zip artifact.commands do
      validateInventoryCommand packetRoot resultRoot actual expected
  for (actual, expected) in
      result.finalRestorationGate.commands.zip index.finalRestorationGateCommands do
    validateInventoryCommand packetRoot resultRoot actual expected

def checkResult (packetIndexPath resultPath : System.FilePath) (index : Index)
    (assuranceClass : A12Kernel.Qualification.MutationResult.AssuranceClass :=
      .isolatedSessionAttestation) : IO Unit := do
  requireRegularFile resultPath
  if resultPath.fileName != some "RESULT.json" then
    fail "qualification result must be named RESULT.json"
  let packetRoot ← match packetIndexPath.parent with
    | some parent => pure parent
    | none => fail "qualification packet index has no parent directory"
  let resultRoot ← match resultPath.parent with
    | some parent => pure parent
    | none => fail "qualification result has no parent directory"
  let input ← readBoundedText resultPath "qualification result"
  let result ← match A12Kernel.Qualification.MutationResult.parseResultText input with
    | .ok result => pure result
    | .error error => fail error
  let expected ← expectedResultPacket packetIndexPath index assuranceClass
  match result.validateMetadata expected with
  | .ok _ => pure ()
  | .error error => fail error
  validateCommands result.naturalGate.commands index.naturalGateCommands "natural gate"
  validateCommands result.finalRestorationGate.commands index.finalRestorationGateCommands
    "final restoration gate"
  for ((record, artifact), mutation) in
      (result.mutations.zip index.mutations).zip mutationPlan.mutations do
    validateCommands record.commands artifact.commands
      s!"mutation {mutation.mechanism.exercise}"
  let commands := allCommands result
  validateGlobalLogPaths commands
  let logs := resultLogFiles result
  if logs.length != logs.eraseDups.length then
    fail "qualification result reuses a raw-log record"
  let expectedTree := ("RESULT.json" :: logs.map (·.path.toString)).mergeSort
  verifyExactTree resultRoot expectedTree "qualification result"
  for log in logs do verifyResultLog resultRoot log
  validateToolchainLogs resultRoot index result
  validateObserverLogs packetRoot resultRoot index result
  validateInventoryLogs packetRoot resultRoot index result

end A12Kernel.Qualification.Checker
