import A12Kernel.Qualification.Runner

/-! # Mutation qualification checker self-test

This IO-only module assembles a real Rust qualification packet, executes its natural and mutant commands in a disposable candidate, and exercises the checker with independent adversarial mutations. It writes only beneath an automatically removed temporary directory.
-/

namespace A12Kernel.Qualification.SelfTest

open Lean
open A12Kernel.Evidence.FlatProtocolBridge
open A12Kernel.Qualification.Artifact
open A12Kernel.Qualification.Packet

private abbrev Result := A12Kernel.Qualification.MutationResult.Result
private abbrev MutationRecord := A12Kernel.Qualification.MutationResult.MutationRecord
private abbrev CommandRecord := A12Kernel.Qualification.MutationResult.CommandRecord

private def fail (message : String) : IO α :=
  throw (IO.userError message)

private def renderResult (result : Result) : String :=
  result.asJson.pretty 100 ++ "\n"

private def renderPacket (index : Index) : String :=
  index.asJson.pretty 100 ++ "\n"

private def requireFailure (label expectedMessage : String) (action : IO α) : IO Unit := do
  let failure? ← try
    let _ ← action
    pure none
  catch error =>
    pure (some (toString error))
  match failure? with
  | none => fail s!"self-test guard '{label}' accepted an invalid artifact"
  | some message =>
      if !message.contains expectedMessage then
        fail s!"self-test guard '{label}' failed at the wrong boundary; expected '{expectedMessage}', found '{message}'"

private def requireSuccess (label : String) (action : IO α) : IO α := do
  try action
  catch error => fail s!"self-test positive guard '{label}' failed: {error}"

private def withRestoredText (path : System.FilePath) (replacement : String)
    (action : IO Unit) : IO Unit := do
  let original ← IO.FS.readFile path
  IO.FS.writeFile path replacement
  try
    action
  finally
    IO.FS.writeFile path original

private def withRemovedFile (path : System.FilePath) (action : IO Unit) : IO Unit := do
  let original ← IO.FS.readBinFile path
  IO.FS.removeFile path
  try
    action
  finally
    IO.FS.writeBinFile path original

private def withExtraFile (path : System.FilePath) (action : IO Unit) : IO Unit := do
  if ← System.FilePath.pathExists path then
    fail s!"self-test extra-file path already exists: '{path}'"
  IO.FS.writeFile path "self-test extra artifact\n"
  try
    action
  finally
    if ← System.FilePath.pathExists path then IO.FS.removeFile path

private def withCorruptedFile (path : System.FilePath) (action : IO Unit) : IO Unit := do
  let original ← IO.FS.readFile path
  IO.FS.writeFile path (original ++ "\nself-test-corruption\n")
  try
    action
  finally
    IO.FS.writeFile path original

private def parsePath (value context : String) : IO PortablePath :=
  match PortablePath.parse value with
  | .ok path => pure path
  | .error error => fail s!"{context}: {error}"

private def parseDigest (value context : String) : IO Digest :=
  match Digest.parse value with
  | .ok digest => pure digest
  | .error error => fail s!"{context}: {error}"

private def hashFile (path : System.FilePath) : IO Digest := do
  parseDigest (← A12Kernel.Process.Sha256.file path) s!"invalid digest for '{path}'"

private def wrongDigest (digest : Digest) : IO Digest := do
  let zeros := String.ofList (List.replicate 64 '0')
  let replacement := if digest.toString == zeros then
    String.ofList (List.replicate 64 '1') else zeros
  parseDigest replacement "self-test replacement digest"

private def alternativeRevision (revision : String) : String :=
  let zeros := String.ofList (List.replicate 40 '0')
  if revision == zeros then String.ofList (List.replicate 40 '1') else zeros

private def removeMember (json : Json) (name : String) : IO Json := do
  let members ← match json.getObj? with
    | .ok object => pure object.toList
    | .error _ => fail "self-test expected a JSON object"
  let remaining := members.filter fun member => member.1 != name
  if remaining.length == members.length then
    fail s!"self-test JSON object has no member '{name}'"
  pure (Json.mkObj remaining)

private def duplicateTopLevelMember (canonical name value : String) : IO String :=
  if canonical.startsWith "{" then
    pure ("{\"" ++ name ++ "\":" ++ value ++ "," ++ canonical.drop 1)
  else
    fail "self-test renderer did not produce a JSON object"

private def updateFirstMutation (result : Result)
    (update : MutationRecord → MutationRecord) : IO Result :=
  match result.mutations with
  | [] => fail "self-test result contains no mutation"
  | mutation :: rest => pure { result with mutations := update mutation :: rest }

private def dropFirstCase (result : Result) : IO Result :=
  updateFirstMutation result fun mutation => {
    mutation with observedCaseResults := mutation.observedCaseResults.drop 1 }

private def reorderFirstCases (result : Result) : IO Result :=
  updateFirstMutation result fun mutation =>
    match mutation.observedCaseResults with
    | first :: second :: rest => {
        mutation with observedCaseResults := second :: first :: rest }
    | _ => mutation

private def alterFirstCommand (result : Result) : IO Result :=
  match result.naturalGate.commands with
  | [] => fail "self-test natural gate contains no command"
  | command :: rest =>
      let altered := { command with argv := command.argv ++ ["--self-test-altered"] }
      pure { result with naturalGate := {
        result.naturalGate with commands := altered :: rest } }

private def alterFirstLogDigest (result : Result) : IO Result :=
  match result.naturalGate.rawLogs with
  | [] => fail "self-test natural gate contains no raw log"
  | log :: rest => do
      let altered := { log with sha256 := ← wrongDigest log.sha256 }
      pure { result with naturalGate := {
        result.naturalGate with rawLogs := altered :: rest } }

private def reuseCrossPhaseLog (result : Result) : IO Result := do
  let naturalCommand ← match result.naturalGate.commands with
    | command :: _ => pure command
    | [] => fail "self-test natural gate contains no command"
  let naturalLog ← match result.naturalGate.rawLogs with
    | log :: _ => pure log
    | [] => fail "self-test natural gate contains no raw log"
  let finalCommands ← match result.finalRestorationGate.commands with
    | command :: rest => pure ({ command with stdoutLog := naturalCommand.stdoutLog } :: rest)
    | [] => fail "self-test final gate contains no command"
  let finalLogs ← match result.finalRestorationGate.rawLogs with
    | _ :: rest => pure (naturalLog :: rest)
    | [] => fail "self-test final gate contains no raw log"
  pure { result with finalRestorationGate := {
    result.finalRestorationGate with commands := finalCommands, rawLogs := finalLogs } }

private def reuseCaseFoldedCrossPhaseLog (result : Result) : IO Result := do
  let naturalCommand ← match result.naturalGate.commands with
    | command :: _ => pure command
    | [] => fail "self-test natural gate contains no command"
  let naturalLog ← match result.naturalGate.rawLogs with
    | log :: _ => pure log
    | [] => fail "self-test natural gate contains no raw log"
  let foldedText := if naturalCommand.stdoutLog.toString.startsWith "logs/" then
    "Logs/" ++ naturalCommand.stdoutLog.toString.drop 5
  else
    "Logs/" ++ naturalCommand.stdoutLog.toString
  let foldedPath ← parsePath foldedText "self-test case-folded log path"
  let finalCommands ← match result.finalRestorationGate.commands with
    | command :: rest => pure ({ command with stdoutLog := foldedPath } :: rest)
    | [] => fail "self-test final gate contains no command"
  let finalLogs ← match result.finalRestorationGate.rawLogs with
    | _ :: rest => pure ({ naturalLog with path := foldedPath } :: rest)
    | [] => fail "self-test final gate contains no raw log"
  pure { result with finalRestorationGate := {
    result.finalRestorationGate with commands := finalCommands, rawLogs := finalLogs } }

private def alterMutationId (result : Result) : IO Result :=
  updateFirstMutation result fun mutation => {
    mutation with mutationId := mutation.mutationId ++ "-altered" }

private def reorderMutations (result : Result) : IO Result :=
  match result.mutations with
  | first :: second :: rest => pure { result with mutations := second :: first :: rest }
  | _ => fail "self-test result contains fewer than two mutations"

private def alterMutationPatch (result : Result) : IO Result := do
  let path ← parsePath "patches/self-test-altered.patch" "self-test altered patch"
  updateFirstMutation result fun mutation => { mutation with patch := path }

private def alterFirstAlgebraRecords : List MutationRecord → Option (List MutationRecord)
  | [] => none
  | mutation :: rest =>
      match mutation.observedAlgebraResults with
      | algebra :: algebraRest =>
          let verdict := if algebra.verdict == .unknown then .notFired else .unknown
          some ({ mutation with observedAlgebraResults :=
            { algebra with verdict } :: algebraRest } :: rest)
      | [] => (alterFirstAlgebraRecords rest).map (mutation :: ·)

private def alterAlgebraResult (result : Result) : IO Result :=
  match alterFirstAlgebraRecords result.mutations with
  | some mutations => pure { result with mutations }
  | none => fail "self-test result contains no algebra observation"

private def alterCapturedObservation (mutation : MutationRecord) : IO String := do
  let caseResults ← match mutation.observedCaseResults with
    | first :: rest =>
        let verdict := if first.verdict == .unknown then .notFired else .unknown
        pure ({ first with verdict } :: rest)
    | [] => fail "self-test mutation contains no case observation"
  let observation : A12Kernel.Qualification.MutationResult.Observation := {
    exercise := mutation.exercise
    caseResults
    algebraResults := mutation.observedAlgebraResults }
  pure (observation.asJson.pretty 100 ++ "\n")

private def alterBaselineInventory (result : Result) : IO Result := do
  let baseline ← match result.baselineSourceFiles with
    | file :: rest => pure ({ file with sha256 := ← wrongDigest file.sha256 } :: rest)
    | [] => fail "self-test result contains no baseline inventory"
  pure { result with baselineSourceFiles := baseline }

private def alterFinalGate (result : Result) : IO Result :=
  pure { result with finalRestorationGate := {
    result.finalRestorationGate with outcome := .failed } }

private def allResultLogs (result : Result) : List FileDigest :=
  result.naturalGate.rawLogs ++ result.mutations.flatMap (·.rawLogs) ++
    result.finalRestorationGate.rawLogs

private def replaceLogDigest (logs : List FileDigest) (path : PortablePath)
    (sha256 : Digest) : List FileDigest :=
  logs.map fun log => if log.path == path then { log with sha256 } else log

private def updateLogDigest (result : Result) (path : PortablePath) (sha256 : Digest) : IO Result := do
  let matching := (allResultLogs result).filter (·.path == path)
  if matching.length != 1 then
    fail s!"self-test expected one result log at '{path}', found {matching.length}"
  let updateGate (gate : A12Kernel.Qualification.MutationResult.GateRecord) := {
    gate with rawLogs := replaceLogDigest gate.rawLogs path sha256 }
  let updateMutation (mutation : MutationRecord) := {
    mutation with rawLogs := replaceLogDigest mutation.rawLogs path sha256 }
  pure {
    result with
    naturalGate := updateGate result.naturalGate
    mutations := result.mutations.map updateMutation
    finalRestorationGate := updateGate result.finalRestorationGate }

private def requireCommand (commands : List CommandRecord) (id context : String) : IO CommandRecord :=
  match commands.filter (·.id == id) with
  | [command] => pure command
  | [] => fail s!"self-test {context} contains no command '{id}'"
  | _ => fail s!"self-test {context} contains duplicate command '{id}'"

private def checkMutatedResult (packetPath resultPath : System.FilePath) (index : Index)
    (label expectedMessage : String) (mutate : Result → IO Result) (result : Result) : IO Unit := do
  let altered ← mutate result
  withRestoredText resultPath (renderResult altered) do
    requireFailure label expectedMessage
      (A12Kernel.Qualification.Checker.checkResult packetPath resultPath index
        .sourceExecutedReplay)

private def checkMutatedPacket (projectRoot candidateRoot packetPath : System.FilePath)
    (label expectedMessage : String) (index : Index) : IO Unit :=
  withRestoredText packetPath (renderPacket index) do
    requireFailure label expectedMessage
      (A12Kernel.Qualification.Checker.readAndVerifyPacket
        projectRoot candidateRoot packetPath true)

private def checkSourceUnapprovedPatch (projectRoot packetRoot : System.FilePath)
    (index : Index) : IO Unit := do
  let first ← match index.mutations with
    | mutation :: _ => pure mutation
    | [] => fail "self-test packet contains no mutation"
  let alteredFirst := {
    first with
    patch := { first.patch with sha256 := index.baselineObserverPatch.sha256 }
    mutatedSourceFiles := index.instrumentedBaselineSourceFiles }
  let alteredIndex := { index with mutations := alteredFirst :: index.mutations.drop 1 }
  let replacement ← IO.FS.readFile
    (packetRoot / index.baselineObserverPatch.path.toString)
  withRestoredText (packetRoot / first.patch.path.toString) replacement do
    requireFailure "source-unapproved but valid-applying mutation patch"
      "patch differs from the source-owned projection" <|
      A12Kernel.Qualification.Checker.validateSourceOwnedPatches
        projectRoot packetRoot alteredIndex

private def checkChangedLog (packetPath resultPath resultRoot : System.FilePath)
    (index : Index) (label expectedMessage : String) (path : PortablePath) (content : String)
    (result : Result) : IO Unit := do
  let absolute := resultRoot / path.toString
  withRestoredText absolute content do
    let altered ← updateLogDigest result path (← hashFile absolute)
    withRestoredText resultPath (renderResult altered) do
      requireFailure label expectedMessage
        (A12Kernel.Qualification.Checker.checkResult packetPath resultPath index
          .sourceExecutedReplay)

private def oversizedText (minimumBytes : Nat) : String :=
  let chunk := String.ofList (List.replicate 1024 'x')
  String.join (List.replicate (minimumBytes / 1024 + 1) chunk)

private def runProcess (cmd : String) (args : Array String)
    (cwd : Option System.FilePath := none) : IO Unit := do
  let output ← IO.Process.output { cmd, args, cwd }
  if output.exitCode != 0 then
    fail s!"self-test command '{cmd}' failed with exit {output.exitCode}: {output.stderr.trimAscii.toString}"

private def commitPath (repository : System.FilePath) (path message : String) : IO Unit := do
  runProcess "git" #["-C", repository.toString, "add", "--", path]
  runProcess "git" #["-C", repository.toString,
    "-c", "user.name=Qualification Self-Test",
    "-c", "user.email=qualification-self-test",
    "commit", "-m", message]

private def checkCandidateRevisionClosure (projectRoot candidateRoot packetPath temporary
    : System.FilePath) (index : Index) : IO Unit := do
  let cloneRoot := temporary / "candidate-revision-closure"
  runProcess "git" #["clone", "--local", "--no-hardlinks", candidateRoot.toString,
    cloneRoot.toString]

  let reportPath := cloneRoot / "reports/self-test.md"
  IO.FS.createDirAll (cloneRoot / "reports")
  IO.FS.writeFile reportPath "# Qualification self-test report\n"
  commitPath cloneRoot "reports/self-test.md" "docs: add qualification self-test report"
  let verified ← requireSuccess "report-only candidate descendant" <|
    A12Kernel.Qualification.Checker.readAndVerifyPacket
      projectRoot cloneRoot packetPath true
  if verified != index then fail "report-only candidate verification changed the packet index"

  let libraryPath := cloneRoot / "src/lib.rs"
  let library ← IO.FS.readFile libraryPath
  IO.FS.writeFile libraryPath (library ++ "\n// self-test build-input drift\n")
  commitPath cloneRoot "src/lib.rs" "test: introduce qualification drift"
  requireFailure "committed candidate build-input drift" "candidate build input 'src/lib.rs'" <|
    A12Kernel.Qualification.Checker.readAndVerifyPacket
      projectRoot cloneRoot packetPath true

private def checkPreexistingExportPreserved (projectRoot candidateRoot temporary
    : System.FilePath) : IO Unit := do
  let outputRoot := temporary / "preexisting-export"
  let sentinel := outputRoot / "sentinel.txt"
  IO.FS.createDirAll outputRoot
  IO.FS.writeFile sentinel "preserve me\n"
  let executable ← IO.appPath
  let output ← IO.Process.output {
    cmd := executable.toString
    args := #["--export", "--candidate-repo", candidateRoot.toString,
      "--output", outputRoot.toString]
    cwd := some projectRoot }
  if output.exitCode == 0 then
    fail "self-test export unexpectedly accepted a pre-existing output directory"
  if !output.stderr.contains "qualification packet output already exists" then
    fail s!"self-test export failed at the wrong boundary: {output.stderr.trimAscii.toString}"
  if !(← System.FilePath.pathExists sentinel) then
    fail "self-test export failure removed a pre-existing output directory"
  if (← IO.FS.readFile sentinel) != "preserve me\n" then
    fail "self-test export failure removed or changed a pre-existing output directory"

private def unknownPacketMember (canonical : String) : IO String :=
  duplicateTopLevelMember canonical "selfTestUnknown" "true"

/-- Export and verify a real packet, execute its complete Rust replay, then require each adversarial mutation to fail independently. The returned count is the number of rejection guards executed. -/
def run (projectRoot candidateRoot : System.FilePath) : IO Nat :=
  IO.FS.withTempDir fun temporary => do
    let packetRoot := temporary / "packet"
    let resultRoot := temporary / "result"
    let packetPath := packetRoot / "PACKET.json"
    let resultPath := resultRoot / "RESULT.json"
    let exported ← A12Kernel.Qualification.RustPacket.exportPacket
      projectRoot candidateRoot packetRoot true
    let index ← A12Kernel.Qualification.Checker.readAndVerifyPacket
      projectRoot candidateRoot packetPath true
    if index != exported then fail "self-test packet changed across export and verification"
    let result ← A12Kernel.Qualification.Runner.run packetPath resultRoot index
    let capturedResult ← IO.FS.readFile resultPath
    if capturedResult != renderResult result then
      fail "source-executed result bytes differ from the returned record"

    let mut guards := 0
    let canonicalPacket ← IO.FS.readFile packetPath
    withRestoredText packetPath (← unknownPacketMember canonicalPacket) do
      requireFailure "unknown PACKET member" "unknown member"
        (A12Kernel.Qualification.Checker.readAndVerifyPacket
          projectRoot candidateRoot packetPath true)
    guards := guards + 1

    let payload := index.expectedBaselineObservation
    withCorruptedFile (packetRoot / payload.path.toString) do
      requireFailure "corrupted packet payload digest" "digest mismatch"
        (A12Kernel.Qualification.Checker.readAndVerifyPacket
          projectRoot candidateRoot packetPath true)
    guards := guards + 1

    withExtraFile (packetRoot / "self-test-extra.txt") do
      requireFailure "extra packet file" "file tree is not exact"
        (A12Kernel.Qualification.Checker.readAndVerifyPacket
          projectRoot candidateRoot packetPath true)
    guards := guards + 1

    withRemovedFile (packetRoot / payload.path.toString) do
      requireFailure "missing packet file" "file tree is not exact"
        (A12Kernel.Qualification.Checker.readAndVerifyPacket
          projectRoot candidateRoot packetPath true)
    guards := guards + 1

    checkMutatedPacket projectRoot candidateRoot packetPath "packet compatibility drift"
      "compatibility identity differs" {
      index with compatibility := {
        index.compatibility with protocolVersion := index.compatibility.protocolVersion + 1 } }
    guards := guards + 1

    checkMutatedPacket projectRoot candidateRoot packetPath "packet source revision drift"
      "qualification packet requires" {
      index with sourceRevision := alternativeRevision index.sourceRevision }
    guards := guards + 1

    let reorderedPacketMutations ← match index.mutations with
      | first :: second :: rest => pure (second :: first :: rest)
      | _ => fail "self-test packet contains fewer than two mutations"
    checkMutatedPacket projectRoot candidateRoot packetPath "packet mutation order drift"
      "exercise is" {
      index with mutations := reorderedPacketMutations }
    guards := guards + 1

    checkSourceUnapprovedPatch projectRoot packetRoot index
    guards := guards + 1

    let duplicateResult ← duplicateTopLevelMember capturedResult "packetId"
      (toJson result.packetId).compress
    withRestoredText resultPath duplicateResult do
      requireFailure "duplicate result JSON member" "duplicate" <|
        A12Kernel.Qualification.Checker.checkResult packetPath resultPath index
          .sourceExecutedReplay
    guards := guards + 1

    let missingResultMember := (← removeMember result.asJson "packetId").pretty 100 ++ "\n"
    withRestoredText resultPath missingResultMember do
      requireFailure "missing result JSON member" "missing member 'packetId'" <|
        A12Kernel.Qualification.Checker.checkResult packetPath resultPath index
          .sourceExecutedReplay
    guards := guards + 1

    let firstResultLog ← match allResultLogs result with
      | log :: _ => pure log
      | [] => fail "self-test result contains no logs"
    withExtraFile (resultRoot / "self-test-extra.log") do
      requireFailure "extra result file" "file tree is not exact" <|
        A12Kernel.Qualification.Checker.checkResult packetPath resultPath index
          .sourceExecutedReplay
    guards := guards + 1

    withRemovedFile (resultRoot / firstResultLog.path.toString) do
      requireFailure "missing result file" "file tree is not exact" <|
        A12Kernel.Qualification.Checker.checkResult packetPath resultPath index
          .sourceExecutedReplay
    guards := guards + 1

    checkMutatedResult packetPath resultPath index "missing mutation case result"
      "complete ordered case results differ"
      dropFirstCase result
    guards := guards + 1

    checkMutatedResult packetPath resultPath index "reordered mutation case result"
      "complete ordered case results differ"
      reorderFirstCases result
    guards := guards + 1

    checkMutatedResult packetPath resultPath index "altered command argv"
      "recorded commands differ"
      alterFirstCommand result
    guards := guards + 1

    checkMutatedResult packetPath resultPath index "wrong raw-log digest"
      "digest mismatch"
      alterFirstLogDigest result
    guards := guards + 1

    checkMutatedResult packetPath resultPath index "reused cross-phase log path"
      "reuses a command-log path across phases"
      reuseCrossPhaseLog result
    guards := guards + 1

    checkMutatedResult packetPath resultPath index "case-folded cross-phase log path"
      "collide on a case-insensitive filesystem"
      reuseCaseFoldedCrossPhaseLog result
    guards := guards + 1

    checkMutatedResult packetPath resultPath index "result packet digest drift"
      "packet-index digest mismatch"
      (fun value => do
        pure { value with packetIndexSha256 := ← wrongDigest value.packetIndexSha256 }) result
    guards := guards + 1

    checkMutatedResult packetPath resultPath index "result assurance-class drift"
      "assurance class differs"
      (fun value => pure { value with assuranceClass := .isolatedSessionAttestation }) result
    guards := guards + 1

    checkMutatedResult packetPath resultPath index "result unresolved question"
      "unresolved questions"
      (fun value => pure { value with unresolvedQuestions := ["self-test unresolved"] }) result
    guards := guards + 1

    checkMutatedResult packetPath resultPath index "result mutation-id drift"
      "mutation id"
      alterMutationId result
    guards := guards + 1

    checkMutatedResult packetPath resultPath index "result mutation order drift"
      "record exercise is"
      reorderMutations result
    guards := guards + 1

    checkMutatedResult packetPath resultPath index "result mutation patch drift"
      "patch does not match the packet"
      alterMutationPatch result
    guards := guards + 1

    checkMutatedResult packetPath resultPath index "result algebra drift"
      "complete ordered algebra results differ"
      alterAlgebraResult result
    guards := guards + 1

    checkMutatedResult packetPath resultPath index "result baseline inventory drift"
      "baseline source inventory mismatch"
      alterBaselineInventory result
    guards := guards + 1

    checkMutatedResult packetPath resultPath index "result final gate drift"
      "final restoration gate: gate did not pass"
      alterFinalGate result
    guards := guards + 1

    let baselineObserver ← requireCommand result.naturalGate.commands
      "observe-baseline" "natural gate"
    checkChangedLog packetPath resultPath resultRoot index
      "semantically wrong baseline observer log" "missing member"
      baselineObserver.stdoutLog "{}\n" result
    guards := guards + 1

    let firstMutation ← match result.mutations with
      | mutation :: _ => pure mutation
      | [] => fail "self-test result contains no mutation"
    let mutationObserver ← requireCommand firstMutation.commands "observe" "first mutation"
    checkChangedLog packetPath resultPath resultRoot index
      "captured mutation observation differs from record"
      "recorded case results differ from captured observer output"
      mutationObserver.stdoutLog (← alterCapturedObservation firstMutation) result
    guards := guards + 1

    let rustcVersion ← requireCommand result.naturalGate.commands
      "rustc-version" "natural gate"
    checkChangedLog packetPath resultPath resultRoot index
      "semantically wrong toolchain log" "log differs from the packet identity"
      rustcVersion.stdoutLog "rustc self-test-wrong\n" result
    guards := guards + 1

    let naturalInventory ← requireCommand result.naturalGate.commands
      "natural-source-inventory" "natural gate"
    checkChangedLog packetPath resultPath resultRoot index
      "semantically wrong inventory log" "stdout differs from its packet manifest"
      naturalInventory.stdoutLog "wrong inventory\n" result
    guards := guards + 1

    checkChangedLog packetPath resultPath resultRoot index
      "nonempty observer stderr" "natural baseline observer wrote stderr"
      baselineObserver.stderrLog "unexpected observer stderr\n" result
    guards := guards + 1

    withRestoredText resultPath (oversizedText (4 * 1024 * 1024)) do
      requireFailure "oversized result JSON" "exceeds the 4194304-byte" <|
        A12Kernel.Qualification.Checker.checkResult packetPath resultPath index
          .sourceExecutedReplay
    guards := guards + 1

    withRestoredText (resultRoot / firstResultLog.path.toString)
        (oversizedText (16 * 1024 * 1024)) do
      requireFailure "oversized result log" "exceeds the 16777216-byte" <|
        A12Kernel.Qualification.Checker.checkResult packetPath resultPath index
          .sourceExecutedReplay
    guards := guards + 1

    checkCandidateRevisionClosure projectRoot candidateRoot packetPath temporary index
    guards := guards + 1

    checkPreexistingExportPreserved projectRoot candidateRoot temporary
    guards := guards + 1

    pure guards

end A12Kernel.Qualification.SelfTest
