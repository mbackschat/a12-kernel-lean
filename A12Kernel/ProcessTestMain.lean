import A12Kernel.Process.Bounded

/-! # A12Kernel.ProcessTestMain — black-box bounded-process regression gate -/

namespace A12Kernel.ProcessTest

open A12Kernel.Process.Bounded

private def fail (message : String) : IO α :=
  throw (IO.userError message)

private def require (condition : Bool) (message : String) : IO Unit := do
  if !condition then fail message

private def writeStdout (content : String) : IO Unit := do
  let stdout ← IO.getStdout
  stdout.putStr content
  stdout.flush

private def writeStderr (content : String) : IO Unit := do
  let stderr ← IO.getStderr
  stderr.putStr content
  stderr.flush

private def repeated (count : Nat) : String :=
  String.ofList (List.replicate count 'x')

private partial def flood (stream : IO.FS.Stream) : IO UInt32 := do
  stream.putStr (repeated 4096)
  stream.flush
  flood stream

private def child : List String → IO UInt32
  | ["echo"] => do
      writeStdout (← (← IO.getStdin).readToEnd)
      pure 0
  | ["stdout-bytes", count] =>
      match count.toNat? with
      | some count => writeStdout (repeated count) *> pure 0
      | none => pure 2
  | ["stderr-bytes", count] =>
      match count.toNat? with
      | some count => writeStderr (repeated count) *> pure 0
      | none => pure 2
  | ["stdout-infinite"] => do
      flood (← IO.getStdout)
  | ["stderr-infinite"] => do
      flood (← IO.getStderr)
  | ["both-overflow"] => do
      writeStdout (repeated 8192)
      writeStderr (repeated 8192)
      pure 0
  | ["binary"] => do
      let stdout ← IO.getStdout
      stdout.write (ByteArray.mk #[0x00, 0xff, 0x0a])
      stdout.flush
      pure 0
  | ["ignore-input"] =>
      pure 0
  | ["sleep"] => do
      IO.sleep 10000
      pure 0
  | ["exit-seven"] => do
      writeStderr "candidate diagnostic\n"
      pure 7
  | ["descendant-parent", marker] => do
      let self ← IO.appPath
      let _ ← IO.Process.spawn {
        cmd := self.toString
        args := #["--child", "descendant", marker]
        stdin := .null
        stdout := .inherit
        stderr := .inherit }
      pure 0
  | ["descendant-close-parent", marker] => do
      let self ← IO.appPath
      let _ ← IO.Process.spawn {
        cmd := self.toString
        args := #["--child", "descendant", marker]
        stdin := .null
        stdout := .null
        stderr := .null }
      pure 0
  | ["descendant", marker] => do
      IO.sleep 500
      IO.FS.writeFile marker "escaped process group"
      pure 0
  | _ => do
      writeStderr "checkBoundedProcess child: unsupported mode\n"
      pure 2

private def executable (name : String) : IO System.FilePath := do
  let directory ← IO.appDir
  pure ((directory / name).addExtension System.FilePath.exeExtension)

private def baseLimits : Limits := {
  timeoutMs := 2000
  cleanupMs := 1000
  pollMs := 5
  inputBytes := 4096
  stdoutBytes := 1024
  stderrBytes := 1024 }

private def invoke (arguments : Array String) (input : String := "request\n")
    (limits : Limits := baseLimits) : IO (Except Failure Output) := do
  runViaRelay (← executable "a12-bounded-process-relay")
    (← executable "checkBoundedProcess") (#["--child"] ++ arguments) input limits

private def expectSuccess : IO Unit := do
  let input := "bounded echo\n"
  match ← invoke #["echo"] input with
  | .error failure => fail s!"bounded echo failed: {repr failure.kind}; cleanup={repr failure.cleanup}; relayExit={repr failure.relayExitCode?}"
  | .ok output => do
      require (output.exitCode == 0) "bounded echo returned a nonzero exit"
      require (String.fromUTF8? output.stdout == some input) "bounded echo changed stdout"
      require output.stderr.isEmpty "bounded echo wrote stderr"

private def expectNonzeroPreserved : IO Unit := do
  match ← invoke #["exit-seven"] with
  | .error failure => fail s!"bounded nonzero case failed: {repr failure.kind}"
  | .ok output => do
      require (output.exitCode == 7) "bounded process did not preserve exit code 7"
      require output.stdout.isEmpty "bounded nonzero case wrote stdout"
      require (String.fromUTF8? output.stderr == some "candidate diagnostic\n")
        "bounded process confused candidate stderr with relay diagnostics"

private def requireCleanup (label : String) (failure : Failure) : IO Unit := do
  require failure.cleanup.tasksCompleted
    s!"bounded process did not finish cleanup after {label}"
  require failure.cleanup.waitError?.isNone
    s!"bounded process wait failed during cleanup after {label}"
  match failure.cleanup.kill with
  | .killed | .alreadyGone => pure ()
  | .failed message =>
      fail s!"bounded process group cleanup failed after {label}: {message}"

private def expectLimit (arguments : Array String) (expected : FailureKind)
    (limits : Limits) : IO Unit := do
  match ← invoke arguments "request\n" limits with
  | .ok _ => fail s!"bounded process did not enforce {repr expected}"
  | .error failure => do
      require (failure.kind == expected)
        s!"bounded process returned {repr failure.kind}, expected {repr expected}"
      requireCleanup s!"{repr expected}" failure

private def expectTimeout : IO Unit := do
  let limits := { baseLimits with timeoutMs := 100, cleanupMs := 500, pollMs := 5 }
  match ← invoke #["sleep"] "request\n" limits with
  | .ok _ => fail "bounded process did not time out"
  | .error failure => do
      require (failure.kind == .timedOut) s!"timeout returned {repr failure.kind}"
      requireCleanup "timeout" failure
      require (failure.elapsedMs <= limits.timeoutMs + limits.cleanupMs + 250)
        "timeout exceeded its execution, cleanup, and scheduling allowance"

private def expectOutputLimits : IO Unit := do
  let limits := { baseLimits with stdoutBytes := 64, stderrBytes := 64 }
  match ← invoke #["stdout-bytes", "64"] "request\n" limits with
  | .ok output => require (output.stdout.size == 64) "an exact stdout cap was not accepted"
  | .error failure => fail s!"an exact stdout cap failed: {repr failure.kind}"
  match ← invoke #["stderr-bytes", "64"] "request\n" limits with
  | .ok output => require (output.stderr.size == 64) "an exact stderr cap was not accepted"
  | .error failure => fail s!"an exact stderr cap failed: {repr failure.kind}"
  expectLimit #["stdout-bytes", "65"] .stdoutLimitExceeded limits
  expectLimit #["stderr-bytes", "65"] .stderrLimitExceeded limits
  expectLimit #["stdout-infinite"] .stdoutLimitExceeded limits
  expectLimit #["stderr-infinite"] .stderrLimitExceeded limits
  match ← invoke #["both-overflow"] "request\n" limits with
  | .ok _ => fail "simultaneous stdout/stderr pressure escaped both caps"
  | .error failure => do
      require (failure.kind == .stdoutLimitExceeded || failure.kind == .stderrLimitExceeded)
        s!"simultaneous output pressure returned {repr failure.kind}"
      requireCleanup "simultaneous stdout/stderr pressure" failure

private def expectBlockedInput : IO Unit := do
  let input := String.ofList (List.replicate (1024 * 1024) 'i')
  expectLimit #["sleep"] .timedOut {
    baseLimits with timeoutMs := 150, cleanupMs := 500, inputBytes := input.utf8ByteSize }

private def expectBinaryTransparency : IO Unit := do
  match ← invoke #["binary"] with
  | .error failure => fail s!"binary capture failed: {repr failure.kind}"
  | .ok output => do
      require (output.stdout == ByteArray.mk #[0x00, 0xff, 0x0a])
        "relay changed binary stdout bytes"
      require (String.fromUTF8? output.stdout).isNone
        "invalid UTF-8 unexpectedly decoded"

private def expectIgnoredInput : IO Unit := do
  let input := String.ofList (List.replicate (1024 * 1024) 'i')
  match ← invoke #["ignore-input"] input { baseLimits with inputBytes := input.utf8ByteSize } with
  | .error failure =>
      fail s!"candidate that ignored stdin failed: {repr failure.kind}"
  | .ok output => do
      require (output.exitCode == 0) "candidate that ignored stdin changed its exit code"
      require output.stdout.isEmpty "candidate that ignored stdin wrote stdout"
      require output.stderr.isEmpty "candidate that ignored stdin wrote stderr"

private def expectGroupTermination : IO Unit := do
  IO.FS.withTempDir fun directory => do
    let marker := directory / "escaped.txt"
    expectLimit #["descendant-parent", marker.toString] .timedOut
      { baseLimits with timeoutMs := 150, pollMs := 5 }
    IO.sleep 600
    require (!(← marker.pathExists))
      "a descendant escaped bounded process-group termination"
  IO.FS.withTempDir fun directory => do
    let marker := directory / "escaped-after-success.txt"
    match ← invoke #["descendant-close-parent", marker.toString] with
    | .error failure => fail s!"success-path descendant case failed: {repr failure.kind}"
    | .ok output => require (output.exitCode == 0) "success-path descendant parent failed"
    IO.sleep 600
    require (!(← marker.pathExists))
      "a closed-stdio descendant survived successful relay completion"

private def expectCandidatePreflight : IO Unit := do
  let relay ← executable "a12-bounded-process-relay"
  let missing := System.FilePath.mk "/path/that/does/not/exist/a12-candidate"
  let accepted ← try
    let _ ← runViaRelay relay missing #[] "request\n" baseLimits
    pure true
  catch _ =>
    pure false
  require (!accepted) "bounded process reported a missing candidate as a candidate result"

private def expectRelayDiagnostic : IO Unit := do
  let relay ← executable "a12-bounded-process-relay"
  let missingInput := System.FilePath.mk "/path/that/does/not/exist/a12-input"
  let output ← IO.Process.output {
    cmd := relay.toString
    args := #[relay.toString, missingInput.toString] }
  require (output.exitCode == 1)
    s!"relay classified its own input failure as exit {output.exitCode}"
  require (output.stderr.startsWith "a12-bounded-process-relay: ")
    "relay failure omitted its diagnostic prefix"

private def expectStatusGuards : IO Unit := do
  let exact := RelayStatus.render 7
  match RelayStatus.parse exact.toUTF8 with
  | .ok exitCode => require (exitCode == 7) "relay status changed exit code 7"
  | .error error => fail s!"relay status did not round-trip: {error}"
  for (label, status) in [
      ("request bytes", "missing status"),
      ("the wrong magic", "wrong\n0\n"),
      ("a leading-zero exit code", s!"{RelayStatus.magic}\n00\n"),
      ("a separated exit code", s!"{RelayStatus.magic}\n1_0\n"),
      ("an oversized record", repeated (RelayStatus.maxBytes + 1))] do
    match RelayStatus.parse status.toUTF8 with
    | .error _ => pure ()
    | .ok _ => fail s!"relay status accepted {label}"

private def expectInvalidLimits : IO Unit := do
  let succeeded ← try
    let _ ← invoke #["echo"] "request\n" { baseLimits with pollMs := 0 }
    pure true
  catch _ =>
    pure false
  require (!succeeded) "bounded process accepted a zero poll interval"

def selfTest : IO Unit := do
  expectSuccess
  expectNonzeroPreserved
  expectTimeout
  expectOutputLimits
  expectBlockedInput
  expectBinaryTransparency
  expectRelayDiagnostic
  expectIgnoredInput
  expectGroupTermination
  expectCandidatePreflight
  expectStatusGuards
  expectInvalidLimits
  IO.println "bounded process: exact bytes, ignored input, relay diagnostics, exit/status separation, timeout, blocked input, output caps, process-group cleanup, and limit guards passed"

def run : List String → IO UInt32
  | "--child" :: arguments => child arguments
  | [] => selfTest *> pure 0
  | _ => do
      writeStderr "checkBoundedProcess: expected no arguments\n"
      pure 2

end A12Kernel.ProcessTest

def main (args : List String) : IO UInt32 := do
  try
    A12Kernel.ProcessTest.run args
  catch error =>
    let stderr ← IO.getStderr
    stderr.putStr s!"checkBoundedProcess: {error}\n"
    stderr.flush
    pure 1
