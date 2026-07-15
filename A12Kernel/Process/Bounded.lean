/-! # A12Kernel.Process.Bounded — bounded subprocess capture

This IO-only module runs a candidate behind the project-owned streaming relay. The outer child has null stdin and therefore retains its original `setsid` metadata, which the pinned Lean 4.31 runtime uses to hard-kill the relay process group. The helper is a resource boundary for cooperative implementation testing on macOS and Linux, not a security sandbox; the candidate and its descendants must retain the caller's credentials.
-/

namespace A12Kernel.Process.Bounded

structure Limits where
  timeoutMs : Nat
  cleanupMs : Nat
  pollMs : Nat
  inputBytes : Nat
  stdoutBytes : Nat
  stderrBytes : Nat
  deriving Repr, DecidableEq

namespace Limits

def validate (limits : Limits) : Except String Unit := do
  if limits.timeoutMs == 0 || limits.timeoutMs > 300000 then
    throw "timeoutMs must be between 1 and 300000"
  if limits.cleanupMs == 0 || limits.cleanupMs > 10000 then
    throw "cleanupMs must be between 1 and 10000"
  if limits.pollMs == 0 then
    throw "pollMs must be positive"
  if limits.pollMs > limits.timeoutMs || limits.pollMs > limits.cleanupMs then
    throw "pollMs must not exceed timeoutMs or cleanupMs"
  if limits.pollMs >= UInt32.size then
    throw "pollMs exceeds the Lean sleep range"
  if limits.inputBytes == 0 || limits.inputBytes > 1024 * 1024 then
    throw "inputBytes must be between 1 and 1048576"
  if limits.stdoutBytes == 0 || limits.stdoutBytes > 16 * 1024 * 1024 then
    throw "stdoutBytes must be between 1 and 16777216"
  if limits.stderrBytes == 0 || limits.stderrBytes > 16 * 1024 * 1024 then
    throw "stderrBytes must be between 1 and 16777216"

end Limits

structure Capture where
  bytes : ByteArray
  exceeded : Bool
  deriving DecidableEq

inductive FailureKind where
  | timedOut
  | stdoutLimitExceeded
  | stderrLimitExceeded
  | stdoutReadFailed (message : String)
  | stderrReadFailed (message : String)
  | waitFailed (message : String)
  | relayExited (exitCode : UInt32)
  | relayStatusInvalid (message : String)
  | cleanupFailed
  deriving Repr, DecidableEq

inductive KillOutcome where
  | killed
  | alreadyGone
  | failed (message : String)
  deriving Repr, DecidableEq

structure CleanupOutcome where
  kill : KillOutcome
  tasksCompleted : Bool
  waitError? : Option String
  deriving Repr, DecidableEq

structure Failure where
  kind : FailureKind
  cleanup : CleanupOutcome
  elapsedMs : Nat
  relayExitCode? : Option UInt32
  stdout : Capture
  stderr : Capture
  deriving DecidableEq

structure Output where
  exitCode : UInt32
  elapsedMs : Nat
  stdout : ByteArray
  stderr : ByteArray
  deriving DecidableEq

namespace RelayStatus

def magic : String := "a12-bounded-process-relay-v1"

def maxBytes : Nat := 64

def render (exitCode : UInt32) : String :=
  s!"{magic}\n{exitCode}\n"

def parse (bytes : ByteArray) : Except String UInt32 := do
  if bytes.size > maxBytes then throw "status exceeds 64 bytes"
  let text ← match String.fromUTF8? bytes with
    | some value => pure value
    | none => throw "status is not UTF-8"
  match text.splitOn "\n" with
  | [receivedMagic, exitCodeText, ""] =>
      if receivedMagic != magic then throw "status magic does not match"
      if exitCodeText.isEmpty || !exitCodeText.toList.all fun character =>
          '0' <= character && character <= '9' then
        throw "status exit code is not canonical ASCII decimal"
      let exitCode ← match exitCodeText.toNat? with
        | some value => pure value
        | none => throw "status exit code is not a natural number"
      if toString exitCode != exitCodeText then
        throw "status exit code is not canonical ASCII decimal"
      if exitCode >= UInt32.size then throw "status exit code exceeds UInt32"
      pure (UInt32.ofNat exitCode)
  | _ => throw "status has the wrong line structure"

end RelayStatus

/-- Whether the host provides the POSIX process-group contract used by this helper. -/
def supportedHost : Bool :=
  !System.Platform.isWindows && !System.Platform.isEmscripten &&
    (System.Platform.isOSX || System.Platform.target.contains "linux")

private partial def readBounded (handle : IO.FS.Handle) (limit : Nat) : IO Capture := do
  -- On the pinned toolchain, compiled `ByteArray.append` uses `fastAppend` with
  -- asymptotic capacity growth, so the single accumulator scales to the public cap.
  let rec loop (accumulator : ByteArray) : IO Capture := do
    let remaining := limit + 1 - accumulator.size
    let chunk ← handle.read (USize.ofNat (min remaining 4096))
    if chunk.isEmpty then
      pure { bytes := accumulator, exceeded := false }
    else
      let next := accumulator ++ chunk
      if next.size > limit then
        pure { bytes := next.extract 0 limit, exceeded := true }
      else
        loop next
  loop ByteArray.empty

private def taskResult? (task : Task (Except IO.Error α)) : BaseIO (Option (Except IO.Error α)) := do
  if ← IO.hasFinished task then
    pure (some task.get)
  else
    pure none

private structure CaptureTasks where
  stdout : Task (Except IO.Error Capture)
  stderr : Task (Except IO.Error Capture)

private structure CleanupTasks where
  exit : Task (Except IO.Error UInt32)
  capture : CaptureTasks

namespace CleanupTasks

private def allFinished (tasks : CleanupTasks) : BaseIO Bool := do
  let exitFinished ← IO.hasFinished tasks.exit
  let stdoutFinished ← IO.hasFinished tasks.capture.stdout
  let stderrFinished ← IO.hasFinished tasks.capture.stderr
  pure (exitFinished && stdoutFinished && stderrFinished)

end CleanupTasks

private inductive PollResult where
  | completed (stdout stderr : Capture)
  | stop (kind : FailureKind)

private partial def poll (tasks : CaptureTasks) (limits : Limits) (startedAt : Nat) : IO PollResult := do
  let now ← IO.monoMsNow
  let elapsed := now - startedAt
  if elapsed >= limits.timeoutMs then
    return .stop .timedOut

  let stdout? ← taskResult? tasks.stdout
  match stdout? with
  | some (.error error) =>
      return .stop (.stdoutReadFailed (toString error))
  | some (.ok capture) =>
      if capture.exceeded then return .stop .stdoutLimitExceeded
  | none => pure ()

  let stderr? ← taskResult? tasks.stderr
  match stderr? with
  | some (.error error) =>
      return .stop (.stderrReadFailed (toString error))
  | some (.ok capture) =>
      if capture.exceeded then return .stop .stderrLimitExceeded
  | none => pure ()

  match stdout?, stderr? with
  | some (.ok stdout), some (.ok stderr) =>
      return .completed stdout stderr
  | _, _ => pure ()

  IO.sleep (UInt32.ofNat (min limits.pollMs (limits.timeoutMs - elapsed)))
  poll tasks limits startedAt

private def killGroup (child : IO.Process.Child {
    stdin := .null, stdout := .piped, stderr := .piped }) : IO KillOutcome := do
  try
    child.kill
    pure .killed
  catch error =>
    match error with
    | .noSuchThing .. => pure .alreadyGone
    -- macOS reports EPERM when the setsid group contains only the completed,
    -- unreaped relay. The owned relay has not yet been waited on, so its PID
    -- still reserves the process-group ID and this cannot target a reused group.
    | .permissionDenied none 1 _ => pure .alreadyGone
    | _ => pure (.failed (toString error))

private partial def waitForTasks (tasks : CleanupTasks) (pollMs cleanupMs startedAt : Nat) : IO Bool := do
  if ← tasks.allFinished then return true
  let elapsed := (← IO.monoMsNow) - startedAt
  if elapsed >= cleanupMs then return false
  IO.sleep (UInt32.ofNat (min pollMs (cleanupMs - elapsed)))
  waitForTasks tasks pollMs cleanupMs startedAt

private def cleanupGroup (child : IO.Process.Child {
    stdin := .null, stdout := .piped, stderr := .piped })
    (capture : CaptureTasks) (limits : Limits) : IO (CleanupOutcome × Option UInt32) := do
  let kill ← killGroup child
  let tasks : CleanupTasks := {
    exit := ← IO.asTask child.wait Task.Priority.dedicated
    capture }
  let cleanupStartedAt ← IO.monoMsNow
  let tasksCompleted ← waitForTasks tasks limits.pollMs limits.cleanupMs cleanupStartedAt
  let exitResult? ← taskResult? tasks.exit
  let waitError? := match exitResult? with
    | some (.error error) => some (toString error)
    | _ => none
  let exitCode? := match exitResult? with
    | some (.ok exitCode) => some exitCode
    | _ => none
  pure ({ kill, tasksCompleted, waitError? }, exitCode?)

private def captureTask? (task : Task (Except IO.Error Capture)) : BaseIO (Option Capture) := do
  match ← taskResult? task with
  | some (.ok capture) => pure (some capture)
  | _ => pure none

private def failureFromTasks (tasks : CaptureTasks) (startedAt : Nat) (kind : FailureKind)
    (cleanup : CleanupOutcome) (relayExitCode? : Option UInt32) : IO Failure := do
  let empty : Capture := { bytes := ByteArray.empty, exceeded := false }
  pure {
    kind
    cleanup
    elapsedMs := (← IO.monoMsNow) - startedAt
    relayExitCode?
    stdout := (← captureTask? tasks.stdout).getD empty
    stderr := (← captureTask? tasks.stderr).getD empty }

private def cleanupFinished (cleanup : CleanupOutcome) : Bool :=
  cleanup.tasksCompleted && match cleanup.kill with
    | .killed | .alreadyGone => true
    | .failed _ => false

private def requireFile (label : String) (path : System.FilePath) : IO Unit := do
  let metadata ← try
    path.metadata
  catch error =>
    throw (IO.userError s!"bounded-process {label} '{path}' is unavailable: {error}")
  if metadata.type != .file then
    throw (IO.userError s!"bounded-process {label} '{path}' is not a file")

/-- Runs `candidate` through `relay`, enforcing input, output, execution, and cleanup limits. The cooperative relay contract is restricted to inherited credentials, working directory, and environment. -/
def runViaRelay (relay candidate : System.FilePath) (candidateArgs : Array String)
    (input : String) (limits : Limits) : IO (Except Failure Output) := do
  if !supportedHost then
    throw (IO.userError s!"bounded-process supports only macOS and Linux, found '{System.Platform.target}'")
  match limits.validate with
  | .error message => throw (IO.userError s!"invalid bounded-process limits: {message}")
  | .ok () => pure ()
  requireFile "relay" relay
  requireFile "candidate" candidate
  let inputBytes := input.toUTF8
  if inputBytes.size > limits.inputBytes then
    throw (IO.userError s!"bounded-process input has {inputBytes.size} bytes, maximum {limits.inputBytes}")
  IO.FS.withTempFile fun handle path => do
    handle.write inputBytes
    handle.flush
    let startedAt ← IO.monoMsNow
    let child ← IO.Process.spawn {
      cmd := relay.toString
      args := #[candidate.toString, path.toString] ++ candidateArgs
      stdin := .null
      stdout := .piped
      stderr := .piped
      setsid := true }
    let tasks : CaptureTasks := {
      stdout := ← IO.asTask (readBounded child.stdout limits.stdoutBytes) Task.Priority.dedicated
      stderr := ← IO.asTask (readBounded child.stderr limits.stderrBytes) Task.Priority.dedicated }
    match ← poll tasks limits startedAt with
    | .stop kind =>
        let (cleanup, relayExitCode?) ← cleanupGroup child tasks limits
        pure (.error (← failureFromTasks tasks startedAt kind cleanup relayExitCode?))
    | .completed stdout stderr =>
        let (cleanup, relayExitCode?) ← cleanupGroup child tasks limits
        if !cleanupFinished cleanup then
          pure (.error (← failureFromTasks tasks startedAt .cleanupFailed cleanup relayExitCode?))
        else match cleanup.waitError? with
          | some message =>
              pure (.error (← failureFromTasks tasks startedAt (.waitFailed message) cleanup none))
          | none => match relayExitCode? with
            | none =>
                pure (.error (← failureFromTasks tasks startedAt
                  (.waitFailed "relay wait completed without an exit code") cleanup none))
            | some relayExitCode =>
                if relayExitCode != 0 then
                  pure (.error (← failureFromTasks tasks startedAt (.relayExited relayExitCode) cleanup (some relayExitCode)))
                else
                  let status ← IO.FS.withFile path .read fun statusHandle =>
                    readBounded statusHandle RelayStatus.maxBytes
                  if status.exceeded then
                    pure (.error (← failureFromTasks tasks startedAt
                      (.relayStatusInvalid "status exceeds 64 bytes") cleanup (some relayExitCode)))
                  else match RelayStatus.parse status.bytes with
                    | .error message =>
                        pure (.error (← failureFromTasks tasks startedAt
                          (.relayStatusInvalid message) cleanup (some relayExitCode)))
                    | .ok exitCode =>
                        pure (.ok {
                          exitCode
                          elapsedMs := (← IO.monoMsNow) - startedAt
                          stdout := stdout.bytes
                          stderr := stderr.bytes })

end A12Kernel.Process.Bounded
