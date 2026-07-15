import A12Kernel.Process.Bounded

/-! # A12Kernel.Process.RelayMain — streaming candidate relay

The bounded parent starts this executable as a new process group with null stdin. The relay feeds one capped request from a temporary file to the candidate, streams both output channels without retaining them, and overwrites the request file with a strict completion record only after every candidate channel completes.
-/

namespace A12Kernel.Process.Relay

private partial def copy (source : IO.FS.Handle) (destination : IO.FS.Stream) : IO Unit := do
  let rec loop : IO Unit := do
    let chunk ← source.read 4096
    if chunk.isEmpty then
      destination.flush
    else
      destination.write chunk
      destination.flush
      loop
  loop

private def writeInput (stdin : IO.FS.Handle) (input : ByteArray) : IO Unit := do
  stdin.write input
  stdin.flush

private def runCandidate (candidate inputPath : System.FilePath)
    (candidateArgs : Array String) : IO UInt32 := do
  let input ← IO.FS.readBinFile inputPath
  let spawned ← IO.Process.spawn {
    cmd := candidate.toString
    args := candidateArgs
    stdin := .piped
    stdout := .piped
    stderr := .piped }
  let (stdin, child) ← spawned.takeStdin
  let stdout ← IO.getStdout
  let stderr ← IO.getStderr
  let stdoutTask ← IO.asTask (copy child.stdout stdout) Task.Priority.dedicated
  let stderrTask ← IO.asTask (copy child.stderr stderr) Task.Priority.dedicated
  let stdinTask ← IO.asTask (writeInput stdin input) Task.Priority.dedicated
  let exitTask ← IO.asTask child.wait Task.Priority.dedicated
  IO.ofExcept stdinTask.get
  let exitCode ← IO.ofExcept exitTask.get
  IO.ofExcept stdoutTask.get
  IO.ofExcept stderrTask.get
  IO.FS.writeFile inputPath (A12Kernel.Process.Bounded.RelayStatus.render exitCode)
  pure 0

def run : List String → IO UInt32
  | candidate :: inputPath :: candidateArgs =>
      runCandidate candidate inputPath candidateArgs.toArray
  | _ =>
      pure 2

end A12Kernel.Process.Relay

def main (args : List String) : IO UInt32 := do
  try
    A12Kernel.Process.Relay.run args
  catch _ =>
    pure 1
