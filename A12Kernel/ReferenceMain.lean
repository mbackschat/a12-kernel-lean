import A12Kernel.Reference.Evaluator

/-! # A12Kernel.ReferenceMain — normalized JSON reference process -/

namespace A12Kernel.Reference.Cli

private def writeStdout (content : String) : IO Unit := do
  let stdout ← IO.getStdout
  stdout.putStr content
  stdout.flush

private def writeStderr (content : String) : IO Unit := do
  let stderr ← IO.getStderr
  stderr.putStr content
  stderr.flush

private partial def readRequestBytes (stdin : IO.FS.Stream) : IO ByteArray := do
  let rec loop (accumulator : ByteArray) : IO ByteArray := do
    if accumulator.size > Support.maxInputBytes then
      pure accumulator
    else
      let remaining := Support.maxInputBytes + 1 - accumulator.size
      let chunk ← stdin.read (USize.ofNat (min remaining 65536))
      if chunk.isEmpty then
        pure accumulator
      else
        loop (accumulator ++ chunk)
  loop ByteArray.empty

private def runRequest : IO UInt32 := do
  let stdin ← IO.getStdin
  let input ← readRequestBytes stdin
  match evaluateBytes input with
  | .ok response =>
      writeStdout response.render
      pure 0
  | .error .incoherentCore =>
      writeStderr "a12-kernel-reference: internal checked-lowering failure\n"
      pure 1

private def run (args : List String) : IO UInt32 :=
  match args with
  | [] => runRequest
  | ["--manifest"] => do
      writeStdout (Support.supportManifest.compress ++ "\n")
      pure 0
  | _ => do
      writeStderr "a12-kernel-reference: expected no arguments or --manifest\n"
      pure 2

end A12Kernel.Reference.Cli

def main (args : List String) : IO UInt32 := do
  try
    A12Kernel.Reference.Cli.run args
  catch error =>
    let stderr ← IO.getStderr
    stderr.putStr s!"a12-kernel-reference: IO failure: {error}\n"
    stderr.flush
    pure 1
