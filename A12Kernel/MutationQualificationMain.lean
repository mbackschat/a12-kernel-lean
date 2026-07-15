import A12Kernel.Qualification.SelfTest

/-! # Source-side Rust mutation qualification process -/

open A12Kernel.Qualification

private def run (args : List String) : IO UInt32 := do
  let projectRoot : System.FilePath := "."
  match args with
  | ["--self-test", "--candidate-repo", candidate] =>
      let guards ← SelfTest.run projectRoot candidate
      IO.println s!"mutation qualification self-test: {guards} adversarial guards passed"
      pure 0
  | ["--export", "--candidate-repo", candidate, "--output", output] =>
      let candidateRoot : System.FilePath := candidate
      let packetRoot : System.FilePath := output
      let _ ← RustPacket.exportPacket projectRoot candidateRoot packetRoot
      try
        let index ← Checker.readAndVerifyPacket projectRoot candidateRoot
          (packetRoot / "PACKET.json")
        IO.println s!"mutation qualification packet: {index.mutations.length}/{index.mutations.length} exact mutations exported and verified at '{packetRoot}'"
        pure 0
      catch error =>
        if ← System.FilePath.pathExists packetRoot then IO.FS.removeDirAll packetRoot
        throw error
  | ["--verify-packet", "--candidate-repo", candidate, "--packet", packet] =>
      let index ← Checker.readAndVerifyPacket projectRoot candidate packet
      IO.println s!"mutation qualification packet: {index.payloadFiles.length}/{index.payloadFiles.length} payloads and {index.mutations.length}/{index.mutations.length} mutations verified"
      pure 0
  | ["--check", "--candidate-repo", candidate, "--packet", packet, "--result", result] =>
      let index ← Checker.readAndVerifyPacket projectRoot candidate packet
      Checker.checkResult packet result index
      let candidateRevision ← RustPacket.candidateHead candidate
      IO.println s!"mutation qualification result: accepted a digest-bound, internally consistent isolated-session attestation with {index.mutations.length}/{index.mutations.length} declared mutations; packet identity, command/status records, observer outputs, and restored path-and-byte inventories passed consistency checks against the build-input closure at candidate revision {candidateRevision}"
      pure 0
  | _ => do
      IO.eprintln "checkMutationQualification: expected --self-test --candidate-repo <path>, --export --candidate-repo <path> --output <new-directory>, --verify-packet --candidate-repo <path> --packet <PACKET.json>, or --check --candidate-repo <path> --packet <PACKET.json> --result <RESULT.json>"
      pure 2

def main (args : List String) : IO UInt32 := do
  try
    run args
  catch error =>
    IO.eprintln s!"checkMutationQualification: {error}"
    pure 1
