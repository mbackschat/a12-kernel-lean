import A12Kernel.Evidence.Capture.Receipt

/-! # Capture receipt IO locks

These tests bind all three retained direct-cascade `capture-receipt-v1` trees and the separate scenario-mutation process receipt, then exercise the shared boundary through a small copied qualification fixture and disposable mutations. They belong to the evidence driver because they perform filesystem IO and establish transport closure, not A12 semantics.
-/

namespace A12Kernel.Evidence.Capture.ReceiptTest

open A12Kernel.Process.Artifact

private def orThrow (context : String) : Except String α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{context}: {error}")

private def expectFailure (context expectedMessage : String) (action : IO α) : IO Unit := do
  let failure? ← try
    let _ ← action
    pure none
  catch error =>
    pure (some (toString error))
  match failure? with
  | none => throw (IO.userError s!"capture receipt mutation was accepted: {context}")
  | some message =>
      if !message.contains expectedMessage then
        throw (IO.userError
          s!"capture receipt mutation '{context}' failed at the wrong guard; expected '{expectedMessage}', found '{message}'")

private def expectParseFailure (context expectedMessage input : String) : IO Unit :=
  match A12Kernel.Evidence.Capture.Receipt.parseText input with
  | .ok _ => throw (IO.userError s!"capture receipt text mutation was accepted: {context}")
  | .error error =>
      if !error.contains expectedMessage then
        throw (IO.userError
          s!"capture receipt text mutation '{context}' failed at the wrong guard; expected '{expectedMessage}', found '{error}'")
      else
        pure ()

private def copyFile (source target : System.FilePath) : IO Unit := do
  let bytes ← IO.FS.readBinFile source
  IO.FS.writeBinFile target bytes

private def copyQualificationFixture (source target : System.FilePath) : IO Unit := do
  IO.FS.createDirAll target
  copyFile (source / "PROFILE.json") (target / "PROFILE.json")
  copyFile (source / "REPORT.json") (target / "REPORT.json")
  copyFile (source / "RECEIPT.json") (target / "RECEIPT.json")

private def checkGlobalTreeOrder : IO Unit :=
  IO.FS.withTempDir fun temporary => do
    IO.FS.createDirAll (temporary / "a")
    IO.FS.writeFile (temporary / "a/inside.json") "{}"
    IO.FS.writeFile (temporary / "a.json") "{}"
    let actual := (← A12Kernel.Process.ArtifactTree.collectFiles temporary).map
      (·.toString)
    let expected := ["a.json", "a/inside.json"]
    if actual != expected then
      throw (IO.userError
        s!"artifact tree is not globally sorted; expected {repr expected}, found {repr actual}")

private def checkScenarioMutationReceipt (captureRoot : System.FilePath)
    (expectedDigest : Digest) : IO Unit := do
  let path := captureRoot / "process/scenario-mutation-receipt.json"
  let input ← A12Kernel.Process.ArtifactTree.readBoundedText path
    "scenario-mutation process receipt"
  let actualDigest ← A12Kernel.Process.Sha256.file path
  if actualDigest != expectedDigest.toString then
    throw (IO.userError
      s!"scenario-mutation process receipt digest mismatch: expected {expectedDigest}, found {actualDigest}")
  let json ← match A12Kernel.Reference.StrictJson.parse input with
    | .ok json => pure json
    | .error error => throw (IO.userError
        s!"scenario-mutation process receipt is not strict JSON: {repr error}")
  let schemaJson ← match json.getObjVal? "schema" with
    | .ok schema => pure schema
    | .error error => throw (IO.userError
        s!"scenario-mutation process receipt has no schema: {error}")
  let schema ← match schemaJson.getStr? with
    | .ok schema => pure schema
    | .error error => throw (IO.userError
        s!"scenario-mutation process receipt schema is not a string: {error}")
  if schema != "capture-scenario-mutation-receipt-v2" then
    throw (IO.userError
      s!"scenario-mutation process receipt has unsupported schema '{schema}'")

private def createSymlink (target link : System.FilePath) : IO Unit := do
  let output ← IO.Process.output {
    cmd := "ln"
    args := #["-s", target.toString, link.toString] }
  if output.exitCode != 0 then
    throw (IO.userError
      s!"capture receipt test could not create symlink: {output.stderr.trimAscii.toString}")

def check (captureRoot : System.FilePath) : IO Unit := do
  let packetDigest ← orThrow "packet receipt digest" <|
    Digest.parse "7e38744283cf17f7f57fe0bce342084a8e2896fb99aa60c2a9f4fb52e185dc17"
  let packetDiffDigest ← orThrow "packet-diff receipt digest" <|
    Digest.parse "b868d6fb57c38dd1b01edf56e58b507567c9c1a17265bcd692b822e97a4d0ce8"
  let qualificationDigest ← orThrow "qualification receipt digest" <|
    Digest.parse "f581d82d7eb04929b38d4663bbb48a28f09c7399273cd5974cd59e739eca5d64"
  let wrongDigest ← orThrow "wrong receipt digest" <|
    Digest.parse "0000000000000000000000000000000000000000000000000000000000000000"
  let scenarioMutationDigest ← orThrow "scenario-mutation receipt digest" <|
    Digest.parse "1ecff441da99528c798eef57a7152da0f7814de481dd4a9654b1f3eb472718c3"
  let _ ← A12Kernel.Evidence.Capture.Receipt.readAndVerify
    (captureRoot / "packet") packetDigest
  let _ ← A12Kernel.Evidence.Capture.Receipt.readAndVerify
    (captureRoot / "packet-diff") packetDiffDigest
  let source := captureRoot / "qualification"
  let _ ← A12Kernel.Evidence.Capture.Receipt.readAndVerify source qualificationDigest
  checkScenarioMutationReceipt captureRoot scenarioMutationDigest
  expectFailure "the out-of-band receipt digest" "capture receipt digest mismatch" <|
    A12Kernel.Evidence.Capture.Receipt.readAndVerify source wrongDigest
  checkGlobalTreeOrder
  let zeros := String.ofList (List.replicate 64 '0')
  expectParseFailure "an artifact larger than the retained-artifact limit"
      "declared byte count exceeds" <|
    "{\"schema\":\"capture-receipt-v1\",\"artifacts\":[{\"path\":\"large.json\"," ++
      "\"role\":\"payload\",\"bytes\":16777217,\"sha256\":\"" ++ zeros ++ "\"}]}"
  IO.FS.withTempDir fun temporary => do
    let fixture := temporary / "qualification"
    copyQualificationFixture source fixture
    let _ ← A12Kernel.Evidence.Capture.Receipt.readAndVerify fixture qualificationDigest
    let reportPath := fixture / "REPORT.json"
    let report ← IO.FS.readFile reportPath
    IO.FS.writeFile reportPath ("[" ++ report.drop 1)
    expectFailure "same-size payload digest drift" "digest mismatch" <|
      A12Kernel.Evidence.Capture.Receipt.readAndVerify fixture qualificationDigest
    IO.FS.writeFile reportPath report
    IO.FS.writeFile reportPath (report ++ "\n")
    expectFailure "payload byte-count drift" "byte count mismatch" <|
      A12Kernel.Evidence.Capture.Receipt.readAndVerify fixture qualificationDigest
    IO.FS.writeFile reportPath report
    IO.FS.writeFile (fixture / "ORPHAN.json") "{}"
    expectFailure "an unlisted artifact" "file tree is not exact" <|
      A12Kernel.Evidence.Capture.Receipt.readAndVerify fixture qualificationDigest
    IO.FS.removeFile (fixture / "ORPHAN.json")
    let symlinkPath := fixture / "ALIAS.json"
    createSymlink reportPath symlinkPath
    expectFailure "a symlink artifact" "contains symlink" <|
      A12Kernel.Evidence.Capture.Receipt.readAndVerify fixture qualificationDigest
    IO.FS.removeFile symlinkPath
    IO.FS.removeFile reportPath
    expectFailure "a listed artifact is missing" "file tree is not exact" <|
      A12Kernel.Evidence.Capture.Receipt.readAndVerify fixture qualificationDigest

end A12Kernel.Evidence.Capture.ReceiptTest
