import A12Kernel.Process.ArtifactTree
import A12Kernel.Reference.StrictJson

/-! # Capture receipt binding

This module decodes the closed `capture-receipt-v1` envelope and binds it to an exact filesystem tree. It establishes transport identity only; packet meaning, cross-artifact relations, qualification policy, and A12 semantics belong to higher layers. Verification assumes a quiescent retained-artifact root: the exact tree is checked before and after file hashing, but this is not an atomic snapshot against a concurrently hostile writer.
-/

namespace A12Kernel.Evidence.Capture.Receipt

open Lean
open A12Kernel.Process.Artifact

structure Artifact where
  file : FileDigest
  role : String
  bytes : Nat
  deriving Repr, DecidableEq

structure Receipt where
  artifacts : List Artifact
  deriving Repr, DecidableEq

structure VerifiedReceipt where
  receipt : Receipt
  receiptSha256 : Digest
  deriving Repr, DecidableEq

private def objectNames (context : String) (json : Json) : Except String (List String) :=
  match json.getObj? with
  | .ok object => pure <| object.toList.map (fun entry => entry.1)
  | .error _ => throw s!"{context} must be an object"

private def hasDuplicate [BEq α] : List α → Bool
  | [] => false
  | value :: rest => rest.contains value || hasDuplicate rest

private def sameInventory (actual expected : List String) : Bool :=
  !hasDuplicate actual && actual.mergeSort == expected.mergeSort

private def requireExactMembers (context : String) (json : Json)
    (expected : List String) : Except String Unit := do
  let actual ← objectNames context json
  if !sameInventory actual expected then
    throw s!"{context} has unknown, missing, or duplicate members"

private def member [FromJson α] (json : Json) (name context : String) : Except String α := do
  let value ← match json.getObjVal? name with
    | .ok value => pure value
    | .error _ => throw s!"{context}: missing member '{name}'"
  match fromJson? value with
  | .ok value => pure value
  | .error error => throw s!"{context}: member '{name}': {error}"

private def Artifact.fromJson (index : Nat) (json : Json) : Except String Artifact := do
  let context := s!"capture receipt artifact {index}"
  requireExactMembers context json ["path", "role", "bytes", "sha256"]
  let pathText : String ← member json "path" context
  let digestText : String ← member json "sha256" context
  let path ← match PortablePath.parse pathText with
    | .ok path => pure path
    | .error error => throw s!"{context}: member 'path': {error}"
  let sha256 ← match Digest.parse digestText with
    | .ok digest => pure digest
    | .error error => throw s!"{context}: member 'sha256': {error}"
  let role : String ← member json "role" context
  if role.isEmpty then
    throw s!"{context}: member 'role' must not be empty"
  let bytes : Nat ← member json "bytes" context
  if bytes > A12Kernel.Process.ArtifactTree.maxArtifactBytes then
    throw s!"{context}: declared byte count exceeds the {A12Kernel.Process.ArtifactTree.maxArtifactBytes}-byte artifact limit"
  pure {
    file := { path, sha256 }
    role
    bytes }

def parseJson (json : Json) : Except String Receipt := do
  requireExactMembers "capture receipt" json ["schema", "artifacts"]
  let schema : String ← member json "schema" "capture receipt"
  if schema != "capture-receipt-v1" then
    throw s!"capture receipt: unsupported schema '{schema}'"
  let artifactsJson : List Json ← member json "artifacts" "capture receipt"
  let artifacts ← artifactsJson.zipIdx.mapM fun (artifact, index) =>
    Artifact.fromJson index artifact
  if artifacts.isEmpty then
    throw "capture receipt: artifact inventory must not be empty"
  let files := artifacts.map (·.file)
  FileDigest.validateInventory files
  if files.any (·.path.toString == "RECEIPT.json") then
    throw "capture receipt: RECEIPT.json must not inventory itself"
  let paths := files.map (·.path.toString)
  if paths != paths.mergeSort then
    throw "capture receipt: artifact inventory must be sorted by portable path"
  pure { artifacts }

def parseText (input : String) : Except String Receipt := do
  let json ← match A12Kernel.Reference.StrictJson.parse input with
    | .ok json => pure json
    | .error error => throw s!"capture receipt: invalid strict JSON: {repr error}"
  parseJson json

private def fail (message : String) : IO α :=
  throw (IO.userError message)

def readAndVerify (root : System.FilePath)
    (expectedReceiptSha256 : Digest) : IO VerifiedReceipt := do
  let receiptPath := root / "RECEIPT.json"
  let input ← A12Kernel.Process.ArtifactTree.readBoundedText receiptPath
    "capture receipt"
  let actualReceiptSha256 ← A12Kernel.Process.Sha256.file receiptPath
  if actualReceiptSha256 != expectedReceiptSha256.toString then
    fail s!"capture receipt digest mismatch: expected {expectedReceiptSha256}, found {actualReceiptSha256}"
  let receipt ← match parseText input with
    | .ok receipt => pure receipt
    | .error error => fail error
  let receiptPath ← match PortablePath.parse "RECEIPT.json" with
    | .ok path => pure path
    | .error error => fail s!"internal receipt path is invalid: {error}"
  A12Kernel.Process.ArtifactTree.verifyExactTree root
    (receiptPath :: receipt.artifacts.map (·.file.path)) "capture receipt"
  for artifact in receipt.artifacts do
    A12Kernel.Process.ArtifactTree.verifyFile root artifact.file artifact.bytes
      s!"capture artifact role '{artifact.role}'"
  A12Kernel.Process.ArtifactTree.verifyExactTree root
    (receiptPath :: receipt.artifacts.map (·.file.path)) "capture receipt"
  pure { receipt, receiptSha256 := expectedReceiptSha256 }

end A12Kernel.Evidence.Capture.Receipt
