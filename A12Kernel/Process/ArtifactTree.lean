import A12Kernel.Process.Artifact
import A12Kernel.Process.Sha256

/-! # Closed artifact-tree verification

This IO-only module owns the reusable filesystem mechanism for bounded, symlink-free artifact roots. It deliberately knows nothing about capture packets or mutation qualification; callers supply the expected portable paths and file identities.
-/

namespace A12Kernel.Process.ArtifactTree

open A12Kernel.Process.Artifact

def maxJsonBytes : Nat := 4 * 1024 * 1024

def maxArtifactBytes : Nat := 16 * 1024 * 1024

def maxTreeFiles : Nat := 512

def maxTreeDepth : Nat := 16

private def fail (message : String) : IO α :=
  throw (IO.userError message)

def requireRegularFile (path : System.FilePath) (label : String) : IO Unit := do
  let metadata ← path.symlinkMetadata
  if metadata.type != .file then
    fail s!"{label} '{path}' is not a regular non-symlink file"

def requireBoundedRegularFile (path : System.FilePath) (label : String)
    (limit : Nat := maxArtifactBytes) : IO Unit := do
  requireRegularFile path label
  let metadata ← path.symlinkMetadata
  if metadata.byteSize > UInt64.ofNat limit then
    fail s!"{label} exceeds the {limit}-byte limit"

def readBoundedText (path : System.FilePath) (label : String)
    (limit : Nat := maxJsonBytes) : IO String := do
  requireBoundedRegularFile path label limit
  IO.FS.readFile path

private partial def collectFilesFrom (current : System.FilePath)
    (relativePrefix : String := "") (depth : Nat := 0)
    (ignoredRootDirectory? : Option String := none) : IO (List PortablePath) := do
  if depth > maxTreeDepth then
    fail s!"artifact tree exceeds depth {maxTreeDepth} at '{relativePrefix}'"
  let entries := (← current.readDir).toList.mergeSort fun left right =>
    left.fileName ≤ right.fileName
  let mut files : List PortablePath := []
  for entry in entries do
    let relative := if relativePrefix.isEmpty then entry.fileName
      else s!"{relativePrefix}/{entry.fileName}"
    let portable ← match PortablePath.parse relative with
      | .ok path => pure path
      | .error error => fail s!"unsafe artifact path '{relative}': {error}"
    let metadata ← entry.path.symlinkMetadata
    match metadata.type with
    | .file => files := files ++ [portable]
    | .dir =>
        if depth == 0 && ignoredRootDirectory? == some entry.fileName then
          pure ()
        else
          let nested ← collectFilesFrom entry.path relative (depth + 1)
            ignoredRootDirectory?
          if nested.isEmpty then
            fail s!"artifact tree contains empty directory '{relative}'"
          files := files ++ nested
    | .symlink => fail s!"artifact tree contains symlink '{relative}'"
    | .other => fail s!"artifact tree contains non-regular path '{relative}'"
  pure files

def collectFiles (root : System.FilePath)
    (ignoredRootDirectory? : Option String := none) : IO (List PortablePath) := do
  let metadata ← root.symlinkMetadata
  if metadata.type != .dir then
    fail s!"artifact root '{root}' is not a regular directory"
  let files ← collectFilesFrom root "" 0 ignoredRootDirectory?
  if files.length > maxTreeFiles then
    fail s!"artifact tree contains more than {maxTreeFiles} files"
  match validatePathSet files with
  | .error error => fail s!"artifact tree contains conflicting paths: {error}"
  | .ok () =>
      pure <| files.mergeSort fun left right =>
        left.toString ≤ right.toString

def verifyExactTree (root : System.FilePath) (expected : List PortablePath)
    (label : String) : IO Unit := do
  match validatePathSet expected with
  | .error error => fail s!"{label} contains an invalid expected inventory: {error}"
  | .ok () => pure ()
  let actual := (← collectFiles root).map (·.toString)
  let expected := expected.map (·.toString) |>.mergeSort
  if actual != expected then
    let missing := expected.filter fun path => !actual.contains path
    let extra := actual.filter fun path => !expected.contains path
    fail s!"{label} file tree is not exact; missing={repr missing}, extra={repr extra}"

def verifyExactTreeStrings (root : System.FilePath) (expected : List String)
    (label : String) : IO Unit := do
  let paths ← expected.mapM fun value =>
    match PortablePath.parse value with
    | .ok path => pure path
    | .error error => fail s!"{label} contains unsafe expected path '{value}': {error}"
  match validatePathSet paths with
  | .ok () => verifyExactTree root paths label
  | .error error => fail s!"{label} contains an invalid expected inventory: {error}"

def verifyDigest (root : System.FilePath) (file : FileDigest)
    (label : String) : IO Unit := do
  let path := root / file.path.toString
  requireBoundedRegularFile path label
  let actual ← A12Kernel.Process.Sha256.file path
  if actual != file.sha256.toString then
    fail s!"{label} digest mismatch for '{file.path}': expected {file.sha256}, found {actual}"

def verifyFile (root : System.FilePath) (file : FileDigest) (bytes : Nat)
    (label : String) : IO Unit := do
  if bytes > maxArtifactBytes then
    fail s!"{label} declared byte count exceeds the {maxArtifactBytes}-byte artifact limit"
  let path := root / file.path.toString
  requireBoundedRegularFile path label
  let metadata ← path.symlinkMetadata
  if metadata.byteSize != UInt64.ofNat bytes then
    fail s!"{label} byte count mismatch for '{file.path}': expected {bytes}, found {metadata.byteSize}"
  verifyDigest root file label

end A12Kernel.Process.ArtifactTree
