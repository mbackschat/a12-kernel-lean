import A12Kernel.Reference.StrictJson
import Lean.Data.Json

/-! # Qualification artifact identities

Portable, validated names used by qualification packets and returned result records.
This module is pure: it parses and renders identities but performs no filesystem IO.
-/

namespace A12Kernel.Qualification.Artifact

open Lean

private def isLowerHex (character : Char) : Bool :=
  decide ('0' ≤ character && character ≤ '9') ||
    decide ('a' ≤ character && character ≤ 'f')

/-- A lowercase hexadecimal SHA-256 digest. Invalid values cannot be constructed publicly. -/
structure Digest where
  private mk ::
  private raw : String
  deriving Repr, DecidableEq

namespace Digest

/-- Parse exactly 64 lowercase hexadecimal characters. -/
def parse (value : String) : Except String Digest := do
  if value.length != 64 then
    throw "SHA-256 digest must contain exactly 64 characters"
  if !value.toList.all isLowerHex then
    throw "SHA-256 digest must contain only lowercase hexadecimal characters"
  pure ⟨value⟩

def toString (digest : Digest) : String := digest.raw

instance : ToString Digest := ⟨toString⟩

def asJson (digest : Digest) : Json := toJson digest.toString

end Digest

private def isControl (character : Char) : Bool :=
  let code := character.toNat
  decide (code < 0x20) || decide (0x7f ≤ code && code ≤ 0x9f)

/-- A `/`-separated path scoped beneath an artifact root. Invalid values cannot be constructed publicly. -/
structure PortablePath where
  private mk ::
  private raw : String
  deriving Repr, DecidableEq

namespace PortablePath

/-- Maximum UTF-8 byte length of an admitted artifact-root-relative path, including separators. -/
def maxTotalBytes : Nat := 1024

/-- Maximum UTF-8 byte length of one admitted path segment. -/
def maxSegmentBytes : Nat := 255

/-- Maximum number of segments, including the final file name, in one admitted path. -/
def maxSegmentCount : Nat := 64

private def validSegment (segment : String) : Except String Unit := do
  if segment.isEmpty then
    throw "portable path must not contain an empty segment"
  if segment.utf8ByteSize > maxSegmentBytes then
    throw s!"portable path segment exceeds {maxSegmentBytes} UTF-8 bytes"
  if segment == "." || segment == ".." then
    throw s!"portable path contains forbidden segment '{segment}'"
  if segment.startsWith "-" then
    throw s!"portable path segment must not start with '-': '{segment}'"
  if !segment.toList.all fun character =>
      decide (character.toNat < 0x80) &&
        (character.isAlphanum || ['.', '_', '-'].contains character) then
    throw s!"portable path segment contains a non-portable character: '{segment}'"

/-- Parse a portable artifact-root-relative path without platform-specific normalization. -/
def parse (value : String) : Except String PortablePath := do
  if value.isEmpty then
    throw "portable path must not be empty"
  if value.utf8ByteSize > maxTotalBytes then
    throw s!"portable path exceeds {maxTotalBytes} UTF-8 bytes"
  if value.startsWith "/" then
    throw "portable path must be relative"
  if value.contains '\\' then
    throw "portable path must use '/' separators, not backslashes"
  if value.contains ':' then
    throw "portable path must not contain ':'"
  if value.toList.any isControl then
    throw "portable path must not contain control characters"
  let pathSegments := value.splitOn "/"
  if pathSegments.length > maxSegmentCount then
    throw s!"portable path exceeds {maxSegmentCount} segments"
  for segment in pathSegments do
    validSegment segment
  pure ⟨value⟩

def toString (path : PortablePath) : String := path.raw

instance : ToString PortablePath := ⟨toString⟩

def segments (path : PortablePath) : List String := path.raw.splitOn "/"

def asJson (path : PortablePath) : Json := toJson path.toString

private def segmentPrefix : List String → List String → Bool
  | [], _ => true
  | _, [] => false
  | left :: leftRest, right :: rightRest =>
      left == right && segmentPrefix leftRest rightRest

/-- Whether one admitted path names a strict ancestor of another admitted path. -/
def isStrictAncestorOf (ancestor descendant : PortablePath) : Bool :=
  ancestor != descendant && segmentPrefix ancestor.segments descendant.segments

def caseFoldedEquivalent (left right : PortablePath) : Bool :=
  left.toString.toLower == right.toString.toLower

def isCaseFoldedStrictAncestorOf (ancestor descendant : PortablePath) : Bool :=
  !caseFoldedEquivalent ancestor descendant &&
    segmentPrefix (ancestor.segments.map (·.toLower)) (descendant.segments.map (·.toLower))

end PortablePath

inductive PathConflict where
  | duplicate (path : PortablePath)
  | ancestor (ancestor descendant : PortablePath)
  | caseFoldedCollision (left right : PortablePath)
  deriving Repr, DecidableEq

private def conflictWith (path : PortablePath) : List PortablePath → Option PathConflict
  | [] => none
  | candidate :: rest =>
      if path == candidate then
        some (.duplicate path)
      else if path.caseFoldedEquivalent candidate then
        some (.caseFoldedCollision path candidate)
      else if path.isStrictAncestorOf candidate then
        some (.ancestor path candidate)
      else if candidate.isStrictAncestorOf path then
        some (.ancestor candidate path)
      else if path.isCaseFoldedStrictAncestorOf candidate then
        some (.caseFoldedCollision path candidate)
      else if candidate.isCaseFoldedStrictAncestorOf path then
        some (.caseFoldedCollision candidate path)
      else
        conflictWith path rest

/-- Return the first exact duplicate or file/directory collision in list order. -/
def firstPathConflict? : List PortablePath → Option PathConflict
  | [] => none
  | path :: rest => conflictWith path rest <|> firstPathConflict? rest

/-- Reject exact duplicate paths and paths that would require another listed file to be a directory. -/
def validatePathSet (paths : List PortablePath) : Except String Unit :=
  match firstPathConflict? paths with
  | none => pure ()
  | some (.duplicate path) =>
      throw s!"duplicate artifact path '{path}'"
  | some (.ancestor ancestor descendant) =>
      throw s!"artifact path '{ancestor}' collides with descendant '{descendant}'"
  | some (.caseFoldedCollision left right) =>
      throw s!"artifact paths '{left}' and '{right}' collide on a case-insensitive filesystem"

structure FileDigest where
  path : PortablePath
  sha256 : Digest
  deriving Repr, DecidableEq

namespace FileDigest

private def requireObject (json : Json) (context : String) : Except String Unit := do
  let object ← match json.getObj? with
    | .ok object => pure object
    | .error _ => throw s!"{context}: expected an object"
  for (name, _) in object.toList do
    if !["path", "sha256"].contains name then
      throw s!"{context}: unknown member '{name}'"

private def requiredString (json : Json) (name context : String) : Except String String := do
  let value ← match json.getObjVal? name with
    | .ok value => pure value
    | .error _ => throw s!"{context}: missing member '{name}'"
  match value.getStr? with
  | .ok value => pure value
  | .error _ => throw s!"{context}: member '{name}' must be a string"

/-- Parse the closed `{ "path", "sha256" }` object shape. -/
def parseJson (json : Json) (context : String := "file digest") : Except String FileDigest := do
  requireObject json context
  let pathText ← requiredString json "path" context
  let digestText ← requiredString json "sha256" context
  let path ← match PortablePath.parse pathText with
    | .ok path => pure path
    | .error error => throw s!"{context}: member 'path': {error}"
  let sha256 ← match Digest.parse digestText with
    | .ok digest => pure digest
    | .error error => throw s!"{context}: member 'sha256': {error}"
  pure {
    path
    sha256 }

/-- Strict text parser; duplicate JSON members are rejected before object decoding. -/
def parseText (input : String) (context : String := "file digest") : Except String FileDigest := do
  let json ← match A12Kernel.Reference.StrictJson.parse input with
    | .ok json => pure json
    | .error error => throw s!"{context}: invalid strict JSON: {repr error}"
  parseJson json context

def asJson (file : FileDigest) : Json :=
  Json.mkObj [
    ("path", file.path.asJson),
    ("sha256", file.sha256.asJson)]

def render (file : FileDigest) : String := file.asJson.compress

/-- Apply path-set validation to a complete file-digest inventory. -/
def validateInventory (files : List FileDigest) : Except String Unit :=
  validatePathSet (files.map (·.path))

end FileDigest

private def repeatedText (character : Char) (count : Nat) : String :=
  String.ofList (List.replicate count character)

private def validDigestText : String := repeatedText 'a' 64

private def maximumPortablePath : String :=
  String.intercalate "/" [
    repeatedText 'a' 255,
    repeatedText 'b' 255,
    repeatedText 'c' 255,
    repeatedText 'd' 254,
    "e"]

private example : (Digest.parse validDigestText).isOk := by native_decide
private example : (Digest.parse (repeatedText 'A' 64)).isOk = false := by native_decide
private example : (Digest.parse (repeatedText 'a' 63)).isOk = false := by native_decide

private example : (PortablePath.parse "logs/natural.stdout").isOk := by native_decide
private example : (PortablePath.parse "").isOk = false := by native_decide
private example : (PortablePath.parse "/absolute").isOk = false := by native_decide
private example : (PortablePath.parse "../escape").isOk = false := by native_decide
private example : (PortablePath.parse "logs/./output").isOk = false := by native_decide
private example : (PortablePath.parse "logs//output").isOk = false := by native_decide
private example : (PortablePath.parse "logs/output/").isOk = false := by native_decide
private example : (PortablePath.parse "logs\\output").isOk = false := by native_decide
private example : (PortablePath.parse "C:/output").isOk = false := by native_decide
private example : (PortablePath.parse "logs/-output").isOk = false := by native_decide
private example : (PortablePath.parse "logs/new\nline").isOk = false := by native_decide
private example : (PortablePath.parse "logs/space name").isOk = false := by native_decide
private example : (PortablePath.parse "logs/ümlaut").isOk = false := by native_decide
private example : (PortablePath.parse (repeatedText 'a' 255)).isOk := by native_decide
private example : (PortablePath.parse
    ("logs/" ++ repeatedText 'a' 256)).isOk = false := by native_decide
private example : (PortablePath.parse
    (String.intercalate "/" (List.replicate 64 "a"))).isOk := by native_decide
private example : (PortablePath.parse
    (String.intercalate "/" (List.replicate 65 "a"))).isOk = false := by native_decide
private example : maximumPortablePath.utf8ByteSize = PortablePath.maxTotalBytes := by native_decide
private example : (PortablePath.parse maximumPortablePath).isOk := by native_decide
private example : (PortablePath.parse (maximumPortablePath ++ "f")).isOk = false := by native_decide
-- Non-ASCII artifact paths are rejected before filesystem normalization can differ by platform.
private example : (PortablePath.parse
    ("logs/" ++ repeatedText 'é' 128)).isOk = false := by native_decide

private example : (do
    let first ← PortablePath.parse "logs/output"
    let second ← PortablePath.parse "logs/output"
    validatePathSet [first, second]).isOk = false := by native_decide

private example : (do
    let first ← PortablePath.parse "logs"
    let second ← PortablePath.parse "logs/output"
    validatePathSet [first, second]).isOk = false := by native_decide

private example : (do
    let first ← PortablePath.parse "logs/first"
    let second ← PortablePath.parse "logs/second"
    validatePathSet [first, second]).isOk := by native_decide

private example : (do
    let first ← PortablePath.parse "Logs/output"
    let second ← PortablePath.parse "logs/output"
    validatePathSet [first, second]).isOk = false := by native_decide

private example : (do
    let first ← PortablePath.parse "Logs"
    let second ← PortablePath.parse "logs/output"
    validatePathSet [first, second]).isOk = false := by native_decide

private def validFileDigestText : String :=
  "{\"path\":\"logs/output\",\"sha256\":\"" ++ validDigestText ++ "\"}"

private example : (FileDigest.parseText validFileDigestText).isOk := by native_decide
private example : (FileDigest.parseText
    ("{\"path\":\"logs/output\",\"sha256\":\"" ++ validDigestText ++
      "\",\"extra\":true}")).isOk =
    false := by native_decide
private example : (FileDigest.parseText
    ("{\"path\":\"logs/output\",\"path\":\"logs/other\",\"sha256\":\"" ++
      validDigestText ++ "\"}")).isOk =
    false := by native_decide

private example : (do
    let file ← FileDigest.parseText validFileDigestText
    let reparsed ← FileDigest.parseText file.render
    if reparsed == file then pure () else throw "round-trip mismatch").isOk := by native_decide

end A12Kernel.Qualification.Artifact
