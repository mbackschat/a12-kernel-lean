import A12Kernel.Evidence.ObservationBundle

/-! # Compact observation-bundle contract locks

These schema tests use synthetic JSON only. They do not constitute kernel evidence.
-/

namespace A12Kernel.Evidence.ObservationBundleTest

open Lean
open A12Kernel.Evidence.ObservationBundle

private def digest := "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
private def revision := "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"
private def repeated (count : Nat) (character : Char := 'a') : String :=
  String.ofList (List.replicate count character)
private def maximumPortablePath : String :=
  String.intercalate "/" [
    repeated 255 'a',
    repeated 255 'b',
    repeated 255 'c',
    repeated 254 'd',
    "e"]

private def file (path : String) (sha256 : String := digest) : Json :=
  Json.mkObj [("path", toJson path), ("sha256", toJson sha256)]

private def qualification (policyId : String := "kernel-route-confirmed-v1") : Json :=
  Json.mkObj [("policyId", toJson policyId), ("receipt", file "qualification/RECEIPT.json")]

private def source (revisionText : String := revision) (qualified : Bool := true)
    (producer : String := "a12-dmkits") : Json :=
  Json.mkObj [
    ("producer", toJson producer),
    ("revision", toJson revisionText),
    ("rawCapture", file "packet/RECEIPT.json"),
    ("qualification", if qualified then qualification else Json.null)]

private def caseJson (id : String)
    (input : Json := Json.mkObj [("side", toJson "input")])
    (observed : Json := Json.mkObj [("side", toJson "observed")]) : Json :=
  Json.mkObj [
    ("id", toJson id),
    ("input", input),
    ("observed", observed)]

private def family (id := "family-v1") (projectionId := "projection-v1")
    (projectionVersion := 1) (sourceJson := source) (cases := [caseJson "case-1"]) : Json :=
  Json.mkObj [
    ("id", toJson id),
    ("projectionId", toJson projectionId),
    ("projectionVersion", toJson projectionVersion),
    ("source", sourceJson),
    ("cases", toJson cases)]

private def bundle (families := [family]) : Json :=
  Json.mkObj [
    ("schemaVersion", toJson 1),
    ("kernelVersion", toJson "30.8.1"),
    ("families", toJson families)]

private def parse (json : Json) : Except String Bundle :=
  Bundle.parseText json.compress

private def rejects (needle : String) (result : Except String α) : Bool :=
  match result with
  | .error message => message.contains needle
  | .ok _ => false

example : (parse bundle).isOk = true := by native_decide
example : (parse (bundle [family (sourceJson := source (qualified := false))])).isOk = true := by native_decide
example : (parse (bundle [family, family (id := "other")])).isOk = true := by native_decide
example : (parse (bundle [family, family (id := "family-v1") (projectionId := "other")])).isOk = true := by native_decide
example : (parse (bundle [family, family (projectionVersion := 2)])).isOk = true := by native_decide
example : (parse (bundle [family (sourceJson := source.setObjVal! "rawCapture"
    (file maximumPortablePath))])).isOk = true := by native_decide
example : (parse (bundle [family (sourceJson := source.setObjVal! "rawCapture"
    (file (String.intercalate "/" (List.replicate 64 "a"))))])).isOk = true := by native_decide

example : (match parse bundle with
    | .ok parsed =>
        parsed.families.head?.bind (·.cases.head?) |>.any fun case =>
          case.input == Json.mkObj [("side", toJson "input")] &&
          case.observed == Json.mkObj [("side", toJson "observed")]
    | .error _ => false) = true := by native_decide

private def rejectedShapes : List Bool := [
  rejects "unknown member" <| parse (bundle.setObjVal! "extra" Json.null),
  rejects "schema version" <| parse (bundle.setObjVal! "schemaVersion" (toJson 2)),
  rejects "kernel version" <| parse (bundle.setObjVal! "kernelVersion" (toJson "other")),
  rejects "at least one family" <| parse (bundle []),
  rejects "family id" <| parse (bundle [family (id := "")]),
  rejects "projection id" <| parse (bundle [family (projectionId := "")]),
  rejects "positive" <| parse (bundle [family (projectionVersion := 0)]),
  rejects "family/projection/version identity" <| parse (bundle [family, family]),
  rejects "family/projection/version identity" <| parse (bundle [family, family (id := "middle"), family]),
  rejects "at least one case" <| parse (bundle [family (cases := [])]),
  rejects "case id" <| parse (bundle [family (cases := [caseJson ""])]),
  rejects "duplicate case id" <| parse (bundle [family (cases := [caseJson "same", caseJson "same"])]),
  rejects "observation family: unknown member" <| parse (bundle [family.setObjVal! "extra" Json.null]),
  rejects "observation family 'family-v1' case: unknown member" <| parse (bundle [family (cases := [caseJson "case-1" |>.setObjVal! "extra" Json.null])]),
  rejects "source: unknown member" <| parse (bundle [family (sourceJson := source.setObjVal! "extra" Json.null)]),
  rejects "source qualification: unknown member" <| parse (bundle [family (sourceJson := source.setObjVal! "qualification" (qualification.setObjVal! "extra" Json.null))]),
  rejects "source producer" <| parse (bundle [family (sourceJson := source (producer := ""))]),
  rejects "Git revision" <| parse (bundle [family (sourceJson := source revision.toUpper)]),
  rejects "must be relative" <| parse (bundle [family (sourceJson := source.setObjVal! "rawCapture" (file "/absolute"))]),
  rejects "forbidden segment" <| parse (bundle [family (sourceJson := source.setObjVal! "rawCapture" (file "../escape"))]),
  rejects "empty segment" <| parse (bundle [family (sourceJson := source.setObjVal! "rawCapture" (file "packet//RECEIPT.json"))]),
  rejects "separators" <| parse (bundle [family (sourceJson := source.setObjVal! "rawCapture" (file "packet\\RECEIPT.json"))]),
  rejects "segment exceeds" <| parse (bundle [family (sourceJson := source.setObjVal! "rawCapture" (file (repeated 256)))]),
  rejects "segments" <| parse (bundle [family (sourceJson := source.setObjVal! "rawCapture"
    (file (String.intercalate "/" (List.replicate 65 "a"))))]),
  rejects "exceeds 1024" <| parse (bundle [family (sourceJson := source.setObjVal! "rawCapture"
    (file (maximumPortablePath ++ "f")))]),
  rejects "must not start" <| parse (bundle [family (sourceJson := source.setObjVal! "rawCapture"
    (file "packet/-receipt.json"))]),
  rejects "non-portable character" <| parse (bundle [family (sourceJson := source.setObjVal! "rawCapture"
    (file "packet/receipt name.json"))]),
  rejects "lowercase hexadecimal" <| parse (bundle [family (sourceJson := source.setObjVal! "rawCapture" (file "packet/RECEIPT.json" digest.toUpper))]),
  rejects "64 characters" <| parse (bundle [family (sourceJson := source.setObjVal! "rawCapture" (file "packet/RECEIPT.json" (repeated 63)))]),
  rejects "raw capture: unknown member" <| parse (bundle [family (sourceJson := source.setObjVal! "rawCapture"
    ((file "packet/RECEIPT.json").setObjVal! "extra" Json.null))]),
  rejects "policy id" <| parse (bundle [family (sourceJson := source.setObjVal! "qualification" (qualification ""))]),
  rejects "qualification receipt" <| parse (bundle [family (sourceJson := source.setObjVal! "qualification" (qualification.setObjVal! "receipt" (file "/absolute")))]),
  rejects "missing member 'qualification'" <| parse (bundle [family (sourceJson := Json.mkObj [
    ("producer", toJson "a12-dmkits"), ("revision", toJson revision),
    ("rawCapture", file "packet/RECEIPT.json")])])]

example : rejectedShapes.all id = true := by native_decide

private def opaqueValues := bundle [family (cases := [
  caseJson "opaque" (toJson (-1 : Int)) (Json.arr #[Json.null, toJson true])])]

example : (match parse opaqueValues with
    | .ok parsed =>
        parsed.families.head?.bind (·.cases.head?) |>.any fun case =>
          case.input == toJson (-1 : Int) &&
          case.observed == Json.arr #[Json.null, toJson true]
    | .error _ => false) = true := by native_decide

private def duplicatePayload : String :=
  bundle.compress.replace "\"input\":{\"side\":\"input\"}" "\"input\":{\"side\":\"input\",\"side\":\"other\"}"

private def oversized : String :=
  String.ofList (List.replicate (maxBytes + 1) ' ')

example : rejects "duplicateMember" (Bundle.parseText duplicatePayload) = true := by native_decide
example : rejects "byte limit" (Bundle.parseText oversized) = true := by native_decide

private def expectLoadFailure (path : System.FilePath) (fragment : String) : IO Unit := do
  let message? ← try
    let _ ← Bundle.load path
    pure none
  catch error =>
    pure (some (toString error))
  match message? with
  | none => throw (IO.userError s!"observation-bundle loader accepted {path}")
  | some message =>
      if !message.contains fragment then
        throw (IO.userError s!"observation-bundle loader failed through {repr message}, expected {repr fragment}")

def checkIo : IO Unit :=
  IO.FS.withTempDir fun temporary => do
    let regular := temporary / "bundle.json"
    IO.FS.writeFile regular bundle.compress
    let loaded ← Bundle.load regular
    if loaded.families.length != 1 then
      throw (IO.userError "observation-bundle loader changed a valid bundle")

    let directory := temporary / "directory.json"
    IO.FS.createDirAll directory
    expectLoadFailure directory "not a regular non-symlink file"

    let symlink := temporary / "alias.json"
    discard <| IO.Process.run {
      cmd := "ln"
      args := #["-s", regular.toString, symlink.toString] }
    expectLoadFailure symlink "not a regular non-symlink file"

    let tooLarge := temporary / "too-large.json"
    IO.FS.writeFile tooLarge (repeated (maxBytes + 1) ' ')
    expectLoadFailure tooLarge "byte limit"

end A12Kernel.Evidence.ObservationBundleTest
