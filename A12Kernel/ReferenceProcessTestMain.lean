import Lake
import Lean.Data.Json

/-! # A12Kernel.ReferenceProcessTestMain — black-box reference CLI gate -/

open Lean

private structure Fixture where
  request : System.FilePath
  response : System.FilePath

private def fixtures : List Fixture := [
  { request := "examples/reference-cli/empty-number-equals-zero.request.json",
    response := "examples/reference-cli/empty-number-equals-zero.response.json" },
  { request := "examples/reference-cli/empty-boolean-equals-true.request.json",
    response := "examples/reference-cli/empty-boolean-equals-true.response.json" },
  { request := "examples/reference-cli/empty-confirm-not-equal-true.request.json",
    response := "examples/reference-cli/empty-confirm-not-equal-true.response.json" },
  { request := "examples/reference-cli/present-number-equals-literal.request.json",
    response := "examples/reference-cli/present-number-equals-literal.response.json" },
  { request := "examples/reference-cli/empty-row-gate.request.json",
    response := "examples/reference-cli/empty-row-gate.response.json" },
  { request := "examples/reference-cli/malformed-number.request.json",
    response := "examples/reference-cli/malformed-number.response.json" },
  { request := "examples/reference-cli/boolean-confirm-composition.request.json",
    response := "examples/reference-cli/boolean-confirm-composition.response.json" },
  { request := "examples/reference-cli/unsupported-ordering.request.json",
    response := "examples/reference-cli/unsupported-ordering.response.json" },
  { request := "examples/reference-cli/illegal-confirm-false.request.json",
    response := "examples/reference-cli/illegal-confirm-false.response.json" },
  { request := "examples/reference-cli/unsupported-version.request.json",
    response := "examples/reference-cli/unsupported-version.response.json" },
  { request := "examples/reference-cli/malformed-json.input",
    response := "examples/reference-cli/malformed-json.response.json" }
]

private def fail (message : String) : IO α :=
  throw (IO.userError message)

private def referenceExecutable : IO System.FilePath := do
  let directory ← IO.appDir
  pure ((directory / "a12-kernel-reference").addExtension System.FilePath.exeExtension)

private def invoke (input : String) (args : Array String := #[]) : IO IO.Process.Output := do
  let executable ← referenceExecutable
  IO.Process.output { cmd := executable.toString, args } (some input)

private def invokeBytes (input : ByteArray) (args : Array String := #[]) :
    IO IO.Process.Output := do
  let executable ← referenceExecutable
  let child ← do
    let child ← IO.Process.spawn {
      cmd := executable.toString
      args
      stdin := .piped
      stdout := .piped
      stderr := .piped }
    let (stdin, child) ← child.takeStdin
    stdin.write input
    stdin.flush
    pure child
  let stdout ← IO.asTask child.stdout.readToEnd Task.Priority.dedicated
  let stderr ← child.stderr.readToEnd
  let exitCode ← child.wait
  pure { exitCode, stdout := ← IO.ofExcept stdout.get, stderr }

private def canonicalFile (path : System.FilePath) : IO String := do
  let content ← IO.FS.readFile path
  match Json.parse content with
  | .ok json => pure (json.compress ++ "\n")
  | .error error => fail s!"invalid expected JSON fixture '{path}': {error}"

private def expectedDiagnostic (category code location : String)
    (details : Json := Json.mkObj []) : String :=
  (Json.mkObj [
    ("protocolVersion", toJson 1),
    ("kernelBehaviorVersion", toJson "30.8.1"),
    ("outcome", toJson "error"),
    ("diagnostic", Json.mkObj [
      ("category", toJson category),
      ("code", toJson code),
      ("at", toJson location),
      ("details", details)])]).compress ++ "\n"

private def replaceRequired (input before after : String) : IO String := do
  let replaced := input.replace before after
  if replaced == input then fail s!"test setup could not find {repr before}"
  pure replaced

private def readJsonFile (path : System.FilePath) : IO Json := do
  let input ← IO.FS.readFile path
  match Json.parse input with
  | .ok json => pure json
  | .error error => fail s!"invalid JSON fixture '{path}': {error}"

private def objectMember (json : Json) (name : String) : IO Json :=
  match json.getObjVal? name with
  | .ok value => pure value
  | .error error => fail s!"test setup member '{name}': {error}"

private def arrayValue (json : Json) : IO (Array Json) :=
  match json.getArr? with
  | .ok values => pure values
  | .error error => fail s!"test setup expected array: {error}"

private def firstValue (values : Array Json) : IO Json :=
  match values[0]? with
  | some value => pure value
  | none => fail "test setup expected a non-empty array"

private def checkOutput (label : String) (output : IO.Process.Output)
    (expectedStdout : String) (expectedExit : UInt32 := 0)
    (expectedStderr : String := "") : IO Unit := do
  if output.exitCode != expectedExit then
    fail s!"{label}: exit {output.exitCode}, expected {expectedExit}"
  if output.stdout != expectedStdout then
    fail s!"{label}: stdout {repr output.stdout}, expected {repr expectedStdout}"
  if output.stderr != expectedStderr then
    fail s!"{label}: stderr {repr output.stderr}, expected {repr expectedStderr}"

private def checkFixture (fixture : Fixture) : IO Unit := do
  let input ← IO.FS.readFile fixture.request
  let expected ← canonicalFile fixture.response
  checkOutput fixture.request.toString (← invoke input) expected

private def checkDeterminism : IO Unit := do
  let requestPath : System.FilePath :=
    "examples/reference-cli/empty-number-equals-zero.request.json"
  let input ← IO.FS.readFile requestPath
  let parsed ← match Json.parse input with
    | .ok json => pure json
    | .error error => fail s!"determinism fixture is invalid: {error}"
  let compactReordered := parsed.compress
  let expected ← canonicalFile
    "examples/reference-cli/empty-number-equals-zero.response.json"
  let original ← invoke input
  let compact ← invoke compactReordered
  let repeated ← invoke input
  checkOutput "determinism/original" original expected
  checkOutput "determinism/reordered" compact expected
  checkOutput "determinism/repeated" repeated expected
  if original.stdout != compact.stdout || original.stdout != repeated.stdout then
    fail "equivalent or repeated requests produced different response bytes"

private def checkDuplicateMember : IO Unit := do
  let input := "{\"protocolVersion\":1,\"protocolVersion\":2}"
  let expected :=
    "{\"diagnostic\":{\"at\":\"$\",\"category\":\"input\",\"code\":\"duplicateMember\",\"details\":{\"member\":\"protocolVersion\"}},\"kernelBehaviorVersion\":\"30.8.1\",\"outcome\":\"error\",\"protocolVersion\":1}\n"
  checkOutput "duplicate member" (← invoke input) expected

private def checkEmptyInput : IO Unit := do
  let expected ← canonicalFile "examples/reference-cli/malformed-json.response.json"
  checkOutput "empty input" (← invoke "") expected

private def checkUnknownMember : IO Unit := do
  let input := "{\"unexpected\":true}"
  let expected :=
    "{\"diagnostic\":{\"at\":\"$.unexpected\",\"category\":\"input\",\"code\":\"invalidShape\",\"details\":{\"member\":\"unexpected\",\"reason\":\"unknownMember\"}},\"kernelBehaviorVersion\":\"30.8.1\",\"outcome\":\"error\",\"protocolVersion\":1}\n"
  checkOutput "unknown member" (← invoke input) expected

private def checkNonCanonicalJsonNumber : IO Unit := do
  let input := "{\"protocolVersion\":1e1025}"
  checkOutput "non-canonical JSON number" (← invoke input)
    (expectedDiagnostic "input" "invalidJsonNumber" "$")

private def checkJsonNestingLimit : IO Unit := do
  let input := String.ofList (List.replicate 129 '[') ++ "0" ++
    String.ofList (List.replicate 129 ']')
  let details := Json.mkObj [("limit", toJson "jsonNesting"), ("maximum", toJson 128)]
  checkOutput "JSON nesting limit" (← invoke input)
    (expectedDiagnostic "input" "resourceLimit" "$" details)

private def checkInputBytesLimit : IO Unit := do
  let input := String.ofList (List.replicate 1048577 ' ')
  let details := Json.mkObj [("limit", toJson "inputBytes"), ("maximum", toJson 1048576)]
  checkOutput "input byte limit" (← invoke input)
    (expectedDiagnostic "input" "resourceLimit" "$" details)

private def checkInvalidUtf8 : IO Unit := do
  checkOutput "invalid UTF-8" (← invokeBytes (ByteArray.mk #[0xff]))
    (expectedDiagnostic "input" "invalidJson" "$")

private def checkNaturalNumberLimit : IO Unit := do
  let input := "{\"protocolVersion\":9007199254740992}"
  let details := Json.mkObj [
    ("limit", toJson "naturalNumber"),
    ("maximum", toJson 9007199254740991)]
  checkOutput "natural-number limit" (← invoke input)
    (expectedDiagnostic "input" "resourceLimit" "$.protocolVersion" details)

private def checkExplicitOmittedCell : IO Unit := do
  let base ← IO.FS.readFile "examples/reference-cli/empty-number-equals-zero.request.json"
  let input ← replaceRequired base "\"cells\": [],"
    "\"cells\": [{\"fieldId\":0,\"state\":{\"tag\":\"omitted\"}}],"
  let details := Json.mkObj [("state", toJson "omitted")]
  checkOutput "explicit omitted cell" (← invoke input)
    (expectedDiagnostic "unsupported" "cellState" "$.cells[0].state.tag" details)

private def checkChildRelativePath : IO Unit := do
  let base ← IO.FS.readFile "examples/reference-cli/empty-number-equals-zero.request.json"
  let withChildDeclaration ← replaceRequired base
    "\"groupPath\": [\"Order\"]," "\"groupPath\": [\"Order\", \"Sub\"],"
  let input ← replaceRequired withChildDeclaration
    "\"field\": {\"base\": \"absolute\", \"groups\": [\"Order\"], \"field\": \"Quantity\"},"
    "\"field\": {\"base\": \"relative\", \"parents\": 0, \"groups\": [\"Sub\"], \"field\": \"Quantity\"},"
  let details := Json.mkObj [("form", toJson "childRelative")]
  checkOutput "child-relative path" (← invoke input)
    (expectedDiagnostic "unsupported" "pathForm" "$.condition.field" details)

private def checkVersionAndOperationAssertions : IO Unit := do
  let base ← IO.FS.readFile "examples/reference-cli/empty-number-equals-zero.request.json"
  let wrongKernel ← replaceRequired base "\"kernelBehaviorVersion\": \"30.8.1\""
    "\"kernelBehaviorVersion\": \"30.9.0\""
  let kernelDetails := Json.mkObj [
    ("received", toJson "30.9.0"), ("supported", toJson "30.8.1")]
  checkOutput "kernel behavior version mismatch" (← invoke wrongKernel)
    (expectedDiagnostic "protocol" "kernelBehaviorVersionMismatch"
      "$.kernelBehaviorVersion" kernelDetails)
  let wrongOperation ← replaceRequired base
    "\"operation\": \"flatValidation.evaluateFull\"" "\"operation\": \"unknown\""
  let operationDetails := Json.mkObj [
    ("received", toJson "unknown"),
    ("supported", toJson "flatValidation.evaluateFull")]
  checkOutput "unsupported operation" (← invoke wrongOperation)
    (expectedDiagnostic "protocol" "unsupportedOperation" "$.operation" operationDetails)

private def checkUnsupportedOrderingMatrix : IO Unit := do
  let base ← IO.FS.readFile "examples/reference-cli/unsupported-ordering.request.json"
  for operator in ["lessEqual", "greater", "greaterEqual"] do
    let input ← replaceRequired base "\"operator\": \"less\""
      s!"\"operator\": \"{operator}\""
    let details := Json.mkObj [("operator", toJson operator)]
    checkOutput s!"unsupported ordering {operator}" (← invoke input)
      (expectedDiagnostic "unsupported" "operator" "$.condition" details)

private def checkPathAndDecimalBoundaries : IO Unit := do
  let base ← IO.FS.readFile "examples/reference-cli/empty-number-equals-zero.request.json"
  let unknownBase ← replaceRequired base "\"base\": \"absolute\"" "\"base\": \"named\""
  checkOutput "unsupported path base" (← invoke unknownBase)
    (expectedDiagnostic "unsupported" "pathBase" "$.condition.field.base"
      (Json.mkObj [("base", toJson "named")]))
  let nonCanonical ← replaceRequired base "\"value\": \"0\"" "\"value\": \"1.0\""
  checkOutput "non-canonical decimal" (← invoke nonCanonical)
    (expectedDiagnostic "input" "invalidDecimal" "$.condition.literal.value"
      (Json.mkObj [("value", toJson "1.0")]))
  let maximumDecimal := String.ofList (List.replicate 256 '1')
  let maximumInput ← replaceRequired base "\"value\": \"0\""
    s!"\"value\": \"{maximumDecimal}\""
  let notFired ← canonicalFile "examples/reference-cli/empty-boolean-equals-true.response.json"
  checkOutput "maximum decimal length" (← invoke maximumInput) notFired
  let oversizedDecimal := maximumDecimal ++ "1"
  let oversizedInput ← replaceRequired base "\"value\": \"0\""
    s!"\"value\": \"{oversizedDecimal}\""
  checkOutput "decimal length limit" (← invoke oversizedInput)
    (expectedDiagnostic "input" "resourceLimit" "$.condition.literal.value"
      (Json.mkObj [("limit", toJson "decimalCharacters"), ("maximum", toJson 256)]))

private def requestWithGroupCount (count : Nat) : IO Json := do
  let request ← readJsonFile "examples/reference-cli/empty-number-equals-zero.request.json"
  let groups := (List.range count).map fun index => s!"G{index}"
  let model ← objectMember request "model"
  let fields ← arrayValue (← objectMember model "fields")
  let declaration := (← firstValue fields).setObjVal! "groupPath" (toJson groups)
  let model := model.setObjVal! "fields" (Json.arr #[declaration])
  let condition ← objectMember request "condition"
  let field ← objectMember condition "field"
  let condition := condition.setObjVal! "field" (field.setObjVal! "groups" (toJson groups))
  pure <| request.setObjVal! "model" model |>.setObjVal! "declaringGroup" (toJson groups)
    |>.setObjVal! "condition" condition

private def checkPathSegmentBoundary : IO Unit := do
  let maximumRequest ← requestWithGroupCount 63
  let fired ← canonicalFile "examples/reference-cli/empty-number-equals-zero.response.json"
  checkOutput "maximum complete field path" (← invoke maximumRequest.compress) fired
  let oversizedRequest ← requestWithGroupCount 64
  checkOutput "complete field path limit" (← invoke oversizedRequest.compress)
    (expectedDiagnostic "input" "resourceLimit" "$.condition.field"
      (Json.mkObj [("limit", toJson "pathSegments"), ("maximum", toJson 64)]))

private def checkCellBoundary : IO Unit := do
  let base ← IO.FS.readFile "examples/reference-cli/empty-number-equals-zero.request.json"
  let duplicate ← replaceRequired base "\"cells\": [],"
    "\"cells\": [{\"fieldId\":0,\"state\":{\"tag\":\"parsedNumber\",\"value\":\"0\"}},{\"fieldId\":0,\"state\":{\"tag\":\"parsedNumber\",\"value\":\"1\"}}],"
  checkOutput "duplicate cell ID" (← invoke duplicate)
    (expectedDiagnostic "input" "duplicateCellId" "$.cells"
      (Json.mkObj [("fieldId", toJson 0)]))
  let undeclared ← replaceRequired base "\"cells\": [],"
    "\"cells\": [{\"fieldId\":99,\"state\":{\"tag\":\"parsedNumber\",\"value\":\"0\"}}],"
  checkOutput "undeclared cell ID" (← invoke undeclared)
    (expectedDiagnostic "input" "undeclaredCellId" "$.cells"
      (Json.mkObj [("fieldId", toJson 99)]))
  let wrongKind ← replaceRequired base "\"cells\": [],"
    "\"cells\": [{\"fieldId\":0,\"state\":{\"tag\":\"parsedBoolean\",\"value\":true}}],"
  let unknown ← canonicalFile "examples/reference-cli/malformed-number.response.json"
  checkOutput "wrong-kind parsed cell" (← invoke wrongKind) unknown
  let confirmBase ← IO.FS.readFile "examples/reference-cli/empty-confirm-not-equal-true.request.json"
  let falseConfirm ← replaceRequired confirmBase "\"cells\": [],"
    "\"cells\": [{\"fieldId\":0,\"state\":{\"tag\":\"parsedConfirm\",\"value\":false}}],"
  checkOutput "stored Confirm false" (← invoke falseConfirm)
    (expectedDiagnostic "input" "invalidShape" "$.cells[0].state.value"
      (Json.mkObj [("reason", toJson "storedConfirmMustBeTrue")]))

private def checkModelAndRepeatableBoundary : IO Unit := do
  let request ← readJsonFile "examples/reference-cli/empty-number-equals-zero.request.json"
  let model ← objectMember request "model"
  let fields ← arrayValue (← objectMember model "fields")
  let first ← firstValue fields
  let duplicate := first.setObjVal! "id" (toJson 1)
  let duplicateModel := model.setObjVal! "fields" (Json.arr (fields.push duplicate))
  let duplicateRequest := request.setObjVal! "model" duplicateModel
  checkOutput "duplicate model path" (← invoke duplicateRequest.compress)
    (expectedDiagnostic "model" "duplicateEntityPath" "$.model"
      (Json.mkObj [("path", toJson ["Order", "Quantity"])]))
  let repeatableField := Json.mkObj [
    ("id", toJson 1), ("groupPath", toJson ["Order", "Items"]),
    ("name", toJson "Count"),
    ("kind", Json.mkObj [("tag", toJson "number"), ("scale", toJson 0),
      ("signed", toJson false)]),
    ("repeatableScope", toJson [10])]
  let repeatableGroup := Json.mkObj [("level", toJson 10),
    ("path", toJson ["Order", "Items"])]
  let repeatableModel := model.setObjVal! "fields" (Json.arr (fields.push repeatableField))
    |>.setObjVal! "repeatableGroups" (Json.arr #[repeatableGroup])
  let repeatableCell := Json.mkObj [("fieldId", toJson 1),
    ("state", Json.mkObj [("tag", toJson "parsedNumber"), ("value", toJson "0")])]
  let cellRequest := request.setObjVal! "model" repeatableModel
    |>.setObjVal! "cells" (Json.arr #[repeatableCell])
  checkOutput "repeatable cell" (← invoke cellRequest.compress)
    (expectedDiagnostic "unsupported" "repeatableCell" "$.cells"
      (Json.mkObj [("fieldId", toJson 1), ("repeatableScope", toJson [10])]))
  let condition ← objectMember request "condition"
  let reference := Json.mkObj [("base", toJson "absolute"),
    ("groups", toJson ["Order", "Items"]), ("field", toJson "Count")]
  let repeatableCondition := condition.setObjVal! "field" reference
  let referenceRequest := request.setObjVal! "model" repeatableModel
    |>.setObjVal! "condition" repeatableCondition
  checkOutput "repeatable reference" (← invoke referenceRequest.compress)
    (expectedDiagnostic "unsupported" "repeatableReference" "$.condition"
      (Json.mkObj [("path", toJson ["Order", "Items", "Count"])]))

private def checkManifest : IO Unit := do
  let expected ← canonicalFile "reference/supported-fragment-v1.json"
  checkOutput "manifest" (← invoke "" #["--manifest"]) expected

private def checkInvocationError : IO Unit := do
  checkOutput "unexpected argument" (← invoke "" #["--unknown"])
    "" 2 "a12-kernel-reference: expected no arguments or --manifest\n"

def main : IO Unit := do
  for fixture in fixtures do
    checkFixture fixture
  checkDeterminism
  checkDuplicateMember
  checkEmptyInput
  checkUnknownMember
  checkNonCanonicalJsonNumber
  checkJsonNestingLimit
  checkInputBytesLimit
  checkInvalidUtf8
  checkNaturalNumberLimit
  checkExplicitOmittedCell
  checkChildRelativePath
  checkVersionAndOperationAssertions
  checkUnsupportedOrderingMatrix
  checkPathAndDecimalBoundaries
  checkPathSegmentBoundary
  checkCellBoundary
  checkModelAndRepeatableBoundary
  checkManifest
  checkInvocationError
  IO.println s!"reference process: {fixtures.length + 19}/{fixtures.length + 19} check groups passed"
