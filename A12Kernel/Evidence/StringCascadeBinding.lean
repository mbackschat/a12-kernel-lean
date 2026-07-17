import A12Kernel.Evidence.Capture.Receipt
import A12Kernel.Evidence.StringCascadeReplay
import A12Kernel.Process.Sha256
import A12Kernel.Reference.StrictJson

/-! # A12Kernel.Evidence.StringCascadeBinding — qualified packet correspondence

This IO-only gate verifies the complete retained direct-cascade packet and qualification trees, closes their cross-artifact identities, checks the two kernel routes and interpreter fidelity, and replays the common observable projection through Lean. It establishes five-case correspondence only; the packet does not expose Lean's hidden dependency cell or prove a general scheduler.
-/

namespace A12Kernel.Evidence.StringCascade.Binding

open Lean
open A12Kernel
open A12Kernel.Process.Artifact
open A12Kernel.Evidence.StringCascade

private def packetReceiptText :=
  "7e38744283cf17f7f57fe0bce342084a8e2896fb99aa60c2a9f4fb52e185dc17"

private def packetDiffReceiptText :=
  "b868d6fb57c38dd1b01edf56e58b507567c9c1a17265bcd692b822e97a4d0ce8"

private def qualificationReceiptText :=
  "f581d82d7eb04929b38d4663bbb48a28f09c7399273cd5974cd59e739eca5d64"

private def sourceRevision :=
  "c992afd62e4fa6148733a5538a3248c30fce60bf"

private def requestDigest :=
  "4c5d4911ecacde819618b3b921b0bd30aa34b514cb0bbf3f0d2b735f21a0fd43"

private def modelDigest :=
  "3d21add02d259a8d1ad2e14475582513aec2f4e60176f1c02c81d40de88a895d"

private def capabilitiesDigest :=
  "b87d381e7f43446bc886292766e34beab72ca3ec179be5f0f614975e66d603ca"

private def member [FromJson α] (json : Json) (name context : String) : Except String α := do
  let value ← match json.getObjVal? name with
    | .ok value => pure value
    | .error _ => throw s!"{context}: missing member '{name}'"
  match fromJson? value with
  | .ok value => pure value
  | .error error => throw s!"{context}: member '{name}': {error}"

private def objectNames (context : String) (json : Json) : Except String (List String) :=
  match json.getObj? with
  | .ok object => pure <| object.toList.map (fun entry => entry.1)
  | .error _ => throw s!"{context} must be an object"

private def hasDuplicate [BEq α] : List α → Bool
  | [] => false
  | value :: rest => rest.contains value || hasDuplicate rest

private def sameInventory (actual expected : List String) : Bool :=
  !hasDuplicate actual && actual.mergeSort == expected.mergeSort

private def requireMembers (context : String) (json : Json)
    (expected : List String) : Except String Unit := do
  let actual ← objectNames context json
  if !sameInventory actual expected then
    throw s!"{context} has unknown, missing, or duplicate members"

private def requireString (context : String) (json : Json)
    (name expected : String) : Except String Unit := do
  let actual : String ← member json name context
  if actual != expected then
    throw s!"{context}: member '{name}' is '{actual}', expected '{expected}'"

private def lowercaseHexOfLength (length : Nat) (value : String) : Bool :=
  value.length == length && value.toList.all fun character =>
    character.isDigit || ('a' ≤ character && character ≤ 'f')

private def requireDigestText (context value : String) : Except String Unit := do
  if !lowercaseHexOfLength 64 value then
    throw s!"{context}: expected a lowercase SHA-256 digest"

private def requirePortable (context value : String) : Except String Unit := do
  match PortablePath.parse value with
  | .ok _ => pure ()
  | .error error => throw s!"{context}: {error}"

private def findUnique (context : String) (values : List α)
    (predicate : α → Bool) : Except String α :=
  match values.filter predicate with
  | [value] => pure value
  | [] => throw s!"{context}: no matching member"
  | _ => throw s!"{context}: duplicate matching members"

private def orThrow (context : String) : Except String α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{context}: {error}")

private def expectRejected (context expectedMessage : String)
    (result : Except String α) : IO Unit :=
  match result with
  | .ok _ => throw (IO.userError s!"direct-cascade mutation was accepted: {context}")
  | .error error =>
      if !error.contains expectedMessage then
        throw (IO.userError
          s!"direct-cascade mutation '{context}' failed at the wrong guard; expected '{expectedMessage}', found '{error}'")
      else
        pure ()

private def readJson (path : System.FilePath) : IO Json := do
  let input ← A12Kernel.Process.ArtifactTree.readBoundedText path "direct-cascade JSON"
  match A12Kernel.Reference.StrictJson.parse input with
  | .ok json => pure json
  | .error error => throw (IO.userError s!"{path}: invalid strict JSON: {repr error}")

private def verifyNamedDigest (root : System.FilePath) (reference expected : String) :
    IO Unit := do
  orThrow reference (requirePortable reference reference)
  let actual ← A12Kernel.Process.Sha256.file (root / reference)
  if actual != expected then
    throw (IO.userError
      s!"{reference}: digest mismatch; expected {expected}, found {actual}")

private structure ObservationArtifact where
  runner : String
  artifact : String
  sha256 : String
  status : String
  deriving Repr, DecidableEq

private structure PacketCase where
  caseId : String
  modelRef : String
  observations : List ObservationArtifact
  deriving Repr, DecidableEq

private structure Packet where
  capabilitiesArtifact : String
  requestArtifact : String
  inputArtifact : String
  legalityArtifact : String
  legalitySha256 : String
  treeStateDigest : String
  cases : List PacketCase
  deriving Repr, DecidableEq

private def ObservationArtifact.fromJson (context : String)
    (json : Json) : Except String ObservationArtifact := do
  requireMembers context json ["runner", "artifact", "sha256", "status"]
  let artifact : String ← member json "artifact" context
  let sha256 : String ← member json "sha256" context
  requirePortable (context ++ ".artifact") artifact
  requireDigestText (context ++ ".sha256") sha256
  pure {
    runner := ← member json "runner" context
    artifact
    sha256
    status := ← member json "status" context }

private def validateKernelIdentity (json : Json) : Except String Unit := do
  requireMembers "packet.kernel" json [
    "artifactCoordinate", "version", "artifactSha256", "closure"]
  requireString "packet.kernel" json "artifactCoordinate"
    "com.mgmtp.a12.kernel:kernel-md-runtime-service"
  requireString "packet.kernel" json "version" A12Kernel.kernelVersion
  let artifactSha256 : String ← member json "artifactSha256" "packet.kernel"
  requireDigestText "packet.kernel.artifactSha256" artifactSha256
  let closure : List Json ← member json "closure" "packet.kernel"
  if closure.isEmpty then
    throw "packet.kernel: runtime closure must not be empty"
  let entries ← closure.zipIdx.mapM fun (entry, index) => do
    let context := s!"packet.kernel.closure[{index}]"
    requireMembers context entry ["coordinate", "version", "sha256"]
    let coordinate : String ← member entry "coordinate" context
    let version : String ← member entry "version" context
    let sha256 : String ← member entry "sha256" context
    if coordinate.isEmpty || version.isEmpty then
      throw s!"{context}: coordinate and version must not be empty"
    requireDigestText (context ++ ".sha256") sha256
    pure (coordinate, version, sha256)
  if hasDuplicate (entries.map (fun entry => entry.1)) then
    throw "packet.kernel: duplicate runtime-closure coordinate"
  let anchor ← findUnique "packet kernel anchor" entries fun entry =>
    entry.1 == "com.mgmtp.a12.kernel:kernel-md-runtime-service"
  if anchor.2.1 != A12Kernel.kernelVersion || anchor.2.2 != artifactSha256 then
    throw "packet.kernel: anchor artifact differs from its runtime-closure member"

private def validateCaptureIdentity (json : Json) : Except String String := do
  requireMembers "packet.capture" json [
    "tool", "toolVersion", "sourceRevision", "workingTree", "developmentMode",
    "treeStateDigest", "runtime", "closureNote"]
  requireString "packet.capture" json "tool" "a12-dmkits-capture"
  requireString "packet.capture" json "toolVersion" "1"
  requireString "packet.capture" json "sourceRevision" sourceRevision
  requireString "packet.capture" json "workingTree" "clean"
  let developmentMode : Bool ← member json "developmentMode" "packet.capture"
  if developmentMode then
    throw "packet.capture: retained qualification cannot use development mode"
  let treeStateDigest : String ← member json "treeStateDigest" "packet.capture"
  requireDigestText "packet.capture.treeStateDigest" treeStateDigest
  let closureNote : String ← member json "closureNote" "packet.capture"
  if closureNote.isEmpty then
    throw "packet.capture: closure note must not be empty"
  let runtime ← json.getObjVal? "runtime"
  requireMembers "packet.capture.runtime" runtime [
    "javaSpecificationVersion", "javaVendor", "javaRuntimeVersion", "vmName"]
  requireString "packet.capture.runtime" runtime "javaSpecificationVersion" "21"
  for name in ["javaVendor", "javaRuntimeVersion", "vmName"] do
    let value : String ← member runtime name "packet.capture.runtime"
    if value.isEmpty then
      throw s!"packet.capture.runtime: member '{name}' must not be empty"
  pure treeStateDigest

private def validatePacketRunner (context : String) (json : Json)
    (expected : String × String × String) : Except String Unit := do
  requireMembers context json ["id", "role", "route"]
  requireString context json "id" expected.1
  requireString context json "role" expected.2.1
  requireString context json "route" expected.2.2

private def Packet.fromJson (json : Json) : Except String Packet := do
  requireMembers "packet" json [
    "schema", "operationSchema", "capabilities", "kernel", "capture", "scenario",
    "world", "runners", "inputs", "legality", "cases", "command"]
  requireString "packet" json "schema" "evidence-packet-v1"
  requireString "packet" json "operationSchema" "compute-observation-v1"
  validateKernelIdentity (← json.getObjVal? "kernel")
  let treeStateDigest ← validateCaptureIdentity (← json.getObjVal? "capture")

  let capabilities ← json.getObjVal? "capabilities"
  requireMembers "packet.capabilities" capabilities [
    "schema", "version", "artifact", "sha256"]
  requireString "packet.capabilities" capabilities "schema"
    "a12-dmkits-capture-capabilities-v1"
  requireString "packet.capabilities" capabilities "version" "1"
  requireString "packet.capabilities" capabilities "artifact"
    "capabilities/capabilities.json"
  requireString "packet.capabilities" capabilities "sha256" capabilitiesDigest

  let scenario ← json.getObjVal? "scenario"
  requireMembers "packet.scenario" scenario [
    "id", "version", "requestArtifact", "requestSha256"]
  requireString "packet.scenario" scenario "id" "string-direct-cascade-v1"
  requireString "packet.scenario" scenario "version" "1"
  requireString "packet.scenario" scenario "requestArtifact" "request/scenarios.json"
  requireString "packet.scenario" scenario "requestSha256" requestDigest

  let world ← json.getObjVal? "world"
  requireMembers "packet.world" world ["profile", "locale", "timezoneHandling"]
  requireString "packet.world" world "profile" "local-wallclock-v1"
  requireString "packet.world" world "locale" "en_US"
  requireString "packet.world" world "timezoneHandling" "runner-local-wall-clock"

  let runners : List Json ← member json "runners" "packet"
  let expectedRunners := [
    ("kernel-groovy-dynamic", "anchor", "kernel-md-runtime dynamic service"),
    ("kernel-java-static", "cross-route-confirmation",
      "kernel static generated-java codegen"),
    ("a12-dmkits-interpreter", "triangulation", "a12-dmkits interpreter")]
  if runners.length != expectedRunners.length then
    throw "packet.runners: expected exactly three runners"
  for pair in runners.zip expectedRunners |>.zipIdx do
    validatePacketRunner s!"packet.runners[{pair.2}]" pair.1.1 pair.1.2

  let inputs : List Json ← member json "inputs" "packet"
  let input ← match inputs with
    | [input] => pure input
    | _ => throw "packet.inputs: expected exactly one copied model"
  requireMembers "packet.inputs[0]" input [
    "ref", "artifact", "suppliedSha256", "adaptedSha256"]
  requireString "packet.inputs[0]" input "ref" "models/string-direct-cascade.json"
  requireString "packet.inputs[0]" input "artifact"
    "inputs/models/string-direct-cascade.json"
  requireString "packet.inputs[0]" input "suppliedSha256" modelDigest
  requireString "packet.inputs[0]" input "adaptedSha256" modelDigest

  let legality : List Json ← member json "legality" "packet"
  let legality ← match legality with
    | [legality] => pure legality
    | _ => throw "packet.legality: expected exactly one legality result"
  requireMembers "packet.legality[0]" legality [
    "ref", "artifact", "sha256", "verdict"]
  requireString "packet.legality[0]" legality "ref" "models/string-direct-cascade.json"
  requireString "packet.legality[0]" legality "artifact"
    "legality/models/string-direct-cascade.json"
  requireString "packet.legality[0]" legality "verdict" "legal"
  let legalityDigest : String ← member legality "sha256" "packet.legality[0]"
  requireDigestText "packet.legality[0].sha256" legalityDigest

  let casesJson : List Json ← member json "cases" "packet"
  let cases ← casesJson.zipIdx.mapM fun (caseJson, index) => do
    let context := s!"packet.cases[{index}]"
    requireMembers context caseJson [
      "caseId", "modelRef", "legality", "executed", "observations"]
    requireString context caseJson "modelRef" "models/string-direct-cascade.json"
    requireString context caseJson "legality" "legal"
    let executed : Bool ← member caseJson "executed" context
    if !executed then
      throw s!"{context}: retained case was not executed"
    let observationsJson : List Json ← member caseJson "observations" context
    let observations ← observationsJson.zipIdx.mapM fun (observation, observationIndex) =>
      ObservationArtifact.fromJson
        s!"{context}.observations[{observationIndex}]" observation
    pure {
      caseId := ← member caseJson "caseId" context
      modelRef := ← member caseJson "modelRef" context
      observations }

  let command ← json.getObjVal? "command"
  requireMembers "packet.command" command ["args"]
  let args : List String ← member command "args" "packet.command"
  if args != [
      "capture", "--scenarios", "request/scenarios.json",
      "--output", "<caller-owned-directory>"] then
    throw "packet.command: capture invocation differs from the retained portable form"

  pure {
    capabilitiesArtifact := ← member capabilities "artifact" "packet.capabilities"
    requestArtifact := ← member scenario "requestArtifact" "packet.scenario"
    inputArtifact := ← member input "artifact" "packet.inputs[0]"
    legalityArtifact := ← member legality "artifact" "packet.legality[0]"
    legalitySha256 := legalityDigest
    treeStateDigest
    cases }

private def requireStringList (context : String) (json : Json) (name : String)
    (expected : List String) : Except String Unit := do
  let actual : List String ← member json name context
  if actual != expected then
    throw s!"{context}: member '{name}' differs from the frozen V1 declaration"

private def validateDeclaredChannel (context : String) (json : Json)
    (availability granularity : String) : Except String Unit := do
  requireMembers context json ["availability", "granularity"]
  requireString context json "availability" availability
  requireString context json "granularity" granularity

private def validateDeclaredRunner (context : String) (json : Json)
    (id role route : String) (typed rendered causes absentEmpty : String)
    (changedAvailability changedGranularity clearedGranularity
      formalAvailability formalGranularity : String) : Except String Unit := do
  requireMembers context json [
    "id", "role", "route", "channels", "typedValues", "renderedValues",
    "structuredCauses", "absentVsPresentEmpty"]
  requireString context json "id" id
  requireString context json "role" role
  requireString context json "route" route
  requireString context json "typedValues" typed
  requireString context json "renderedValues" rendered
  requireString context json "structuredCauses" causes
  requireString context json "absentVsPresentEmpty" absentEmpty
  let channels ← json.getObjVal? "channels"
  requireMembers (context ++ ".channels") channels [
    "withoutErrors", "changedSubset", "withErrors", "cleared",
    "formalErrorsInOperands", "appliedState"]
  validateDeclaredChannel (context ++ ".channels.withoutErrors")
    (← channels.getObjVal? "withoutErrors") "available" "all-computed-clean"
  validateDeclaredChannel (context ++ ".channels.changedSubset")
    (← channels.getObjVal? "changedSubset") changedAvailability changedGranularity
  validateDeclaredChannel (context ++ ".channels.withErrors")
    (← channels.getObjVal? "withErrors") "available" "errored-instances"
  validateDeclaredChannel (context ++ ".channels.cleared")
    (← channels.getObjVal? "cleared") "available" clearedGranularity
  validateDeclaredChannel (context ++ ".channels.formalErrorsInOperands")
    (← channels.getObjVal? "formalErrorsInOperands") formalAvailability formalGranularity
  validateDeclaredChannel (context ++ ".channels.appliedState")
    (← channels.getObjVal? "appliedState") "available" "requested-probes"

private def validateCapabilities (json : Json) : Except String Unit := do
  requireMembers "capabilities" json [
    "schema", "capabilitiesVersion", "describes", "requestSchemas", "envelopeSchemas",
    "operationSchemas", "legalitySchema", "receiptSchema", "reportSchemas",
    "worldProfiles", "locales", "projections", "requiredChannelsSemantics",
    "commands", "policies", "runners"]
  requireString "capabilities" json "schema" "a12-dmkits-capture-capabilities-v1"
  requireString "capabilities" json "capabilitiesVersion" "1"
  requireString "capabilities" json "describes"
    "transport-capability, never A12 semantic support"
  requireStringList "capabilities" json "requestSchemas" ["capture-scenario-set-v1"]
  requireStringList "capabilities" json "envelopeSchemas" ["evidence-packet-v1"]
  requireString "capabilities" json "legalitySchema" "capture-legality-v1"
  requireString "capabilities" json "receiptSchema" "capture-receipt-v1"
  requireStringList "capabilities" json "reportSchemas" [
    "qualification-profile-v1", "qualification-report-v1",
    "packet-diff-report-v1", "report-diff-report-v1"]
  requireStringList "capabilities" json "worldProfiles" ["local-wallclock-v1"]
  requireStringList "capabilities" json "locales" ["en_US"]
  requireStringList "capabilities" json "projections" [
    "compute-projection-kernel-route-v1",
    "compute-projection-dmkits-portable-v1"]
  requireStringList "capabilities" json "commands" [
    "capabilities", "validate-scenarios", "capture", "verify",
    "diff-packets", "diff-reports"]
  let requiredSemantics : String ← member json "requiredChannelsSemantics" "capabilities"
  if requiredSemantics.isEmpty then
    throw "capabilities: required-channel semantics must not be empty"

  let operationSchemas : List Json ← member json "operationSchemas" "capabilities"
  let operation ← match operationSchemas with
    | [operation] => pure operation
    | _ => throw "capabilities: expected exactly one operation schema"
  requireMembers "capabilities.operationSchemas[0]" operation [
    "id", "inputSupport", "repeatableComputationTargets", "channels"]
  requireString "capabilities.operationSchemas[0]" operation "id" "compute-observation-v1"
  requireString "capabilities.operationSchemas[0]" operation "inputSupport"
    "non-repeatable-compute-targets-v1"
  requireString "capabilities.operationSchemas[0]" operation
    "repeatableComputationTargets" "rejected"
  requireStringList "capabilities.operationSchemas[0]" operation "channels" [
    "withoutErrors", "changedSubset", "withErrors", "cleared",
    "formalErrorsInOperands", "appliedState"]

  let policies : List Json ← member json "policies" "capabilities"
  let expectedPolicies : List (String × List String × List String) := [
    ("characterization-v1", [], []),
    ("kernel-route-confirmed-v1",
      ["kernel-groovy-dynamic", "kernel-java-static"],
      ["compute-projection-kernel-route-v1"]),
    ("dmkits-projected-conformance-v1",
      ["kernel-groovy-dynamic", "kernel-java-static", "a12-dmkits-interpreter"],
      ["compute-projection-kernel-route-v1", "compute-projection-dmkits-portable-v1"])]
  if policies.length != expectedPolicies.length then
    throw "capabilities: expected exactly three policies"
  for pair in policies.zip expectedPolicies |>.zipIdx do
    let context := s!"capabilities.policies[{pair.2}]"
    let policy := pair.1.1
    let expected := pair.1.2
    requireMembers context policy ["id", "qualifyingRunners", "mandatoryProjections"]
    requireString context policy "id" expected.1
    requireStringList context policy "qualifyingRunners" expected.2.1
    requireStringList context policy "mandatoryProjections" expected.2.2

  let runners : List Json ← member json "runners" "capabilities"
  if runners.length != 3 then
    throw "capabilities: expected exactly three runner declarations"
  match runners with
  | [groovy, java, interpreter] =>
      validateDeclaredRunner "capabilities.runners[0]" groovy
        "kernel-groovy-dynamic" "anchor" "kernel-md-runtime dynamic service"
        "available" "available" "available" "available"
        "available" "delta-vs-input" "input-filled-only"
        "available" "operand-formal-errors"
      validateDeclaredRunner "capabilities.runners[1]" java
        "kernel-java-static" "cross-route-confirmation"
        "kernel static generated-java codegen"
        "available" "available" "available" "available"
        "available" "delta-vs-input" "input-filled-only"
        "available" "operand-formal-errors"
      validateDeclaredRunner "capabilities.runners[2]" interpreter
        "a12-dmkits-interpreter" "triangulation" "a12-dmkits interpreter"
        "notExposedByRunner" "available" "notExposedByRunner" "notExposedByRunner"
        "notExposedByRunner" "notExposed" "all-cleared"
        "notExposedByRunner" "notExposed"
  | _ => throw "capabilities: expected exactly three runner declarations"

private def validateLegality (json : Json) : Except String Unit := do
  requireMembers "legality" json [
    "schema", "validator", "modelRef", "suppliedSha256", "adaptedSha256",
    "verdict", "notifications"]
  requireString "legality" json "schema" "capture-legality-v1"
  requireString "legality" json "modelRef" "models/string-direct-cascade.json"
  requireString "legality" json "suppliedSha256" modelDigest
  requireString "legality" json "adaptedSha256" modelDigest
  requireString "legality" json "verdict" "legal"
  let notifications : List Json ← member json "notifications" "legality"
  if !notifications.isEmpty then
    throw "legality: the closed model must have no notifications"
  let validator ← json.getObjVal? "validator"
  requireMembers "legality.validator" validator ["runner", "kernelVersion"]
  requireString "legality.validator" validator "runner" "kernel-checkConsistency"
  requireString "legality.validator" validator "kernelVersion" A12Kernel.kernelVersion

private def validateLocale (context : String) (json : Json) : Except String Unit := do
  requireMembers context json ["code"]
  requireString context json "code" "en_US"

private def validateErrorMessage (context : String) (json : Json)
    (expectedText : String) : Except String Unit := do
  requireMembers context json ["locale", "text"]
  requireString context json "locale" "en_US"
  requireString context json "text" expectedText

private def validateComputation (context : String) (json : Json)
    (id name target operation message : String) : Except String Unit := do
  requireMembers context json ["type", "id", "name", "Computation"]
  requireString context json "type" "Computation"
  requireString context json "id" id
  requireString context json "name" name
  let body ← json.getObjVal? "Computation"
  requireMembers (context ++ ".Computation") body [
    "computedFieldRelPath", "computationAlternatives", "errorMessage"]
  requireString (context ++ ".Computation") body "computedFieldRelPath" target
  let alternatives : List Json ← member body "computationAlternatives"
    (context ++ ".Computation")
  let alternative ← match alternatives with
    | [alternative] => pure alternative
    | _ => throw s!"{context}: expected exactly one unconditional alternative"
  requireMembers (context ++ ".Computation.computationAlternatives[0]")
    alternative ["operation"]
  requireString (context ++ ".Computation.computationAlternatives[0]")
    alternative "operation" operation
  let messages : List Json ← member body "errorMessage" (context ++ ".Computation")
  let retainedMessage ← match messages with
    | [retainedMessage] => pure retainedMessage
    | _ => throw s!"{context}: expected exactly one English error message"
  validateErrorMessage (context ++ ".Computation.errorMessage[0]")
    retainedMessage message

private def validateStringField (context : String) (json : Json)
    (id name : String) (maximum : Option Nat) : Except String Unit := do
  requireMembers context json ["type", "id", "name", "Field"]
  requireString context json "type" "Field"
  requireString context json "id" id
  requireString context json "name" name
  let field ← json.getObjVal? "Field"
  requireMembers (context ++ ".Field") field ["fieldType"]
  let fieldType ← field.getObjVal? "fieldType"
  match maximum with
  | none =>
      requireMembers (context ++ ".Field.fieldType") fieldType ["type"]
      requireString (context ++ ".Field.fieldType") fieldType "type" "StringType"
  | some bound =>
      requireMembers (context ++ ".Field.fieldType") fieldType ["type", "StringType"]
      requireString (context ++ ".Field.fieldType") fieldType "type" "StringType"
      let stringType ← fieldType.getObjVal? "StringType"
      requireMembers (context ++ ".Field.fieldType.StringType") stringType ["maxLength"]
      let actual : Nat ← member stringType "maxLength"
        (context ++ ".Field.fieldType.StringType")
      if actual != bound then
        throw s!"{context}: unexpected String maximum length {actual}"

private def validateModel (json : Json) : Except String Unit := do
  requireMembers "cascade model" json ["header", "content"]
  let header ← json.getObjVal? "header"
  requireMembers "cascade model.header" header [
    "id", "modelType", "modelVersion", "locales", "labels",
    "annotations", "modelReferences"]
  requireString "cascade model.header" header "id" "lean-string-direct-cascade"
  requireString "cascade model.header" header "modelType" "document"
  requireString "cascade model.header" header "modelVersion" "28.4.0"
  let locales : List Json ← member header "locales" "cascade model.header"
  match locales with
  | [locale] => validateLocale "cascade model.header.locales[0]" locale
  | _ => throw "cascade model.header: expected exactly one locale"
  for name in ["labels", "annotations", "modelReferences"] do
    let values : List Json ← member header name "cascade model.header"
    if !values.isEmpty then
      throw s!"cascade model.header: member '{name}' must be empty"

  let content ← json.getObjVal? "content"
  requireMembers "cascade model.content" content ["modelInfo", "modelConfig", "modelRoot"]
  let info ← content.getObjVal? "modelInfo"
  requireMembers "cascade model.content.modelInfo" info [
    "name", "variant", "revision", "immutable"]
  requireString "cascade model.content.modelInfo" info "name" "lean-string-direct-cascade"
  requireString "cascade model.content.modelInfo" info "variant" "cockpit"
  requireString "cascade model.content.modelInfo" info "revision" "Arbeitsversion"
  let immutable : Bool ← member info "immutable" "cascade model.content.modelInfo"
  if immutable then
    throw "cascade model.content.modelInfo: retained model must be mutable"

  let config ← content.getObjVal? "modelConfig"
  requireMembers "cascade model.content.modelConfig" config [
    "decimalSeparator", "timeZone", "conditionLanguage", "fieldRefByShortNameAllowed"]
  requireString "cascade model.content.modelConfig" config "decimalSeparator" "."
  requireString "cascade model.content.modelConfig" config "timeZone" "Europe/Berlin"
  let shortNames : Bool ← member config "fieldRefByShortNameAllowed"
    "cascade model.content.modelConfig"
  if !shortNames then
    throw "cascade model.content.modelConfig: short-name resolution must be enabled"
  let language ← config.getObjVal? "conditionLanguage"
  requireMembers "cascade model.content.modelConfig.conditionLanguage" language ["code"]
  requireString "cascade model.content.modelConfig.conditionLanguage" language "code" "en_US"

  let modelRoot ← content.getObjVal? "modelRoot"
  requireMembers "cascade model.content.modelRoot" modelRoot ["rootGroups"]
  let roots : List Json ← member modelRoot "rootGroups" "cascade model.content.modelRoot"
  let root ← match roots with
    | [root] => pure root
    | _ => throw "cascade model: expected exactly one root group"
  requireMembers "cascade model.rootGroups[0]" root ["type", "id", "name", "Group"]
  requireString "cascade model.rootGroups[0]" root "type" "Group"
  requireString "cascade model.rootGroups[0]" root "id" "/Cascade"
  requireString "cascade model.rootGroups[0]" root "name" "Cascade"
  let group ← root.getObjVal? "Group"
  requireMembers "cascade model.rootGroups[0].Group" group ["repeatability", "elements"]
  let repeatability : Nat ← member group "repeatability" "cascade model.rootGroups[0].Group"
  if repeatability != 1 then
    throw "cascade model: root group must be non-repeatable"
  let elements : List Json ← member group "elements" "cascade model.rootGroups[0].Group"
  match elements with
  | [midComputationJson, outComputationJson, sourceJson, midJson, outJson] =>
      validateComputation "cascade model.elements[0]" midComputationJson
        "/Cascade/MidComputation" "MidComputation" "../Mid" "[Source]"
        "Mid could not be computed."
      validateComputation "cascade model.elements[1]" outComputationJson
        "/Cascade/OutComputation" "OutComputation" "../Out" "[Mid] + \"-X\""
        "Out could not be computed."
      validateStringField "cascade model.elements[2]" sourceJson
        "/Cascade/Source" "Source" none
      validateStringField "cascade model.elements[3]" midJson
        "/Cascade/Mid" "Mid" (some 3)
      validateStringField "cascade model.elements[4]" outJson
        "/Cascade/Out" "Out" none
  | _ => throw "cascade model: expected the exact two-computation/three-field inventory"

private def validateProfileProjection (context : String) (json : Json)
    (id role : String) (included : List String)
    (excluded : Option (List String)) : Except String Unit := do
  match excluded with
  | none =>
      requireMembers context json [
        "id", "version", "role", "includedFields", "comparison"]
  | some _ =>
      requireMembers context json [
        "id", "version", "role", "includedFields", "excludedFields", "comparison"]
  requireString context json "id" id
  requireString context json "version" "1"
  requireString context json "role" role
  requireStringList context json "includedFields" included
  let comparison : String ← member json "comparison" context
  if comparison.isEmpty then
    throw s!"{context}: comparison description must not be empty"
  match excluded with
  | none => pure ()
  | some expected =>
      let excludedJson : List Json ← member json "excludedFields" context
      let fields ← excludedJson.zipIdx.mapM fun (entry, index) => do
        let entryContext := s!"{context}.excludedFields[{index}]"
        requireMembers entryContext entry ["field", "rationale"]
        let field : String ← member entry "field" entryContext
        let rationale : String ← member entry "rationale" entryContext
        if rationale.isEmpty then
          throw s!"{entryContext}: rationale must not be empty"
        pure field
      if fields != expected then
        throw s!"{context}: excluded-field inventory differs from frozen V1"

private def validateQualificationProfile (json : Json) : Except String Unit := do
  requireMembers "qualification profile" json ["schema", "policy", "projections", "rules"]
  requireString "qualification profile" json "schema" "qualification-profile-v1"
  let policy ← json.getObjVal? "policy"
  requireMembers "qualification profile.policy" policy ["id", "version"]
  requireString "qualification profile.policy" policy "id" "kernel-route-confirmed-v1"
  requireString "qualification profile.policy" policy "version" "1"
  let projections : List Json ← member json "projections" "qualification profile"
  match projections with
  | [kernel, interpreter] =>
      validateProfileProjection "qualification profile.projections[0]" kernel
        "compute-projection-kernel-route-v1" "required"
        ["allChannels", "typedValues", "renderedValues", "structuredCauses", "appliedStates"]
        none
      validateProfileProjection "qualification profile.projections[1]" interpreter
        "compute-projection-dmkits-portable-v1" "reported"
        ["targets", "outcomeClassification", "renderedValues", "attemptedRenderedValues",
          "clearedAtKernelGranularity", "appliedValueText"]
        (some ["typedValues", "structuredCauses", "changedSubset",
          "formalErrorsInOperands", "appliedState.absentVsPresentEmpty"])
  | _ => throw "qualification profile: expected exactly two projections"
  let rules : List String ← member json "rules" "qualification profile"
  if rules.length != 5 || rules.any String.isEmpty then
    throw "qualification profile: expected five nonempty policy rules"

private def validateComparisonChannel (context : String) (json : Json)
    (channel result : String) (detailRequired : Bool) : Except String Unit := do
  requireMembers context json ["channel", "result", "detail"]
  requireString context json "channel" channel
  requireString context json "result" result
  let detail : Option String ← member json "detail" context
  if detailRequired then
    match detail with
    | some text =>
        if text.isEmpty then throw s!"{context}: exclusion detail must not be empty"
    | none => throw s!"{context}: exclusion detail is missing"
  else if detail.isSome then
    throw s!"{context}: an equal comparison must not carry a detail"

private def validateComparison (context caseId : String) (json : Json)
    (kernelProjection : Bool) : Except String Unit := do
  requireMembers context json [
    "caseId", "runnerA", "runnerB", "projection", "projectionVersion",
    "includedFields", "unavailableFields", "channels", "result"]
  requireString context json "caseId" caseId
  requireString context json "runnerA" "kernel-groovy-dynamic"
  requireString context json "runnerB"
    (if kernelProjection then "kernel-java-static" else "a12-dmkits-interpreter")
  requireString context json "projection"
    (if kernelProjection then "compute-projection-kernel-route-v1"
      else "compute-projection-dmkits-portable-v1")
  requireString context json "projectionVersion" "1"
  requireString context json "result" "equal"
  let unavailable : List String ← member json "unavailableFields" context
  if !unavailable.isEmpty then
    throw s!"{context}: comparison must not hide unavailable projected fields"
  if kernelProjection then
    requireStringList context json "includedFields" [
      "allChannels", "typedValues", "renderedValues", "structuredCauses", "appliedStates"]
  else
    requireStringList context json "includedFields" [
      "targets", "outcomeClassification", "renderedValues", "attemptedRenderedValues",
      "clearedAtKernelGranularity", "appliedValueText"]
  let channels : List Json ← member json "channels" context
  if kernelProjection then
    let expected := [
      "withoutErrors", "changedSubset", "withErrors", "cleared",
      "formalErrorsInOperands", "appliedState"]
    if channels.length != expected.length then
      throw s!"{context}: kernel comparison must cover all six channels"
    for pair in channels.zip expected |>.zipIdx do
      validateComparisonChannel s!"{context}.channels[{pair.2}]"
        pair.1.1 pair.1.2 "equal" false
  else
    let expected : List (String × String × Bool) := [
      ("withoutErrors", "equal", false),
      ("withErrors", "equal", false),
      ("cleared", "equal", false),
      ("appliedState", "equal", false),
      ("changedSubset", "excluded", true),
      ("formalErrorsInOperands", "excluded", true)]
    if channels.length != expected.length then
      throw s!"{context}: portable comparison must classify all six channels"
    for pair in channels.zip expected |>.zipIdx do
      validateComparisonChannel s!"{context}.channels[{pair.2}]"
        pair.1.1 pair.1.2.1 pair.1.2.2.1 pair.1.2.2.2

private def validateQualificationReport (json : Json)
    (actualProfileDigest expectedTreeStateDigest : String) : Except String Unit := do
  requireMembers "qualification report" json [
    "schema", "policy", "request", "packet", "profileSha256",
    "verifier", "verdict", "reasons", "comparisons"]
  requireString "qualification report" json "schema" "qualification-report-v1"
  requireString "qualification report" json "profileSha256" actualProfileDigest
  requireString "qualification report" json "verdict" "satisfied"
  let reasons : List String ← member json "reasons" "qualification report"
  if !reasons.isEmpty then
    throw "qualification report: a satisfied report must have no reasons"

  let policy ← json.getObjVal? "policy"
  requireMembers "qualification report.policy" policy ["id", "version"]
  requireString "qualification report.policy" policy "id" "kernel-route-confirmed-v1"
  requireString "qualification report.policy" policy "version" "1"

  let request ← json.getObjVal? "request"
  requireMembers "qualification report.request" request [
    "scenarioSetId", "scenarioSetVersion", "requestSha256",
    "qualificationPolicy", "observationRequirement"]
  requireString "qualification report.request" request "scenarioSetId"
    "string-direct-cascade-v1"
  requireString "qualification report.request" request "scenarioSetVersion" "1"
  requireString "qualification report.request" request "requestSha256" requestDigest
  requireString "qualification report.request" request "qualificationPolicy"
    "kernel-route-confirmed-v1"
  let requirement ← request.getObjVal? "observationRequirement"
  requireMembers "qualification report.request.observationRequirement" requirement [
    "id", "version", "requiredChannels", "comparisonProjections"]
  requireString "qualification report.request.observationRequirement" requirement "id"
    "string-direct-cascade-kernel-route-v1"
  requireString "qualification report.request.observationRequirement" requirement "version" "1"
  requireStringList "qualification report.request.observationRequirement"
    requirement "requiredChannels" [
      "withoutErrors", "changedSubset", "withErrors", "cleared",
      "formalErrorsInOperands", "appliedState"]
  requireStringList "qualification report.request.observationRequirement"
    requirement "comparisonProjections" [
      "compute-projection-kernel-route-v1", "compute-projection-dmkits-portable-v1"]

  let packet ← json.getObjVal? "packet"
  requireMembers "qualification report.packet" packet [
    "receiptSha256", "sourceRevision", "workingTree"]
  requireString "qualification report.packet" packet "receiptSha256" packetReceiptText
  requireString "qualification report.packet" packet "sourceRevision" sourceRevision
  requireString "qualification report.packet" packet "workingTree" "clean"

  let verifier ← json.getObjVal? "verifier"
  requireMembers "qualification report.verifier" verifier [
    "tool", "toolVersion", "sourceRevision", "workingTree", "treeStateDigest"]
  requireString "qualification report.verifier" verifier "tool" "a12-dmkits-capture"
  requireString "qualification report.verifier" verifier "toolVersion" "1"
  requireString "qualification report.verifier" verifier "sourceRevision" sourceRevision
  requireString "qualification report.verifier" verifier "workingTree" "clean"
  let treeStateDigest : String ← member verifier "treeStateDigest"
    "qualification report.verifier"
  requireDigestText "qualification report.verifier.treeStateDigest" treeStateDigest
  if treeStateDigest != expectedTreeStateDigest then
    throw "qualification report: verifier tree state differs from the packet capture closure"

  let comparisons : List Json ← member json "comparisons" "qualification report"
  let caseIds := ScenarioRequest.expected.cases.map (·.caseId)
  if comparisons.length != caseIds.length * 2 then
    throw "qualification report: expected two comparisons for each retained case"
  for caseId in caseIds do
    let matching ← pure <| comparisons.filter fun comparison =>
      match comparison.getObjVal? "caseId" with
      | .ok (.str value) => value == caseId
      | _ => false
    match matching with
    | [kernel, interpreter] =>
        validateComparison s!"qualification report.comparisons[{caseId}].kernel"
          caseId kernel true
        validateComparison s!"qualification report.comparisons[{caseId}].interpreter"
          caseId interpreter false
    | _ => throw s!"qualification report: case '{caseId}' lacks exactly two comparisons"

private def validatePacketDiff (json : Json) : Except String Unit := do
  requireMembers "packet diff" json [
    "schema", "before", "after", "identical", "drift", "projection"]
  requireString "packet diff" json "schema" "packet-diff-report-v1"
  requireString "packet diff" json "projection" "compute-projection-kernel-route-v1"
  let identical : Bool ← member json "identical" "packet diff"
  if !identical then
    throw "packet diff: clean recaptures were not identical"
  let drift : List Json ← member json "drift" "packet diff"
  if !drift.isEmpty then
    throw "packet diff: identical recaptures must have no drift"
  for name in ["before", "after"] do
    let side ← json.getObjVal? name
    requireMembers s!"packet diff.{name}" side ["receiptSha256"]
    requireString s!"packet diff.{name}" side "receiptSha256" packetReceiptText

-- The request validator closes each placement stream; these retained upstream hashes bind
-- every runner's consumed identity back to that exact per-case stream.
private def expectedConsumedDocumentDigest (caseId : String) : Except String String :=
  match caseId with
  | "source-abc-mid-old" =>
      pure "ad8a8b4dd054f854987f74bf9f803e081fdac23cf9427d8eb17189eb8500409c"
  | "source-abc-mid-abc" =>
      pure "b0fbbe25a13575bc66d52b66c6b02204da10ef982d0f169d572edcf64052b5ae"
  | "source-absent-mid-old" =>
      pure "91741339b50cf089dd1857a87331ac424a9eeabeece09ae359482071db4bff92"
  | "source-absent-mid-absent" =>
      pure "3e6c0a9426bf7c5cc667e1641936a3ac27ee1a483ef4cdeebc01ffe3825ab3bf"
  | "source-abcd-mid-old" =>
      pure "a1718de009a2f5c5a84013ee9a30ea19e306a4b452cc23382947373d0688606c"
  | other => throw s!"{other}: no closed consumed-document digest"

private def validateObservationIdentity (case : ScenarioCase)
    (runner : String) (observation : Observation) : Except String Unit := do
  if observation.caseId != case.caseId || observation.runner != runner then
    throw s!"{case.caseId}: observation identity or runner differs from its packet member"
  if observation.status != "success" || observation.statusDetail.isSome then
    throw s!"{case.caseId}: observation status is not a clean success"
  if observation.consumedModel.ref != "models/string-direct-cascade.json" ||
      observation.consumedModel.suppliedSha256 != modelDigest ||
      observation.consumedModel.adaptedSha256 != modelDigest then
    throw s!"{case.caseId}: consumed model identity differs from the supplied model"
  let expectedDocumentDigest ← expectedConsumedDocumentDigest case.caseId
  if observation.consumedDocument.placements != case.placements.length ||
      observation.consumedDocument.canonicalSha256 != expectedDocumentDigest then
    throw s!"{case.caseId}: consumed document identity does not cover the supplied placements"

private def normalizeKernelRunner (observation : Observation) : Observation :=
  { observation with runner := "kernel-groovy-dynamic" }

private def validateCaseObservations (case : ScenarioCase)
    (groovy java interpreter : Observation) : Except String CoreProjection := do
  validateObservationIdentity case "kernel-groovy-dynamic" groovy
  validateObservationIdentity case "kernel-java-static" java
  validateObservationIdentity case "a12-dmkits-interpreter" interpreter
  if groovy.consumedDocument != java.consumedDocument ||
      groovy.consumedDocument != interpreter.consumedDocument then
    throw s!"{case.caseId}: runners consumed different document identities"
  if groovy.consumedModel != java.consumedModel ||
      groovy.consumedModel != interpreter.consumedModel then
    throw s!"{case.caseId}: runners consumed different model identities"
  if normalizeKernelRunner java != groovy then
    throw s!"{case.caseId}: kernel routes differ in raw order, multiplicity, or channel content"
  let observed ← groovy.projectKernel
  let replayed ← case.replay
  if observed.signatures != replayed.signatures then
    throw s!"{case.caseId}: kernel projection {repr observed.signatures} differs from Lean {repr replayed.signatures}"
  let kernelPortable ← groovy.projectPortable case
  let interpreterPortable ← interpreter.projectPortable case
  if kernelPortable.signatures != interpreterPortable.signatures then
    throw s!"{case.caseId}: interpreter triangulation differs on the declared portable projection"
  pure observed

private def expectedObservationArtifacts (caseId : String) :
    List (String × String) := [
  ("kernel-groovy-dynamic",
    s!"observations/{caseId}/kernel-groovy-dynamic.json"),
  ("kernel-java-static",
    s!"observations/{caseId}/kernel-java-static.json"),
  ("a12-dmkits-interpreter",
    s!"observations/{caseId}/a12-dmkits-interpreter.json")]

private def validatePacketAgainstRequest (packet : Packet)
    (request : ScenarioRequest) : Except String Unit := do
  if packet.cases.map (·.caseId) != request.cases.map (·.caseId) then
    throw "packet case order or inventory differs from the input-only request"
  for case in request.cases do
    let retained ← findUnique s!"packet case '{case.caseId}'" packet.cases
      (·.caseId == case.caseId)
    if retained.modelRef != request.modelRef then
      throw s!"{case.caseId}: packet case model differs from the request"
    let actual := retained.observations.map fun observation =>
      (observation.runner, observation.artifact)
    if actual != expectedObservationArtifacts case.caseId ||
        retained.observations.any (·.status != "success") then
      throw s!"{case.caseId}: packet observation routes, paths, or statuses differ"

private def receiptInventory
    (verified : A12Kernel.Evidence.Capture.Receipt.VerifiedReceipt) :
    List (String × String) :=
  verified.receipt.artifacts.map fun artifact =>
    (artifact.file.path.toString, artifact.role)

private def validateReceiptInventory (context : String)
    (verified : A12Kernel.Evidence.Capture.Receipt.VerifiedReceipt)
    (expected : List (String × String)) : Except String Unit := do
  let actual := receiptInventory verified
  let sort := fun (values : List (String × String)) =>
    values.mergeSort fun left right =>
      if left.1 == right.1 then left.2 ≤ right.2 else left.1 ≤ right.1
  if sort actual != sort expected then
    throw s!"{context}: receipt roles or complete member inventory differ"

private def expectedPacketReceiptInventory (packet : Packet) :
    List (String × String) :=
  [
    ("PACKET.json", "packet-envelope"),
    (packet.capabilitiesArtifact, "capability-declaration"),
    (packet.inputArtifact, "copied-input"),
    (packet.legalityArtifact, "legality"),
    (packet.requestArtifact, "copied-request")
  ] ++ packet.cases.flatMap fun case =>
    case.observations.map fun observation => (observation.artifact, "observation")

private def readObservation (packetRoot : System.FilePath)
    (artifact : ObservationArtifact) : IO Observation := do
  verifyNamedDigest packetRoot artifact.artifact artifact.sha256
  orThrow artifact.artifact <| Observation.fromJson
    (← readJson (packetRoot / artifact.artifact))

private def readCaseObservations (packetRoot : System.FilePath)
    (packetCase : PacketCase) : IO (Observation × Observation × Observation) := do
  match packetCase.observations with
  | [groovyArtifact, javaArtifact, interpreterArtifact] =>
      let groovy ← readObservation packetRoot groovyArtifact
      let java ← readObservation packetRoot javaArtifact
      let interpreter ← readObservation packetRoot interpreterArtifact
      pure (groovy, java, interpreter)
  | _ => throw (IO.userError
      s!"{packetCase.caseId}: expected exactly three observation artifacts")

private def checkAdversarialLocks (request : ScenarioRequest)
    (loaded : List (ScenarioCase × Observation × Observation × Observation)) : IO Unit := do
  let accepted ← orThrow "accepted-case mutation fixture" <|
    findUnique "accepted-case mutation fixture" loaded
      (fun entry => entry.1.caseId == "source-abc-mid-old")
  let (acceptedCase, acceptedGroovy, acceptedJava, acceptedInterpreter) := accepted
  let reversedJava := {
    acceptedJava with
    withoutErrors := {
      acceptedJava.withoutErrors with
      entries := acceptedJava.withoutErrors.entries.reverse } }
  expectRejected "raw kernel result order" "raw order" <|
    validateCaseObservations acceptedCase acceptedGroovy reversedJava acceptedInterpreter

  let changedConsumedDocument := {
    acceptedGroovy.consumedDocument with
    canonicalSha256 :=
      "0000000000000000000000000000000000000000000000000000000000000000" }
  let changedGroovyDocument := {
    acceptedGroovy with consumedDocument := changedConsumedDocument }
  let changedJavaDocument := {
    acceptedJava with consumedDocument := changedConsumedDocument }
  let changedInterpreterDocument := {
    acceptedInterpreter with consumedDocument := changedConsumedDocument }
  expectRejected "consumed-document request binding" "supplied placements" <|
    validateCaseObservations acceptedCase changedGroovyDocument changedJavaDocument
      changedInterpreterDocument

  let changedInterpreter := {
    acceptedInterpreter with
    changedSubset := {
      acceptedInterpreter.changedSubset with
      availability := .available } }
  expectRejected "interpreter fidelity" "fidelity" <|
    validateCaseObservations acceptedCase acceptedGroovy acceptedJava changedInterpreter

  let leakedTypedValues := acceptedInterpreter.withoutErrors.entries.map fun entry =>
    { entry with value := {
        entry.value with
        typed := {
          availability := .available
          kind := some "STRING"
          value := entry.value.rendered.value } } }
  let typedLeak := {
    acceptedInterpreter with
    withoutErrors := {
      acceptedInterpreter.withoutErrors with entries := leakedTypedValues } }
  expectRejected "interpreter typed-value leak" "typed value fidelity" <|
    validateCaseObservations acceptedCase acceptedGroovy acceptedJava typedLeak

  let errored ← orThrow "errored-case mutation fixture" <|
    findUnique "errored-case mutation fixture" loaded
      (fun entry => entry.1.caseId == "source-abcd-mid-old")
  let (erroredCase, erroredGroovy, erroredJava, erroredInterpreter) := errored
  let changedErrors := erroredGroovy.withErrors.entries.map fun entry =>
    { entry with cause := { entry.cause with code := some "stringZuKurz" } }
  let changedGroovy := {
    erroredGroovy with
    withErrors := { erroredGroovy.withErrors with entries := changedErrors } }
  let changedJava := {
    erroredJava with
    withErrors := { erroredJava.withErrors with entries := changedErrors } }
  expectRejected "target-error cause" "differs from Lean" <|
    validateCaseObservations erroredCase changedGroovy changedJava erroredInterpreter

  let leakedCauses := erroredInterpreter.withErrors.entries.map fun entry =>
    { entry with cause := {
        availability := .available
        code := some "stringZuLang"
        messageType := some "VALUE_ERROR"
        errorPointer := some "/Cascade[1]/Mid" } }
  let causeLeak := {
    erroredInterpreter with
    withErrors := { erroredInterpreter.withErrors with entries := leakedCauses } }
  expectRejected "interpreter structured-cause leak" "error cause fidelity" <|
    validateCaseObservations erroredCase erroredGroovy erroredJava causeLeak

  let leakedAppliedStates := erroredInterpreter.appliedState.entries.map fun entry =>
    { entry with state := .presentEmpty }
  let appliedStateLeak := {
    erroredInterpreter with
    appliedState := {
      erroredInterpreter.appliedState with entries := leakedAppliedStates } }
  expectRejected "interpreter rich no-value-state leak" "unavailable in frozen V1" <|
    validateCaseObservations erroredCase erroredGroovy erroredJava appliedStateLeak

  let changedRequest := {
    request with cases := request.cases.map fun (scenario : ScenarioCase) =>
      if scenario.caseId == "source-abc-mid-old" then
        { scenario with probes := ["/Cascade[1]/Mid"] }
      else scenario }
  expectRejected "input-only scenario mutation" "closed input-only matrix"
    changedRequest.validate

private def parseDigest (context value : String) : IO Digest :=
  orThrow context (Digest.parse value)

/-- Verify and replay the complete retained direct String-cascade evidence unit. -/
def checkArtifacts (captureRoot : System.FilePath) : IO Nat := do
  let packetReceiptDigest ← parseDigest "packet receipt" packetReceiptText
  let packetDiffReceiptDigest ← parseDigest "packet-diff receipt" packetDiffReceiptText
  let qualificationReceiptDigest ← parseDigest "qualification receipt" qualificationReceiptText
  let packetRoot := captureRoot / "packet"
  let packetDiffRoot := captureRoot / "packet-diff"
  let qualificationRoot := captureRoot / "qualification"
  let packetReceipt ← A12Kernel.Evidence.Capture.Receipt.readAndVerify
    packetRoot packetReceiptDigest
  let packetDiffReceipt ← A12Kernel.Evidence.Capture.Receipt.readAndVerify
    packetDiffRoot packetDiffReceiptDigest
  let qualificationReceipt ← A12Kernel.Evidence.Capture.Receipt.readAndVerify
    qualificationRoot qualificationReceiptDigest

  let packet ← orThrow "PACKET.json" <| Packet.fromJson
    (← readJson (packetRoot / "PACKET.json"))
  orThrow "packet receipt roles" <|
    validateReceiptInventory "packet" packetReceipt
      (expectedPacketReceiptInventory packet)
  orThrow "packet-diff receipt roles" <|
    validateReceiptInventory "packet diff" packetDiffReceipt
      [("DIFF.json", "diff-report")]
  orThrow "qualification receipt roles" <|
    validateReceiptInventory "qualification" qualificationReceipt [
      ("PROFILE.json", "qualification-profile"),
      ("REPORT.json", "qualification-report")]

  verifyNamedDigest packetRoot packet.requestArtifact requestDigest
  let request ← orThrow packet.requestArtifact <| ScenarioRequest.fromJson
    (← readJson (packetRoot / packet.requestArtifact))
  orThrow packet.requestArtifact request.validate
  orThrow "PACKET.json request relations" <| validatePacketAgainstRequest packet request

  verifyNamedDigest packetRoot packet.capabilitiesArtifact capabilitiesDigest
  orThrow packet.capabilitiesArtifact <| validateCapabilities
    (← readJson (packetRoot / packet.capabilitiesArtifact))
  verifyNamedDigest packetRoot packet.inputArtifact modelDigest
  orThrow packet.inputArtifact <| validateModel
    (← readJson (packetRoot / packet.inputArtifact))
  verifyNamedDigest packetRoot packet.legalityArtifact packet.legalitySha256
  orThrow packet.legalityArtifact <| validateLegality
    (← readJson (packetRoot / packet.legalityArtifact))

  orThrow "packet-diff/DIFF.json" <|
    validatePacketDiff (← readJson (packetDiffRoot / "DIFF.json"))
  let profilePath := qualificationRoot / "PROFILE.json"
  let profileDigest ← A12Kernel.Process.Sha256.file profilePath
  orThrow "qualification/PROFILE.json" <|
    validateQualificationProfile (← readJson profilePath)
  let qualificationReport ← readJson (qualificationRoot / "REPORT.json")
  orThrow "qualification/REPORT.json" <|
    validateQualificationReport qualificationReport profileDigest packet.treeStateDigest
  let verifier ← orThrow "qualification/REPORT.json verifier" <|
    qualificationReport.getObjVal? "verifier"
  let changedReport := qualificationReport.setObjVal! "verifier"
    (verifier.setObjVal! "treeStateDigest"
      (toJson "0000000000000000000000000000000000000000000000000000000000000000"))
  expectRejected "qualification verifier closure" "packet capture closure" <|
    validateQualificationReport changedReport profileDigest packet.treeStateDigest

  let mut loaded : List (ScenarioCase × Observation × Observation × Observation) := []
  for case in request.cases do
    let packetCase ← orThrow case.caseId <|
      findUnique s!"packet case '{case.caseId}'" packet.cases (·.caseId == case.caseId)
    let observations ← readCaseObservations packetRoot packetCase
    discard <| orThrow case.caseId <|
      validateCaseObservations case observations.1 observations.2.1 observations.2.2
    loaded := loaded ++ [(case, observations.1, observations.2.1, observations.2.2)]
  checkAdversarialLocks request loaded
  pure request.cases.length

end A12Kernel.Evidence.StringCascade.Binding
