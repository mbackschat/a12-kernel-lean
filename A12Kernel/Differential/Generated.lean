import A12Kernel.Differential.Profile

/-! # Generated differential profile self-test

This executable-only gate checks the frozen profile decoder, exact finite enumeration, structural budgets, and response projection. A separately named compatibility audit then runs those historical requests through the current in-process Lean reference; it is not reconstruction of the historical result. `A12Kernel.Differential.Runner` owns the separate bounded subprocess campaign.
-/

namespace A12Kernel.Differential.Generated

open Lean
open A12Kernel.Differential.Profile
open A12Kernel.Reference

private def fail (message : String) : IO α :=
  throw (IO.userError message)

private def zeroRevision : String := String.ofList (List.replicate 40 '0')

private def oneRevision : String := String.ofList (List.replicate 40 '1')

private def compatibilityJson : Json := Json.mkObj [
  ("capabilityId", toJson Lineage.historicalFlatCapability.suiteId),
  ("operation", toJson Lineage.historicalFlatCapability.operation),
  ("referenceSemanticsVersion",
    toJson Lineage.historicalFlatCapability.compatibility.referenceSemanticsVersion),
  ("protocolVersion", toJson Lineage.historicalFlatCapability.compatibility.protocolVersion),
  ("manifestSchemaVersion",
    toJson Lineage.historicalFlatCapability.compatibility.manifestSchemaVersion),
  ("kernelBehaviorVersion",
    toJson Lineage.historicalFlatCapability.compatibility.kernelBehaviorVersion)]

private def boundsJson : Json := Json.mkObj [
  ("cases", toJson expectedCaseCount),
  ("requestBytes", toJson 4096),
  ("fields", toJson 3),
  ("cells", toJson 2),
  ("conditionDepth", toJson 2),
  ("conditionNodes", toJson 3),
  ("aggregateRequestBytes", toJson 65536),
  ("aggregateProcessInputBytes", toJson 131072),
  ("processTimeoutMilliseconds", toJson 2000),
  ("processCleanupMilliseconds", toJson 1000),
  ("processPollMilliseconds", toJson 5),
  ("aggregateElapsedMilliseconds", toJson 30000),
  ("processStdoutBytes", toJson 4096),
  ("processStderrBytes", toJson 4096),
  ("aggregateProcessOutputBytes", toJson 524288),
  ("resultBytes", toJson 1048576)]

private def executionJson : Json := Json.mkObj [
  ("strategy", toJson "sequentialDualProcessViaProjectRelay"),
  ("processGroupContract", toJson "lean4.31-posix-setsid-sigkill"),
  ("platforms", toJson ["macos", "linux"]),
  ("workingDirectory", toJson "inherited"),
  ("environment", toJson "inherited"),
  ("jobs", toJson 1),
  ("processesPerCase", toJson 2)]

private def generatorJson : Json := Json.mkObj [
  ("strategy", toJson "exhaustiveFiniteMatrices"),
  ("group", toJson "GeneratedForm"),
  ("fieldOrder", toJson ["N", "B", "C"]),
  ("cellStateOrder", toJson ["sparseEmpty", "parsedBooleanTrue", "rejectedMalformed"]),
  ("leafOrder", toJson ["numberEqualZero", "booleanEqualTrue", "confirmNotEqualTrue", "booleanNotFilled"]),
  ("verdictAtomOrder", toJson ["notFired", "value", "omission", "unknown"]),
  ("rowGateAtomOrder", toJson ["ineligible", "eligible"]),
  ("connectiveOrder", toJson ["and", "or"])]

private def canonicalProfileJson : Json := Json.mkObj [
  ("schemaVersion", toJson schemaVersion),
  ("profileId", toJson profileId),
  ("compatibility", compatibilityJson),
  ("revisions", Json.mkObj [
    ("referenceRepository", toJson "a12-kernel-lean"),
    ("candidateRepository", toJson "a12-kernel-rust-spike"),
    ("reference", toJson zeroRevision),
    ("candidate", toJson oneRevision)]),
  ("responseProjection", toJson "flatVerdictV1"),
  ("observableVerdicts", toJson ["notFired", "fired.value", "fired.omission", "unknown"]),
  ("bounds", boundsJson),
  ("execution", executionJson),
  ("generator", generatorJson)]

private def replaceMember (json : Json) (name : String) (value : Json) : Except String Json := do
  let members ← match json.getObj? with
    | .ok object => pure object.toList
    | .error _ => throw "self-test expected an object"
  if !members.any (·.1 == name) then throw s!"self-test object has no member '{name}'"
  pure <| Json.mkObj (members.map fun member => if member.1 == name then (name, value) else member)

private def replaceNestedMember (json : Json) (objectName memberName : String) (value : Json) :
    Except String Json := do
  let nested ← match json.getObjVal? objectName with
    | .ok value => pure value
    | .error _ => throw s!"self-test profile has no object '{objectName}'"
  replaceMember json objectName (← replaceMember nested memberName value)

private def addMember (json : Json) (name : String) (value : Json) : Except String Json := do
  let members ← match json.getObj? with
    | .ok object => pure object.toList
    | .error _ => throw "self-test expected an object"
  pure <| Json.mkObj (members ++ [(name, value)])

private def expectParseFailure (label : String) (input : String) : Except String Unit :=
  match parseText input with
  | .error _ => pure ()
  | .ok _ => throw s!"profile guard accepted {label}"

private def expectGenerationFailure (label : String) (json : Json) : Except String Unit := do
  let profile ← parseText json.compress
  match generate profile with
  | .error _ => pure ()
  | .ok _ => throw s!"generation guard accepted {label}"

private structure Distribution where
  notFired : Nat := 0
  firedValue : Nat := 0
  firedOmission : Nat := 0
  unknown : Nat := 0
  deriving Repr, DecidableEq

private def Distribution.add (distribution : Distribution) : ProjectedVerdict → Distribution
  | .notFired => { distribution with notFired := distribution.notFired + 1 }
  | .firedValue => { distribution with firedValue := distribution.firedValue + 1 }
  | .firedOmission => { distribution with firedOmission := distribution.firedOmission + 1 }
  | .unknown => { distribution with unknown := distribution.unknown + 1 }

private def evaluateCurrentCompatibilityDistribution (profile : Profile) (cases : List GeneratedCase) :
    Except String Distribution := do
  let mut distribution := {}
  for case in cases do
    distribution := distribution.add (← evaluateReference profile case)
  pure distribution

private def countFamily (family : Family) (cases : List GeneratedCase) : Nat :=
  (cases.filter (·.family == family)).length

private def expectedOrderedCaseIds : List String := [
  "generated-leaf-number-equal-zero-sparse-empty",
  "generated-leaf-number-equal-zero-parsed-boolean-true",
  "generated-leaf-number-equal-zero-rejected-malformed",
  "generated-leaf-boolean-equal-true-sparse-empty",
  "generated-leaf-boolean-equal-true-parsed-boolean-true",
  "generated-leaf-boolean-equal-true-rejected-malformed",
  "generated-leaf-confirm-not-equal-true-sparse-empty",
  "generated-leaf-confirm-not-equal-true-parsed-boolean-true",
  "generated-leaf-confirm-not-equal-true-rejected-malformed",
  "generated-leaf-boolean-not-filled-sparse-empty",
  "generated-leaf-boolean-not-filled-parsed-boolean-true",
  "generated-leaf-boolean-not-filled-rejected-malformed",
  "generated-algebra-and-not-fired-not-fired",
  "generated-algebra-and-not-fired-value",
  "generated-algebra-and-not-fired-omission",
  "generated-algebra-and-not-fired-unknown",
  "generated-algebra-and-value-not-fired",
  "generated-algebra-and-value-value",
  "generated-algebra-and-value-omission",
  "generated-algebra-and-value-unknown",
  "generated-algebra-and-omission-not-fired",
  "generated-algebra-and-omission-value",
  "generated-algebra-and-omission-omission",
  "generated-algebra-and-omission-unknown",
  "generated-algebra-and-unknown-not-fired",
  "generated-algebra-and-unknown-value",
  "generated-algebra-and-unknown-omission",
  "generated-algebra-and-unknown-unknown",
  "generated-algebra-or-not-fired-not-fired",
  "generated-algebra-or-not-fired-value",
  "generated-algebra-or-not-fired-omission",
  "generated-algebra-or-not-fired-unknown",
  "generated-algebra-or-value-not-fired",
  "generated-algebra-or-value-value",
  "generated-algebra-or-value-omission",
  "generated-algebra-or-value-unknown",
  "generated-algebra-or-omission-not-fired",
  "generated-algebra-or-omission-value",
  "generated-algebra-or-omission-omission",
  "generated-algebra-or-omission-unknown",
  "generated-algebra-or-unknown-not-fired",
  "generated-algebra-or-unknown-value",
  "generated-algebra-or-unknown-omission",
  "generated-algebra-or-unknown-unknown",
  "generated-row-gate-and-ineligible-ineligible",
  "generated-row-gate-and-ineligible-eligible",
  "generated-row-gate-and-eligible-ineligible",
  "generated-row-gate-and-eligible-eligible",
  "generated-row-gate-or-ineligible-ineligible",
  "generated-row-gate-or-ineligible-eligible",
  "generated-row-gate-or-eligible-ineligible",
  "generated-row-gate-or-eligible-eligible"]

private def fingerprintText (initial : UInt64) (value : String) : UInt64 :=
  value.toUTF8.foldl
    (fun fingerprint byte => (fingerprint ^^^ byte.toUInt64) * 1099511628211)
    initial

/-- A deterministic regression fingerprint, not a security or provenance digest. -/
private def requestFingerprint (cases : List GeneratedCase) : UInt64 :=
  cases.foldl
    (fun fingerprint generated => fingerprintText fingerprint (generated.request.compress ++ "\n"))
    14695981039346656037

private def expectedRequestFingerprint : UInt64 := 122705490169478792

private def findCase (cases : List GeneratedCase) (id : String) : Except String GeneratedCase :=
  match cases.find? (·.id == id) with
  | some generated => pure generated
  | none => throw s!"self-test could not find generated case '{id}'"

private def checkNamedVerdictAtoms (profile : Profile) (cases : List GeneratedCase) :
    Except String Unit := do
  let expectations : List (String × ProjectedVerdict) := [
    ("not-fired", .notFired),
    ("value", .firedValue),
    ("omission", .firedOmission),
    ("unknown", .unknown)]
  for (name, expected) in expectations do
    let generated ← findCase cases s!"generated-algebra-and-{name}-{name}"
    let actual ← evaluateReference profile generated
    if actual != expected then
      throw s!"named verdict atom '{name}' projected as {actual.tag}, expected {expected.tag}"

private def checkRowGateAtom (profile : Profile) (cases : List GeneratedCase)
    (name : String) (eligible : Bool) (expected : ProjectedVerdict) : Except String Unit := do
  let generated ← findCase cases s!"generated-row-gate-or-{name}-{name}"
  let request ← match Decode.request generated.request with
    | .ok (.flatValidation request) => pure request
    | .ok _ => throw s!"row-gate witness '{name}' decoded as the wrong operation"
    | .error diagnostic => throw s!"row-gate witness '{name}' was rejected: {diagnostic.asJson.compress}"
  if request.hasContent then
    throw s!"row-gate witness '{name}' lost its authoritative hasContent=false input"
  match request.cells with
  | [{ fieldId := 1, raw := .parsed (.bool true) }] => pure ()
  | _ => throw s!"row-gate witness '{name}' lost its present Boolean control cell"
  let checked ← match A12Kernel.elaborate request.model request.declaringGroup request.condition with
    | .ok checked => pure checked
    | .error error => throw s!"row-gate witness '{name}' did not lower: {repr error}"
  if checked.core.canFireOnEmpty != eligible then
    throw s!"row-gate atom '{name}' eligibility changed from {eligible}"
  let actual ← evaluateReference profile generated
  if actual != expected then
    throw s!"row-gate atom '{name}' projected as {actual.tag}, expected {expected.tag}"

private def checkRowGateAtoms (profile : Profile) (cases : List GeneratedCase) :
    Except String Unit := do
  checkRowGateAtom profile cases "ineligible" false .notFired
  checkRowGateAtom profile cases "eligible" true .firedOmission

private def expectProjectionFailure (profile : Profile) (label : String) (json : Json) :
    Except String Unit :=
  match projectResponse profile json with
  | .error _ => pure ()
  | .ok _ => throw s!"response projection accepted {label}"

private def responseJson (profile : Profile) (tag : String)
    (polarity? : Option String := none) : Json :=
  let verdictMembers := [("tag", toJson tag)] ++
    match polarity? with
    | some polarity => [("polarity", toJson polarity)]
    | none => []
  Json.mkObj [
    ("protocolVersion", toJson profile.compatibility.protocolVersion),
    ("kernelBehaviorVersion", toJson profile.compatibility.kernelBehaviorVersion),
    ("outcome", toJson "ok"),
    ("verdict", Json.mkObj verdictMembers)]

private def checkProjectionGuards (profile : Profile) : Except String Unit := do
  expectProjectionFailure profile "a wrong protocol version"
    (← replaceMember (responseJson profile "notFired") "protocolVersion" (toJson 2))
  expectProjectionFailure profile "a wrong kernel version"
    (← replaceMember (responseJson profile "notFired") "kernelBehaviorVersion" (toJson "other"))
  expectProjectionFailure profile "an unknown response member"
    (← addMember (responseJson profile "notFired") "unexpected" (toJson true))
  let base ← responseJson profile "notFired" |>.getObjVal? "verdict" |>.mapError fun _ =>
    "self-test response has no verdict"
  expectProjectionFailure profile "an unknown verdict member"
    (← replaceMember (responseJson profile "notFired") "verdict"
      (← addMember base "unexpected" (toJson true)))
  expectProjectionFailure profile "polarity on notFired"
    (responseJson profile "notFired" (some "value"))
  expectProjectionFailure profile "polarity on unknown"
    (responseJson profile "unknown" (some "value"))
  expectProjectionFailure profile "fired without polarity" (responseJson profile "fired")
  let mistypedPolarity ← replaceMember (responseJson profile "fired" (some "value")) "verdict"
    (Json.mkObj [("tag", toJson "fired"), ("polarity", toJson 1)])
  expectProjectionFailure profile "a mistyped polarity" mistypedPolarity
  let diagnostic := Json.mkObj [
    ("protocolVersion", toJson profile.compatibility.protocolVersion),
    ("kernelBehaviorVersion", toJson profile.compatibility.kernelBehaviorVersion),
    ("outcome", toJson "error"),
    ("diagnostic", Json.mkObj [])]
  expectProjectionFailure profile "an error response" diagnostic

private def checkProfileGuards : Except String Unit := do
  let canonical := canonicalProfileJson
  expectParseFailure "an unknown top-level member"
    (← addMember canonical "unexpected" (toJson true)).compress
  expectParseFailure "a duplicate top-level member"
    ("{\"schemaVersion\":1," ++ canonical.compress.drop 1)
  expectParseFailure "a different capability"
    (← replaceNestedMember canonical "compatibility" "capabilityId" (toJson "other-capability")).compress
  expectParseFailure "a non-revision reference pin"
    (← replaceNestedMember canonical "revisions" "reference" (toJson "main")).compress
  expectParseFailure "a different reference repository identity"
    (← replaceNestedMember canonical "revisions" "referenceRepository" (toJson "other")).compress
  expectParseFailure "a different candidate repository identity"
    (← replaceNestedMember canonical "revisions" "candidateRepository" (toJson "other")).compress
  expectParseFailure "an unknown response projection"
    (← replaceMember canonical "responseProjection" (toJson "wholeJson")).compress
  expectParseFailure "an incomplete verdict projection"
    (← replaceMember canonical "observableVerdicts" (toJson ["notFired", "unknown"])).compress
  expectParseFailure "a reordered generator domain"
    (← replaceNestedMember canonical "generator" "fieldOrder" (toJson ["B", "N", "C"])).compress
  expectParseFailure "a zero process timeout"
    (← replaceNestedMember canonical "bounds" "processTimeoutMilliseconds" (toJson 0)).compress
  expectParseFailure "a zero cleanup timeout"
    (← replaceNestedMember canonical "bounds" "processCleanupMilliseconds" (toJson 0)).compress
  expectParseFailure "concurrent execution"
    (← replaceNestedMember canonical "execution" "jobs" (toJson 2)).compress
  expectParseFailure "a missing process-output budget"
    (← replaceNestedMember canonical "bounds" "processStdoutBytes" (toJson 0)).compress
  expectParseFailure "a request-body budget that leaves no room for the JSON-line newline"
    (← replaceNestedMember canonical "bounds" "requestBytes"
      (toJson historicalMaxInputBytes)).compress
  expectParseFailure "an undersized aggregate process-input budget"
    (← replaceNestedMember canonical "bounds" "aggregateProcessInputBytes" (toJson 1)).compress
  expectParseFailure "an undersized result budget"
    (← replaceNestedMember canonical "bounds" "resultBytes" (toJson 1)).compress
  expectParseFailure "a non-additive result budget"
    (← replaceNestedMember canonical "bounds" "resultBytes" (toJson 200000)).compress
  expectGenerationFailure "an undersized per-request budget"
    (← replaceNestedMember canonical "bounds" "requestBytes" (toJson 32))
  expectGenerationFailure "an undersized aggregate request budget"
    (← replaceNestedMember canonical "bounds" "aggregateRequestBytes" (toJson 4096))

/-- Exercise the frozen profile/generator and an explicitly separate current-reference
backward-compatibility audit without launching a child process. The frozen result artifact
is validated from its pinned bytes and distribution elsewhere; this function does not
reconstruct it from today's evaluator. -/
def selfTest : IO Unit := do
  let result : Except String (Nat × Distribution) := do
    let profile ← parseText canonicalProfileJson.compress
    let cases ← generate profile
    if countFamily .leafCellState cases != 12 then throw "expected 12 leaf/cell-state cases"
    if countFamily .verdictAlgebra cases != 32 then throw "expected 32 verdict-algebra cases"
    if countFamily .rowGate cases != 8 then throw "expected 8 row-gate cases"
    if cases.map (·.id) != expectedOrderedCaseIds then
      throw "generated case IDs or their exact order changed"
    let fingerprint := requestFingerprint cases
    if fingerprint != expectedRequestFingerprint then
      throw s!"generated request identity changed: fingerprint={fingerprint.toNat}"
    let repeated ← generate profile
    if repeated.map (·.id) != cases.map (·.id) ||
        repeated.map (·.request.compress) != cases.map (·.request.compress) then
      throw "deterministic generation changed between invocations"
    -- This is deliberately a current compatibility audit. It may change or be retired when
    -- the current decoder/evaluator no longer supports the historical request vocabulary.
    let distribution ← evaluateCurrentCompatibilityDistribution profile cases
    let expected : Distribution := { notFired := 14, firedValue := 11, firedOmission := 13, unknown := 14 }
    if distribution != expected then
      throw s!"reference verdict distribution {repr distribution} does not match {repr expected}"
    checkNamedVerdictAtoms profile cases
    checkRowGateAtoms profile cases
    checkProjectionGuards profile
    checkProfileGuards
    pure (cases.length, distribution)
  match result with
  | .error error => fail error
  | .ok (count, distribution) =>
      IO.println s!"generated differential profile self-test: {count}/{expectedCaseCount}; current compatibility verdicts notFired={distribution.notFired}, fired.value={distribution.firedValue}, fired.omission={distribution.firedOmission}, unknown={distribution.unknown}"

end A12Kernel.Differential.Generated
