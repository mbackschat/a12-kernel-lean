import A12Kernel.Evidence.OperatorEmptyReplay
import A12Kernel.Process.Sha256
import A12Kernel.Reference.Protocol
import A12Kernel.Reference.StrictJson

/-! # A12Kernel.Evidence.OperatorProtocolBridge — directional Number evidence to protocol

This IO/test-side bridge derives the current flat suite's one directional Number case from the complete retained operator capture. It independently binds the selected model, case, rule, field, row-content witness, and three strategy signature lists before it associates normalized request/response bytes with the public suite case.
-/

namespace A12Kernel.Evidence.OperatorEmpty.ProtocolBridge

open Lean
open A12Kernel
open A12Kernel.Reference

private structure Placement where
  kind : String
  path : String
  reps : List Nat
  value : Option String
  deriving Repr, DecidableEq

private structure Observation where
  id : String
  kernelVersion : String
  modelRef : String
  operation : String
  placements : List Placement
  expected : List String
  divergences : List Json

private structure CaptureCase where
  id : String
  caseSha256 : String
  groovyDynamic : List String
  javaStatic : List String
  interpreter : List String
  deriving Repr, DecidableEq

private structure CaptureReceipt where
  schemaVersion : Nat
  kernelVersion : String
  sourceRevision : String
  operation : String
  cases : List CaptureCase
  deriving Repr, DecidableEq

private inductive CapturedPolarity where
  | value
  | omission
  deriving Repr, DecidableEq

private structure MessageSignature where
  code : String
  polarity : CapturedPolarity
  pointer : String
  deriving Repr, DecidableEq

/-- Exact source association for the sole 0.3.0 lineage-separating flat case. -/
structure Descriptor where
  suiteCaseId : String
  modelId : String
  retainedCaseId : String
  ruleName : String
  ruleCode : String
  fieldId : FieldId
  groupPath : List String
  fieldName : String
  scale : Nat
  signed : Bool
  literal : Int
  contentFieldName : String
  contentValue : String
  expectedPolarity : Polarity
  projection : System.FilePath
  suiteProjection : System.FilePath
  request : System.FilePath
  response : System.FilePath
  suite : System.FilePath
  covers : List String
  deriving Repr, DecidableEq

def descriptor : Descriptor := {
  suiteCaseId := "number-empty-not-equal-negative-directional"
  modelId := "lean-number-directional-empty"
  retainedCaseId := "number-directional-empty-content"
  ruleName := "LeanUnsignedNeNegative"
  ruleCode := "NUM_UNSIGNED_NE_NEG"
  fieldId := 0
  groupPath := ["Order"]
  fieldName := "StockOnHand"
  scale := 0
  signed := false
  literal := -1
  contentFieldName := "CustomerName"
  contentValue := "Acme"
  expectedPolarity := .value
  projection := "evidence/kernel-30.8.1/operator-empty-projection.json"
  suiteProjection := "evidence/kernel-30.8.1/captures/validation-core-v1/semantic-observations.json"
  request := "examples/reference-cli/empty-unsigned-number-not-equal-negative.request.json"
  response := "examples/reference-cli/empty-unsigned-number-not-equal-negative.response.json"
  suite := "reference/flat-validation-empty-logic-v2.conformance.json"
  covers := [
    "emptyUnsignedNumber",
    "notEqualNegativeLiteral",
    "directionalFillability",
    "valuePolarity"] }

private def firstDuplicate? [BEq α] : List α → Option α
  | [] => none
  | value :: rest => if rest.contains value then some value else firstDuplicate? rest

private def member [FromJson α] (json : Json) (name : String) : Except String α := do
  fromJson? (← json.getObjVal? name)

private def optionalArray (json : Json) (name : String) : Except String (List Json) :=
  match json.getObjVal? name with
  | .ok value => fromJson? value
  | .error _ => pure []

private def optionalString (json : Json) (name : String) : Except String (Option String) :=
  match json.getObjVal? name with
  | .ok value => some <$> fromJson? value
  | .error _ => pure none

private def Placement.fromJson (json : Json) : Except String Placement := do
  pure {
    kind := ← member json "kind"
    path := ← member json "path"
    reps := ← member json "reps"
    value := ← optionalString json "value" }

private def Observation.fromJson (json : Json) : Except String Observation := do
  let metadata ← json.getObjVal? "meta"
  let operation ← json.getObjVal? "op"
  let placements : List Json ← member json "placements"
  pure {
    id := ← member metadata "id"
    kernelVersion := ← member metadata "kernelVersion"
    modelRef := ← member json "modelRef"
    operation := ← member operation "kind"
    placements := ← placements.mapM Placement.fromJson
    expected := ← member json "expected"
    divergences := ← optionalArray json "divergences" }

private def CaptureCase.fromJson (json : Json) : Except String CaptureCase := do
  pure {
    id := ← member json "id"
    caseSha256 := ← member json "caseSha256"
    groovyDynamic := ← member json "groovyDynamic"
    javaStatic := ← member json "javaStatic"
    interpreter := ← member json "interpreter" }

private def CaptureReceipt.fromJson (json : Json) : Except String CaptureReceipt := do
  let cases : List Json ← member json "cases"
  pure {
    schemaVersion := ← member json "schemaVersion"
    kernelVersion := ← member json "kernelVersion"
    sourceRevision := ← member json "a12DmkitsRevision"
    operation := ← member json "operation"
    cases := ← cases.mapM CaptureCase.fromJson }

private def MessageSignature.parse (value : String) : Except String MessageSignature := do
  let (code, polarityName, pointer) ← match value.splitOn "|" with
    | [code, polarityName, pointer] => pure (code, polarityName, pointer)
    | _ => throw s!"invalid retained message signature '{value}'"
  if code.isEmpty || pointer.isEmpty then
    throw s!"incomplete retained message signature '{value}'"
  let polarity ← match polarityName with
    | "VALUE_ERROR" => pure .value
    | "OMISSION_ERROR" => pure .omission
    | other => throw s!"unsupported retained message polarity '{other}'"
  pure { code, polarity, pointer }

private def absolutePath (segments : List String) : String :=
  "/" ++ String.intercalate "/" segments

private def firstRowPointer (descriptor : Descriptor) : String :=
  absolutePath descriptor.groupPath ++ "[1]/" ++ descriptor.fieldName

private def fieldPath (descriptor : Descriptor) : List String :=
  descriptor.groupPath ++ [descriptor.fieldName]

private def findUnique (context : String) (values : List α) (predicate : α → Bool) :
    Except String α :=
  match values.filter predicate with
  | [value] => pure value
  | [] => throw s!"{context}: no exact match"
  | _ => throw s!"{context}: duplicate matches"

private def CaptureCase.completeSignatures (case : CaptureCase) : Except String (List String) := do
  if case.groovyDynamic != case.javaStatic || case.groovyDynamic != case.interpreter then
    throw s!"{case.id}: retained strategy signature lists disagree"
  if case.groovyDynamic != case.groovyDynamic.mergeSort then
    throw s!"{case.id}: retained strategy signatures are not canonical"
  if let some duplicate := firstDuplicate? case.groovyDynamic then
    throw s!"{case.id}: duplicate retained strategy signature '{duplicate}'"
  pure case.groovyDynamic

private def Descriptor.validate (descriptor : Descriptor) : Except String Unit := do
  if descriptor.suiteCaseId.isEmpty || descriptor.modelId.isEmpty ||
      descriptor.retainedCaseId.isEmpty || descriptor.ruleName.isEmpty ||
      descriptor.ruleCode.isEmpty || descriptor.groupPath.isEmpty ||
      descriptor.groupPath.any String.isEmpty || descriptor.fieldName.isEmpty ||
      descriptor.contentFieldName.isEmpty || descriptor.contentValue.isEmpty ||
      descriptor.covers.isEmpty then
    throw "operator protocol descriptor is incomplete"
  if descriptor.projection != "evidence/kernel-30.8.1/operator-empty-projection.json" then
    throw "operator protocol descriptor names the wrong evidence projection"
  if descriptor.suiteProjection !=
      "evidence/kernel-30.8.1/captures/validation-core-v1/semantic-observations.json" then
    throw "operator protocol descriptor names the wrong compact suite projection"
  if descriptor.suite != "reference/flat-validation-empty-logic-v2.conformance.json" then
    throw "operator protocol descriptor names the wrong current suite"

private def bindModel (descriptor : Descriptor) (bundle : Bundle) :
    Except String (ModelSpec × FieldSpec × RuleSpec) := do
  let model ← findUnique s!"model '{descriptor.modelId}'" bundle.models
    (·.id == descriptor.modelId)
  if model.declaringGroup != descriptor.groupPath then
    throw s!"{descriptor.modelId}: declaring group differs from the protocol descriptor"
  let field ← findUnique s!"field {descriptor.fieldId}" model.fields
    (·.id == descriptor.fieldId)
  if field.path != fieldPath descriptor then
    throw s!"{descriptor.modelId}: selected field path differs from the protocol descriptor"
  match field.kind with
  | .number scale signed =>
      if scale != descriptor.scale || signed != descriptor.signed then
        throw s!"{descriptor.modelId}: selected Number kind differs from the protocol descriptor"
  | _ => throw s!"{descriptor.modelId}: selected protocol field is not Number"
  let rule ← findUnique s!"rule '{descriptor.ruleCode}'" model.rules
    (·.code == descriptor.ruleCode)
  if rule.name != descriptor.ruleName || rule.errorFieldId != descriptor.fieldId ||
      rule.errorPointer != firstRowPointer descriptor then
    throw s!"{descriptor.modelId}: selected rule identity or route differs from the protocol descriptor"
  if rule.condition != .numberNotEqual descriptor.fieldId descriptor.literal then
    throw s!"{descriptor.modelId}: selected rule condition differs from the protocol descriptor"
  pure (model, field, rule)

private def bindCase (descriptor : Descriptor) (bundle : Bundle) (model : ModelSpec) :
    Except String CaseSpec := do
  let case ← findUnique s!"case '{descriptor.retainedCaseId}'" bundle.cases
    (·.id == descriptor.retainedCaseId)
  if case.modelId != model.id then
    throw s!"{case.id}: selected case names model '{case.modelId}'"
  if !case.hasContent then
    throw s!"{case.id}: directional protocol case must be content-bearing"
  let cell ← findUnique s!"{case.id} field {descriptor.fieldId}" case.cells
    (·.fieldId == descriptor.fieldId)
  if cell.state != .empty then
    throw s!"{case.id}: selected Number cell is not empty"
  pure case

private def bindObservation (descriptor : Descriptor) (bundle : Bundle) (model : ModelSpec)
    (case : CaseSpec) (observation : Observation) : Except String Unit := do
  if observation.id != case.id || observation.kernelVersion != bundle.kernelVersion ||
      observation.modelRef != model.modelRef || observation.operation != "validateFull" ||
      !observation.divergences.isEmpty then
    throw s!"{case.id}: retained observation identity or operation differs from the projection"
  let groupPath := absolutePath descriptor.groupPath
  discard <| findUnique s!"{case.id} group placement" observation.placements fun placement =>
    placement == { kind := "GROUP", path := groupPath, reps := [1], value := none }
  discard <| findUnique s!"{case.id} content placement" observation.placements fun placement =>
    placement == {
      kind := "FIELD"
      path := groupPath ++ "/" ++ descriptor.contentFieldName
      reps := [1, 1]
      value := some descriptor.contentValue }
  discard <| findUnique s!"{case.id} empty Number placement" observation.placements fun placement =>
    placement == {
      kind := "EMPTY"
      path := absolutePath (fieldPath descriptor)
      reps := [1, 1]
      value := none }

private def capturedVerdict (descriptor : Descriptor) (signatures : List String) :
    Except String Verdict := do
  let parsed ← signatures.mapM MessageSignature.parse
  let focused := parsed.filter (·.code == descriptor.ruleCode)
  let signature ← match focused with
    | [signature] => pure signature
    | [] => throw s!"{descriptor.retainedCaseId}: complete strategy signatures omit '{descriptor.ruleCode}'"
    | _ => throw s!"{descriptor.retainedCaseId}: complete strategy signatures duplicate '{descriptor.ruleCode}'"
  if signature.pointer != firstRowPointer descriptor then
    throw s!"{descriptor.retainedCaseId}: focused signature routes to '{signature.pointer}'"
  let polarity := match signature.polarity with
    | .value => Polarity.value
    | .omission => Polarity.omission
  if polarity != descriptor.expectedPolarity then
    throw s!"{descriptor.retainedCaseId}: focused polarity {repr polarity} differs from the required lineage witness"
  pure (.fired polarity)

private def requestJson (descriptor : Descriptor) (field : FieldSpec) (case : CaseSpec) : Json :=
  Json.mkObj [
    ("protocolVersion", toJson Support.protocolVersion),
    ("kernelBehaviorVersion", toJson Support.kernelBehaviorVersion),
    ("operation", toJson Support.Operation.flatValidationEvaluateFull.tag),
    ("model", Json.mkObj [
      ("fieldRefByShortNameAllowed", toJson false),
      ("repeatableGroups", toJson ([] : List Json)),
      ("fields", Json.arr #[Json.mkObj [
        ("id", toJson field.id),
        ("groupPath", toJson field.groups),
        ("name", toJson field.name),
        ("kind", Json.mkObj [
          ("tag", toJson "number"),
          ("scale", toJson descriptor.scale),
          ("signed", toJson descriptor.signed)]),
        ("repeatableScope", toJson ([] : List Nat))]])]),
    ("declaringGroup", toJson descriptor.groupPath),
    ("condition", Json.mkObj [
      ("tag", toJson "compare"),
      ("operator", toJson "notEqual"),
      ("field", Json.mkObj [
        ("base", toJson "absolute"),
        ("groups", toJson descriptor.groupPath),
        ("field", toJson descriptor.fieldName)]),
      ("literal", Json.mkObj [
        ("tag", toJson "number"),
        ("value", toJson (toString descriptor.literal))])]),
    ("cells", Json.arr #[]),
    ("hasContent", toJson case.hasContent)]

/-- Derived protocol association for the directional Number case. -/
structure CaseArtifact where
  request : Json
  response : Json

def CaseArtifact.suiteCaseJson (_artifact : CaseArtifact)
    (descriptor : Descriptor := descriptor) : Json :=
  Json.mkObj [
    ("id", toJson descriptor.suiteCaseId),
    ("request", toJson descriptor.request.toString),
    ("expectedResponse", toJson descriptor.response.toString),
    ("evidence", Json.mkObj [
      ("kind", toJson "kernelRuntimeObservation"),
      ("projection", toJson descriptor.suiteProjection.toString),
      ("caseId", toJson descriptor.retainedCaseId),
      ("externalSupports", toJson "verdictFiringAndPolarity"),
      ("expectedResponseSource", toJson "retainedProjection")]),
    ("covers", toJson descriptor.covers)]

private def buildArtifact (descriptor : Descriptor) (bundle : Bundle)
    (receipt : CaptureReceipt) (observation : Observation) : Except String CaseArtifact := do
  descriptor.validate
  bundle.validate
  let (model, field, _rule) ← bindModel descriptor bundle
  let case ← bindCase descriptor bundle model
  bindObservation descriptor bundle model case observation
  if receipt.schemaVersion != 1 || receipt.kernelVersion != bundle.kernelVersion ||
      receipt.sourceRevision != bundle.sourceRevision || receipt.operation != "validateFull" then
    throw "operator protocol capture identity differs from its projection"
  let captureCase ← findUnique s!"capture case '{case.id}'" receipt.cases (·.id == case.id)
  if captureCase.caseSha256 != case.caseSha256 then
    throw s!"{case.id}: capture case digest differs from the projection"
  let signatures ← captureCase.completeSignatures
  if observation.expected != signatures then
    throw s!"{case.id}: retained observation differs from the complete strategy signatures"
  let verdict ← capturedVerdict descriptor signatures
  pure {
    request := requestJson descriptor field case
    response := Response.asJson (.verdict verdict) }

private def readEvidenceJson (path : System.FilePath) : IO Json := do
  let content ← IO.FS.readFile path
  match StrictJson.parseEvidence content with
  | .ok json => pure json
  | .error error => throw (IO.userError s!"{path}: invalid JSON: {repr error}")

private def readProtocolJson (path : System.FilePath) : IO Json := do
  let content ← IO.FS.readFile path
  match StrictJson.parse content with
  | .ok json => pure json
  | .error error => throw (IO.userError s!"{path}: invalid JSON: {repr error}")

private def orThrow (context : String) : Except String α → IO α
  | .ok value => pure value
  | .error message => throw (IO.userError s!"{context}: {message}")

private def checkDigest (context : String) (path : System.FilePath) (expected : String) : IO Unit := do
  let actual ← A12Kernel.Process.Sha256.file path
  if actual != expected then
    throw (IO.userError s!"{context}: SHA-256 is {actual}, expected {expected}")

private def findSuiteCase (descriptor : Descriptor) (suite : Json) : Except String Json := do
  let cases : List Json ← member suite "cases"
  let matching ← cases.filterM fun case => do
    let id : String ← member case "id"
    pure (id == descriptor.suiteCaseId)
  findUnique s!"suite case '{descriptor.suiteCaseId}'" matching fun _ => true

private def expectRejected (label : String) (result : Except String CaseArtifact) : Except String Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw s!"operator protocol mutation guard accepted {label}"

private def validateAssociation (descriptor : Descriptor) (artifact : CaseArtifact)
    (request response suiteCase : Json) : Except String Unit := do
  if request != artifact.request then
    throw "normalized request differs from the typed operator bridge"
  if response != artifact.response then
    throw "normalized response differs from the typed operator bridge"
  if suiteCase != artifact.suiteCaseJson descriptor then
    throw "suite case differs from the typed operator bridge"

private def expectAssociationRejected (label : String) (result : Except String Unit) :
    Except String Unit :=
  match result with
  | .error _ => pure ()
  | .ok () => throw s!"operator protocol association guard accepted {label}"

private def replaceSignaturePolarity (signature : String) : String :=
  if signature.startsWith (descriptor.ruleCode ++ "|") then
    signature.replace "|VALUE_ERROR|" "|OMISSION_ERROR|"
  else signature

private def checkMutationGuards (bundle : Bundle) (receipt : CaptureReceipt)
    (observation : Observation) (artifact : CaseArtifact) : Except String Unit := do
  expectRejected "a wrong rule"
    (buildArtifact { descriptor with ruleCode := "NUM_UNSIGNED_NE_POS" } bundle receipt observation)
  expectRejected "a wrong field path"
    (buildArtifact { descriptor with fieldName := "Quantity" } bundle receipt observation)
  expectRejected "a wrong retained case"
    (buildArtifact { descriptor with retainedCaseId := "number-directional-filled-zero" }
      bundle receipt observation)
  let changedSignatures := observation.expected.map replaceSignaturePolarity
  let changedCases := receipt.cases.map fun case =>
    if case.id == descriptor.retainedCaseId then
      { case with
        groovyDynamic := changedSignatures
        javaStatic := changedSignatures
        interpreter := changedSignatures }
    else case
  expectRejected "a wrong retained polarity"
    (buildArtifact descriptor bundle { receipt with cases := changedCases }
      { observation with expected := changedSignatures })
  let duplicatedSignatures :=
    (observation.expected ++ [observation.expected.headD ""]).mergeSort
  let duplicateCases := receipt.cases.map fun case =>
    if case.id == descriptor.retainedCaseId then
      { case with
        groovyDynamic := duplicatedSignatures
        javaStatic := duplicatedSignatures
        interpreter := duplicatedSignatures }
    else case
  expectRejected "a duplicate retained signature"
    (buildArtifact descriptor bundle { receipt with cases := duplicateCases }
      { observation with expected := duplicatedSignatures })
  let canonicalCase ←
    findUnique "canonical retained case" bundle.cases (·.id == descriptor.retainedCaseId)
  let replacedCase ← match bundle.cases.find? (·.id != descriptor.retainedCaseId) with
    | some case => pure case
    | none => throw "operator protocol mutation setup has no distinct retained case"
  let duplicateIdentityCase := { canonicalCase with
    caseRef := replacedCase.caseRef
    caseSha256 := replacedCase.caseSha256 }
  let duplicateBundle := { bundle with cases := bundle.cases.map fun case =>
    if case.id == replacedCase.id then duplicateIdentityCase else case }
  expectRejected "a duplicate retained case id"
    (buildArtifact descriptor duplicateBundle receipt observation)
  let wrongStrategyCases := receipt.cases.map fun case =>
    if case.id == descriptor.retainedCaseId then { case with interpreter := [] } else case
  expectRejected "an incomplete strategy signature association"
    (buildArtifact descriptor bundle { receipt with cases := wrongStrategyCases } observation)
  let wrongPointerSignatures := observation.expected.map fun signature =>
    if signature.startsWith (descriptor.ruleCode ++ "|") then
      signature.replace (firstRowPointer descriptor) "/Order[1]/WrongField"
    else signature
  let wrongPointerCases := receipt.cases.map fun case =>
    if case.id == descriptor.retainedCaseId then
      { case with
        groovyDynamic := wrongPointerSignatures
        javaStatic := wrongPointerSignatures
        interpreter := wrongPointerSignatures }
    else case
  expectRejected "a misrouted focused signature"
    (buildArtifact descriptor bundle { receipt with cases := wrongPointerCases }
      { observation with expected := wrongPointerSignatures })
  let requestCondition ← artifact.request.getObjVal? "condition"
  let requestField ← requestCondition.getObjVal? "field"
  let wrongPathRequest := artifact.request.setObjVal! "condition"
    (requestCondition.setObjVal! "field"
      (requestField.setObjVal! "field" (toJson "WrongPath")))
  expectAssociationRejected "a wrong normalized request path"
    (validateAssociation descriptor artifact wrongPathRequest artifact.response
      (artifact.suiteCaseJson descriptor))
  let wrongContentRequest := artifact.request.setObjVal! "hasContent" (toJson false)
  expectAssociationRejected "a wrong normalized row-content flag"
    (validateAssociation descriptor artifact wrongContentRequest artifact.response
      (artifact.suiteCaseJson descriptor))

/-- Load and derive the one operator-sensitive protocol artifact from retained bytes. -/
def loadArtifact (descriptor : Descriptor := descriptor) : IO CaseArtifact := do
  let bundle ← orThrow descriptor.projection.toString
    (Bundle.fromJson (← readEvidenceJson descriptor.projection))
  orThrow descriptor.projection.toString bundle.validate
  let root : System.FilePath := "evidence/kernel-30.8.1"
  let capturePath := root / bundle.captureRef
  checkDigest "operator protocol capture" capturePath bundle.captureSha256
  let receipt ← orThrow capturePath.toString
    (CaptureReceipt.fromJson (← readEvidenceJson capturePath))
  let model ← orThrow descriptor.modelId
    (findUnique s!"model '{descriptor.modelId}'" bundle.models (·.id == descriptor.modelId))
  checkDigest descriptor.modelId (root / model.modelRef) model.modelSha256
  let case ← orThrow descriptor.retainedCaseId
    (findUnique s!"case '{descriptor.retainedCaseId}'" bundle.cases
      (·.id == descriptor.retainedCaseId))
  checkDigest descriptor.retainedCaseId (root / case.caseRef) case.caseSha256
  let observation ← orThrow case.caseRef
    (Observation.fromJson (← readEvidenceJson (root / case.caseRef)))
  orThrow descriptor.suiteCaseId (buildArtifact descriptor bundle receipt observation)

/-- Check fixture and suite bytes plus adversarial bridge mutations. -/
def checkArtifacts : IO Nat := do
  let bundle ← orThrow descriptor.projection.toString
    (Bundle.fromJson (← readEvidenceJson descriptor.projection))
  orThrow descriptor.projection.toString bundle.validate
  let root : System.FilePath := "evidence/kernel-30.8.1"
  let receipt ← orThrow bundle.captureRef
    (CaptureReceipt.fromJson (← readEvidenceJson (root / bundle.captureRef)))
  let case ← orThrow descriptor.retainedCaseId
    (findUnique s!"case '{descriptor.retainedCaseId}'" bundle.cases
      (·.id == descriptor.retainedCaseId))
  let observation ← orThrow case.caseRef
    (Observation.fromJson (← readEvidenceJson (root / case.caseRef)))
  let artifact ← loadArtifact descriptor
  orThrow descriptor.suiteCaseId (checkMutationGuards bundle receipt observation artifact)
  let actualRequest ← readProtocolJson descriptor.request
  let actualResponse ← readProtocolJson descriptor.response
  let suiteCase ← orThrow descriptor.suiteCaseId
    (findSuiteCase descriptor (← readProtocolJson descriptor.suite))
  orThrow descriptor.suiteCaseId
    (validateAssociation descriptor artifact actualRequest actualResponse suiteCase)
  pure 1

end A12Kernel.Evidence.OperatorEmpty.ProtocolBridge
