import A12Kernel.Evidence.AuthoringIdentifier
import A12Kernel.Evidence.StringComputationReplay
import A12Kernel.Process.Sha256
import A12Kernel.Reference.StrictJson

/-! # A12Kernel.Evidence.StringComputationBinding — retained packet binding

This IO-only gate binds the first String-computation projection to its exact retained capture, model, and case bytes. The Groovy dynamic kernel route is the observation anchor and the Java static route confirms it. The a12-dmkits interpreter remains an explicitly classified triangulation source: its agreement and three intentional mismatches are checked, but it never supplies the expected result checked against Lean.
-/

namespace A12Kernel.Evidence.StringComputation.Binding

open Lean
open A12Kernel
open A12Kernel.Evidence.StringComputation

private structure Placement where
  kind : String
  path : String
  reps : List Nat
  value : Option String
  deriving Repr, DecidableEq

private structure Observation where
  id : String
  kernelVersion : String
  source : String
  modelRef : String
  operation : String
  placements : List Placement
  computeExpected : List String
  deriving Repr, DecidableEq

private structure RetainedField where
  id : String
  name : String
  kind : String
  deriving Repr, DecidableEq

private structure RetainedComputation where
  id : String
  name : String
  targetRelPath : String
  operations : List String
  deriving Repr, DecidableEq

private structure RetainedGroup where
  id : String
  name : String
  repeatability : Nat
  fields : List RetainedField
  computations : List RetainedComputation
  deriving Repr, DecidableEq

private structure RetainedModel where
  conditionLanguage : String
  shortNamesAllowed : Bool
  group : RetainedGroup
  deriving Repr, DecidableEq

private structure CaptureModel where
  id : String
  operation : String
  sha256 : String
  bytes : Nat
  consistencySeverityNames : List String
  consistencyNotificationStreamSha256 : String
  deriving Repr, DecidableEq

private structure CaptureCase where
  id : String
  modelId : String
  caseSha256 : String
  groovyDynamic : List String
  javaStatic : List String
  interpreterRaw : List String
  interpreterProjected : List String
  interpreterAgreesWithKernel : Bool
  deriving Repr, DecidableEq

private structure Triangulation where
  strategy : String
  role : String
  mismatchCaseIds : List String
  deriving Repr, DecidableEq

private structure RequiredEnvironment where
  names : List String
  captureDirectory : String
  sourceRevision : String
  harnessSha256 : String
  deriving Repr, DecidableEq

private structure CaptureReceipt where
  schemaVersion : Nat
  kernelVersion : String
  sourceRevision : String
  captureDate : String
  anchor : String
  confirmationStrategies : List String
  triangulation : Triangulation
  operation : String
  modelValidation : String
  disposableHarnessSha256 : String
  operationNormalizedModelShapeSha256 : String
  normalizedCaptureCommand : String
  requiredEnvironment : RequiredEnvironment
  computationName : String
  computationTarget : String
  models : List CaptureModel
  cases : List CaptureCase
  deriving Repr, DecidableEq

private def member [FromJson α] (json : Json) (name : String) : Except String α := do
  fromJson? (← json.getObjVal? name)

private def optionalString (json : Json) (name : String) : Except String (Option String) :=
  match json.getObjVal? name with
  | .ok value => some <$> fromJson? value
  | .error _ => pure none

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

private def safeRelative (reference : String) : Bool :=
  !reference.isEmpty && !reference.startsWith "/" &&
    !(reference.splitOn "/").contains ".."

private def basename (reference : String) : String :=
  (reference.splitOn "/").getLast?.getD ""

private def absolutePath (segments : List String) : String :=
  "/" ++ String.intercalate "/" segments

private def safeIdentifier (identifier : String) : Bool :=
  A12Kernel.Evidence.AuthoringIdentifier.safe identifier

private def projectedFieldPath (field : FieldSpec) : String :=
  absolutePath field.path

private def targetPlacementPath (model : ModelSpec) : Except String String := do
  pure <| projectedFieldPath (← model.findField model.targetFieldId)

private def findUnique (context : String) (values : List α) (predicate : α → Bool) :
    Except String α :=
  match values.filter predicate with
  | [value] => pure value
  | [] => throw s!"{context}: no exact match"
  | _ => throw s!"{context}: duplicate matches"

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
    source := ← member metadata "source"
    modelRef := ← member json "modelRef"
    operation := ← member operation "kind"
    placements := ← placements.mapM Placement.fromJson
    computeExpected := ← member json "computeExpected" }

private def RetainedField.fromJson (json : Json) : Except String RetainedField := do
  requireExactMembers "retained String field" json ["type", "id", "name", "Field"]
  let body ← json.getObjVal? "Field"
  requireExactMembers "retained String field body" body ["fieldType"]
  let fieldType ← body.getObjVal? "fieldType"
  requireExactMembers "retained String field type" fieldType ["type"]
  pure {
    id := ← member json "id"
    name := ← member json "name"
    kind := ← member fieldType "type" }

private def RetainedComputation.fromJson (json : Json) : Except String RetainedComputation := do
  requireExactMembers "retained String computation" json
    ["type", "id", "name", "Computation"]
  let body ← json.getObjVal? "Computation"
  requireExactMembers "retained String computation body" body
    ["computedFieldRelPath", "computationAlternatives", "errorMessage"]
  let alternatives : List Json ← member body "computationAlternatives"
  for alternative in alternatives do
    requireExactMembers "retained String computation alternative" alternative ["operation"]
  let messages : List Json ← member body "errorMessage"
  for message in messages do
    requireExactMembers "retained String computation message" message ["locale", "text"]
  pure {
    id := ← member json "id"
    name := ← member json "name"
    targetRelPath := ← member body "computedFieldRelPath"
    operations := ← alternatives.mapM fun alternative => member alternative "operation" }

private def RetainedGroup.fromJson (json : Json) : Except String RetainedGroup := do
  requireExactMembers "retained String-computation group" json ["type", "id", "name", "Group"]
  let elementType : String ← member json "type"
  if elementType != "Group" then
    throw s!"retained String-computation root has type '{elementType}'"
  let body ← json.getObjVal? "Group"
  requireExactMembers "retained String-computation group body" body
    ["repeatability", "elements"]
  let elements : List Json ← member body "elements"
  let mut fields : List RetainedField := []
  let mut computations : List RetainedComputation := []
  for element in elements do
    let kind : String ← member element "type"
    match kind with
    | "Field" => fields := fields ++ [← RetainedField.fromJson element]
    | "Computation" => computations := computations ++ [← RetainedComputation.fromJson element]
    | other => throw s!"unsupported retained String-computation element type '{other}'"
  pure {
    id := ← member json "id"
    name := ← member json "name"
    repeatability := ← member body "repeatability"
    fields
    computations }

private def RetainedModel.fromJson (json : Json) : Except String RetainedModel := do
  requireExactMembers "retained String-computation model" json ["header", "content"]
  let content ← json.getObjVal? "content"
  requireExactMembers "retained String-computation content" content
    ["modelInfo", "modelConfig", "modelRoot"]
  let config ← content.getObjVal? "modelConfig"
  requireExactMembers "retained String-computation modelConfig" config
    ["decimalSeparator", "timeZone", "conditionLanguage", "fieldRefByShortNameAllowed"]
  let language ← config.getObjVal? "conditionLanguage"
  requireExactMembers "retained String-computation conditionLanguage" language ["code"]
  let root ← content.getObjVal? "modelRoot"
  requireExactMembers "retained String-computation modelRoot" root ["rootGroups"]
  let roots : List Json ← member root "rootGroups"
  let rootGroup ← match roots with
    | [rootGroup] => pure rootGroup
    | _ => throw "retained String-computation model must have exactly one root group"
  pure {
    conditionLanguage := ← member language "code"
    shortNamesAllowed := ← member config "fieldRefByShortNameAllowed"
    group := ← RetainedGroup.fromJson rootGroup }

private def retainedRootElements (json : Json) : Except String (List Json) := do
  let content ← json.getObjVal? "content"
  let root ← content.getObjVal? "modelRoot"
  let groups : List Json ← member root "rootGroups"
  let group ← match groups with
    | [group] => pure group
    | _ => throw "retained String-computation model must have exactly one root group"
  let body ← group.getObjVal? "Group"
  member body "elements"

private def hasElementType (expected : String) (json : Json) : Bool :=
  match member json "type" with
  | .ok actual => actual == expected
  | .error _ => false

private def hasElementId (expected : String) (json : Json) : Bool :=
  match member json "id" with
  | .ok actual => actual == expected
  | .error _ => false

private def CaptureModel.fromJson (json : Json) : Except String CaptureModel := do
  let consistencySeverityCounts ← json.getObjVal? "consistencySeverityCounts"
  pure {
    id := ← member json "id"
    operation := ← member json "operation"
    sha256 := ← member json "sha256"
    bytes := ← member json "bytes"
    consistencySeverityNames := ← objectNames "consistencySeverityCounts" consistencySeverityCounts
    consistencyNotificationStreamSha256 :=
      ← member json "consistencyNotificationStreamSha256" }

private def CaptureCase.fromJson (json : Json) : Except String CaptureCase := do
  pure {
    id := ← member json "id"
    modelId := ← member json "modelId"
    caseSha256 := ← member json "caseSha256"
    groovyDynamic := ← member json "groovyDynamic"
    javaStatic := ← member json "javaStatic"
    interpreterRaw := ← member json "interpreterRaw"
    interpreterProjected := ← member json "interpreterProjected"
    interpreterAgreesWithKernel := ← member json "interpreterAgreesWithKernel" }

private def Triangulation.fromJson (json : Json) : Except String Triangulation := do
  pure {
    strategy := ← member json "strategy"
    role := ← member json "role"
    mismatchCaseIds := ← member json "mismatchCaseIds" }

private def RequiredEnvironment.fromJson (json : Json) : Except String RequiredEnvironment := do
  pure {
    names := ← objectNames "requiredEnvironment" json
    captureDirectory := ← member json "A12_CAPTURE_DIR"
    sourceRevision := ← member json "A12_DMKITS_REVISION"
    harnessSha256 := ← member json "A12_HARNESS_SHA256" }

private def CaptureReceipt.fromJson (json : Json) : Except String CaptureReceipt := do
  let triangulation ← json.getObjVal? "triangulation"
  let requiredEnvironment ← json.getObjVal? "requiredEnvironment"
  let computation ← json.getObjVal? "computation"
  let models : List Json ← member json "models"
  let cases : List Json ← member json "cases"
  pure {
    schemaVersion := ← member json "schemaVersion"
    kernelVersion := ← member json "kernelVersion"
    sourceRevision := ← member json "a12DmkitsRevision"
    captureDate := ← member json "captureDate"
    anchor := ← member json "anchor"
    confirmationStrategies := ← member json "confirmationStrategies"
    triangulation := ← Triangulation.fromJson triangulation
    operation := ← member json "operation"
    modelValidation := ← member json "modelValidation"
    disposableHarnessSha256 := ← member json "disposableHarnessSha256"
    operationNormalizedModelShapeSha256 :=
      ← member json "operationNormalizedModelShapeSha256"
    normalizedCaptureCommand := ← member json "normalizedCaptureCommand"
    requiredEnvironment := ← RequiredEnvironment.fromJson requiredEnvironment
    computationName := ← member computation "name"
    computationTarget := ← member computation "target"
    models := ← models.mapM CaptureModel.fromJson
    cases := ← cases.mapM CaptureCase.fromJson }

private def orThrow (context : String) : Except String α → IO α
  | .ok value => pure value
  | .error message => throw (IO.userError s!"{context}: {message}")

private def readJson (path : System.FilePath) : IO Json := do
  let metadata ← path.symlinkMetadata
  if metadata.type != .file then
    throw (IO.userError s!"retained artifact '{path}' is not a regular file")
  let content ← IO.FS.readFile path
  match A12Kernel.Reference.StrictJson.parseEvidence content with
  | .ok json => pure json
  | .error error => throw (IO.userError s!"{path}: {repr error}")

private def requireDigest (context expected actual : String) : Except String Unit := do
  if actual != expected then
    throw s!"{context}: retained SHA-256 is {actual}, expected {expected}"

private def expectedModelIds (bundle : Bundle) : List String :=
  bundle.models.map (fun model => model.id)

private def expectedCaseIds (bundle : Bundle) : List String :=
  bundle.cases.map (fun case => case.id)

private def validateRenderedIdentifiers (model : ModelSpec) : Except String Unit := do
  if model.declaringGroup.any (!safeIdentifier ·) ||
      model.fields.any (fun field => !safeIdentifier field.name) ||
      !safeIdentifier model.computationName then
    throw s!"{model.id}: projected authoring names are not conservative non-keyword ASCII identifiers"

private def validateCaptureBasics (bundle : Bundle) (receipt : CaptureReceipt) : Except String Unit := do
  if receipt.schemaVersion != 1 || receipt.kernelVersion != bundle.kernelVersion ||
      receipt.sourceRevision != bundle.sourceRevision then
    throw "String-computation capture compatibility identity differs from its projection"
  if receipt.captureDate != "2026-07-15" || receipt.anchor != "kernel-groovy-dynamic" ||
      receipt.confirmationStrategies != ["kernel-java-static"] ||
      receipt.operation != "compute" ||
      receipt.modelValidation != "allAcceptedByKernelCheckConsistency" then
    throw "String-computation capture provenance or model-validation posture is unsupported"
  if !A12Kernel.Process.Sha256.isDigest receipt.disposableHarnessSha256 ||
      !A12Kernel.Process.Sha256.isDigest receipt.operationNormalizedModelShapeSha256 then
    throw "String-computation capture has an invalid harness or normalized-shape digest"
  if receipt.triangulation.strategy != "interpreter" ||
      receipt.triangulation.role != "knowledge source, not oracle" then
    throw "String-computation interpreter is not classified solely as triangulation"
  let expectedEnvironmentNames := [
    "A12_CAPTURE_DIR", "A12_DMKITS_REVISION", "A12_HARNESS_SHA256"]
  if !sameInventory receipt.requiredEnvironment.names expectedEnvironmentNames ||
      receipt.requiredEnvironment.captureDirectory != "build/lean-string-computation-capture" ||
      receipt.requiredEnvironment.sourceRevision != bundle.sourceRevision ||
      receipt.requiredEnvironment.harnessSha256 != receipt.disposableHarnessSha256 then
    throw "String-computation normalized capture environment differs from its pinned inputs"
  if receipt.normalizedCaptureCommand !=
      "./build.sh :adapter:test --tests io.github.mbackschat.a12.dm.adapter.laws.StringComputationPortableCaptureTest -PtestForks=1" then
    throw "String-computation normalized capture command differs from the retained harness route"
  if !sameInventory (receipt.models.map (fun model => model.id)) (expectedModelIds bundle) ||
      !sameInventory (receipt.cases.map (fun case => case.id)) (expectedCaseIds bundle) then
    throw "String-computation capture model or case inventory differs from its projection"

private def bindModel (projected : ModelSpec) (retained : RetainedModel) : Except String Unit := do
  if retained.conditionLanguage != "en_US" || !retained.shortNamesAllowed then
    throw s!"{projected.id}: retained model language or short-name policy differs from the captured expression"
  if projected.declaringGroup.length != 1 then
    throw s!"{projected.id}: this evidence binding admits exactly one nonrepeatable declaring group"
  let groupPath := absolutePath projected.declaringGroup
  let expectedGroupName := projected.declaringGroup.getLast?.getD ""
  if retained.group.id != groupPath || retained.group.name != expectedGroupName ||
      retained.group.repeatability != 1 then
    throw s!"{projected.id}: retained declaring group differs from the typed projection"
  let expectedFieldIds := projected.fields.map projectedFieldPath
  let actualFieldIds := retained.group.fields.map (fun field => field.id)
  if !sameInventory actualFieldIds expectedFieldIds then
    throw s!"{projected.id}: retained four-String-field inventory differs from the typed projection"
  for field in projected.fields do
    let path := projectedFieldPath field
    let actual ← findUnique s!"{projected.id} field '{path}'" retained.group.fields
      (fun retainedField => retainedField.id == path)
    if actual.name != field.name || actual.kind != "StringType" then
      throw s!"{projected.id}: retained field '{path}' is not the projected String field"
  let computation ← match retained.group.computations with
    | [computation] => pure computation
    | _ => throw s!"{projected.id}: retained model must contain exactly one computation"
  let expectedComputationId := groupPath ++ "/" ++ projected.computationName
  let expectedOperation ← projected.expression.render projected
  if computation.id != expectedComputationId ||
      computation.name != projected.computationName ||
      computation.targetRelPath != projected.targetRelPath ||
      computation.operations != [expectedOperation] then
    throw s!"{projected.id}: retained computation identity, target, or operation differs from the typed projection"

private def validateCaptureModel (bundle : Bundle) (receipt : CaptureReceipt)
    (projected : ModelSpec) (captured : CaptureModel) : Except String Unit := do
  let expectedOperation ← projected.expression.render projected
  if captured.id != projected.id || captured.operation != expectedOperation ||
      captured.sha256 != projected.modelSha256 || captured.bytes == 0 then
    throw s!"{projected.id}: captured model identity, operation, or artifact metadata differs from the projection"
  if !captured.consistencySeverityNames.isEmpty ||
      captured.consistencyNotificationStreamSha256 !=
        "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855" then
    throw s!"{projected.id}: kernel consistency validation was not clean"
  if receipt.computationName != projected.computationName ||
      receipt.computationTarget != projected.targetRelPath ||
      receipt.sourceRevision != bundle.sourceRevision then
    throw s!"{projected.id}: capture computation descriptor differs from the projection"

private def expectedPlacements (model : ModelSpec) (case : CaseSpec) : Except String (List Placement) := do
  let groupPath := absolutePath model.declaringGroup
  let group : Placement := { kind := "GROUP", path := groupPath, reps := [1], value := none }
  let witness ← findUnique s!"{case.id} content witness" model.fields
    (fun field => field.name == "Witness")
  let content : List Placement := if case.hasContent then [{
    kind := "FIELD"
    path := projectedFieldPath witness
    reps := [1, 1]
    value := some "present" }] else []
  let cells ← case.cells.mapM fun cell => do
    let field ← model.findField cell.fieldId
    let path := projectedFieldPath field
    match cell.state with
    | .empty => pure { kind := "EMPTY", path, reps := [1, 1], value := none }
    | .string value => pure { kind := "FIELD", path, reps := [1, 1], value := some value }
  let priorTarget ← match case.priorTarget with
    | .empty => pure []
    | .string value => pure [{
        kind := "FIELD"
        path := ← targetPlacementPath model
        reps := [1, 1]
        value := some value }]
  pure <| [group] ++ content ++ cells ++ priorTarget

private def validateDeltaSignatures (caseId targetPointer : String)
    (allowEmptyValue : Bool) (signatures : List String) : Except String Unit := do
  if signatures.length > 1 || signatures != signatures.mergeSort || hasDuplicate signatures then
    throw s!"{caseId}: retained computation signatures are not one-outcome, canonical, and duplicate-free"
  for signature in signatures do
    match signature.splitOn "|" with
    | [pointer, "CLEARED"] | [pointer, "ERRORED"] =>
        if pointer != targetPointer then
          throw s!"{caseId}: retained computation signature targets '{pointer}'"
    | [pointer, "VALUE", value] =>
        if pointer != targetPointer || (!allowEmptyValue && value.isEmpty) then
          throw s!"{caseId}: retained VALUE signature is not a storable target value"
    | _ => throw s!"{caseId}: invalid retained computation signature '{signature}'"

/-- Reproduce the kernel-style delta granularity used only to compare the a12-dmkits interpreter as triangulation: unchanged values and clears of absent targets are silent, while changed values and errors remain visible. -/
private def projectInterpreterSignatures (case : CaseSpec) (targetPointer : String)
    (signatures : List String) : Except String (List String) := do
  let mut projected : List String := []
  for signature in signatures do
    match signature.splitOn "|" with
    | [pointer, "CLEARED"] =>
        if pointer != targetPointer then
          throw s!"{case.id}: interpreter CLEARED targets '{pointer}'"
        match case.priorTarget with
        | .empty => pure ()
        | .string _ => projected := projected ++ [signature]
    | [pointer, "ERRORED"] =>
        if pointer != targetPointer then
          throw s!"{case.id}: interpreter ERRORED targets '{pointer}'"
        projected := projected ++ [signature]
    | [pointer, "VALUE", value] =>
        if pointer != targetPointer then
          throw s!"{case.id}: interpreter VALUE targets '{pointer}'"
        match case.priorTarget with
        | .string previous =>
            if value != previous then projected := projected ++ [signature]
        | .empty => projected := projected ++ [signature]
    | _ => throw s!"{case.id}: invalid interpreter signature '{signature}'"
  pure projected

private def bindObservation (bundle : Bundle) (model : ModelSpec) (case : CaseSpec)
    (observation : Observation) : Except String Unit := do
  if observation.id != case.id || observation.kernelVersion != bundle.kernelVersion ||
      observation.source != "curated" || observation.modelRef != model.modelRef ||
      observation.operation != "compute" then
    throw s!"{case.id}: retained computation observation identity or operation differs from the projection"
  let placements ← expectedPlacements model case
  if observation.placements != placements then
    throw s!"{case.id}: retained placements {repr observation.placements} differ from projection {repr placements}"
  validateDeltaSignatures case.id model.targetPointer false observation.computeExpected

private def validateCaptureCase (model : ModelSpec) (case : CaseSpec)
    (observation : Observation) (captured : CaptureCase) : Except String Unit := do
  if captured.id != case.id || captured.modelId != model.id ||
      captured.caseSha256 != case.caseSha256 then
    throw s!"{case.id}: captured case identity differs from the projection"
  if captured.groovyDynamic != observation.computeExpected ||
      captured.javaStatic != captured.groovyDynamic then
    throw s!"{case.id}: Groovy kernel anchor, Java kernel confirmation, and retained observation disagree"
  validateDeltaSignatures case.id model.targetPointer false captured.groovyDynamic
  validateDeltaSignatures case.id model.targetPointer true captured.interpreterRaw
  validateDeltaSignatures case.id model.targetPointer true captured.interpreterProjected
  let derivedInterpreterProjection ←
    projectInterpreterSignatures case model.targetPointer captured.interpreterRaw
  if captured.interpreterProjected != derivedInterpreterProjection then
    throw s!"{case.id}: interpreter projection differs from the retained raw result and prior target"
  if captured.interpreterAgreesWithKernel !=
      (captured.interpreterProjected == captured.groovyDynamic) then
    throw s!"{case.id}: interpreter triangulation agreement flag is inconsistent"

private def expectedInterpreterMismatchIds : List String := [
  "all-empty-target-stale-content",
  "all-empty-target-absent-content",
  "all-empty-target-absent-empty-row"]

private def validateInterpreterMismatchSet (receipt : CaptureReceipt) : Except String Unit := do
  let derived := receipt.cases.filterMap fun case =>
    if case.interpreterAgreesWithKernel then none else some case.id
  if receipt.triangulation.mismatchCaseIds != expectedInterpreterMismatchIds ||
      derived != expectedInterpreterMismatchIds ||
      hasDuplicate receipt.triangulation.mismatchCaseIds then
    throw "String-computation interpreter triangulation mismatch set differs from the three retained all-empty cases"

private def expectRejected (context : String) (result : Except String α) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError s!"negative String-computation evidence lock accepted {context}")

private def checkDirectoryInventory (directory : System.FilePath)
    (expectedNames : List String) : IO Unit := do
  let entries ← directory.readDir
  let mut actualNames : List String := []
  for entry in entries do
    let metadata ← entry.path.symlinkMetadata
    if metadata.type != .file then
      throw (IO.userError s!"retained String-computation path '{entry.path}' is not a regular file")
    actualNames := actualNames ++ [entry.fileName]
  if !sameInventory actualNames expectedNames then
    throw (IO.userError
      s!"retained String-computation directory '{directory}' has stale, missing, or duplicate artifacts")

private def checkPacketInventory (root : System.FilePath) (bundle : Bundle) : IO Unit := do
  for model in bundle.models do
    if !safeRelative model.modelRef ||
        !model.modelRef.startsWith "models/lean-string-computation-" then
      throw (IO.userError s!"{model.id}: unsafe or misrouted modelRef '{model.modelRef}'")
  for case in bundle.cases do
    if !safeRelative case.caseRef ||
        !case.caseRef.startsWith "cases/computation/string-computation-v1/" then
      throw (IO.userError s!"{case.id}: unsafe or misrouted caseRef '{case.caseRef}'")
  if !safeRelative bundle.captureRef ||
      !bundle.captureRef.startsWith "captures/string-computation-" then
    throw (IO.userError s!"unsafe or misrouted String-computation captureRef '{bundle.captureRef}'")
  checkDirectoryInventory (root / "cases/computation/string-computation-v1")
    (bundle.cases.map (fun case => basename case.caseRef))

private def checkModel (root : System.FilePath) (bundle : Bundle)
    (receipt : CaptureReceipt) (projected : ModelSpec) : IO RetainedModel := do
  let path := root / projected.modelRef
  let content ← IO.FS.readFile path
  let digest ← A12Kernel.Process.Sha256.file path
  orThrow projected.id (requireDigest projected.id projected.modelSha256 digest)
  let captured ← orThrow projected.id <|
    findUnique s!"capture model '{projected.id}'" receipt.models
      (fun model => model.id == projected.id)
  orThrow projected.id (validateCaptureModel bundle receipt projected captured)
  if captured.bytes != content.utf8ByteSize then
    throw (IO.userError s!"{projected.id}: captured model byte size differs from retained bytes")
  let retained ← orThrow projected.id (RetainedModel.fromJson (← readJson path))
  orThrow projected.id (bindModel projected retained)
  pure retained

private def checkCase (root : System.FilePath) (bundle : Bundle)
    (receipt : CaptureReceipt) (case : CaseSpec) : IO Unit := do
  let model ← orThrow case.id (bundle.modelFor case)
  let path := root / case.caseRef
  let digest ← A12Kernel.Process.Sha256.file path
  orThrow case.id (requireDigest case.id case.caseSha256 digest)
  let observation ← orThrow case.id (Observation.fromJson (← readJson path))
  orThrow case.id (bindObservation bundle model case observation)
  let captured ← orThrow case.id <|
    findUnique s!"capture case '{case.id}'" receipt.cases
      (fun capturedCase => capturedCase.id == case.id)
  orThrow case.id (validateCaptureCase model case observation captured)
  let actual ← orThrow case.id (case.replay model)
  if actual != observation.computeExpected then
    throw (IO.userError
      s!"{case.id}: kernel observed {repr observation.computeExpected}, Lean derived {repr actual}")

private def checkAdversarialLocks (root : System.FilePath) (bundle : Bundle)
    (receipt : CaptureReceipt) : IO Unit := do
  let model ← match bundle.models with
    | model :: _ => pure model
    | [] => throw (IO.userError "String-computation binding lock requires a model")
  let retained ← checkModel root bundle receipt model
  let retainedJson ← readJson (root / model.modelRef)
  let elements ← orThrow model.id (retainedRootElements retainedJson)
  let retainedFieldJson ← orThrow model.id <|
    findUnique "retained String field for constraint lock" elements
      (hasElementId "/Shipment/Source")
  let fieldBody ← orThrow model.id (retainedFieldJson.getObjVal? "Field")
  let fieldType ← orThrow model.id (fieldBody.getObjVal? "fieldType")
  let constrainedField := retainedFieldJson.setObjVal! "Field"
    (fieldBody.setObjVal! "fieldType" (fieldType.setObjVal! "maxLength" (toJson 20)))
  expectRejected "an unprojected retained String field constraint"
    (RetainedField.fromJson constrainedField)
  let retainedComputationJson ← orThrow model.id <|
    findUnique "retained String computation for precondition lock" elements
      (hasElementType "Computation")
  let computationBody ← orThrow model.id (retainedComputationJson.getObjVal? "Computation")
  let conditionalComputation := retainedComputationJson.setObjVal! "Computation"
    (computationBody.setObjVal! "commonPrecondition" (toJson "True"))
  expectRejected "an unprojected retained computation precondition"
    (RetainedComputation.fromJson conditionalComputation)
  let changedComputations := retained.group.computations.map fun computation =>
    { computation with operations := computation.operations.map (fun operation => operation ++ " changed") }
  expectRejected "a changed retained computation operation"
    (bindModel model { retained with group := {
      retained.group with computations := changedComputations } })
  let renamedFields := retained.group.fields.map fun field =>
    { field with name := field.name ++ "Changed" }
  expectRejected "a retained String field rename"
    (bindModel model { retained with group := { retained.group with fields := renamedFields } })
  let unsafeFields := model.fields.map fun field =>
    if field.id == 1 then { field with name := "Source] + True" } else field
  expectRejected "an injected projected field identifier"
    (validateRenderedIdentifiers { model with fields := unsafeFields })
  let keywordFields := model.fields.map fun field =>
    if field.id == 1 then { field with name := "Length" } else field
  expectRejected "a keyword projected field identifier"
    (validateRenderedIdentifiers { model with fields := keywordFields })
  let case ← match bundle.cases with
    | case :: _ => pure case
    | [] => throw (IO.userError "String-computation binding lock requires a case")
  let caseModel ← orThrow case.id (bundle.modelFor case)
  let observation ← orThrow case.id
    (Observation.fromJson (← readJson (root / case.caseRef)))
  expectRejected "a changed content-witness placement"
    (bindObservation bundle caseModel { case with hasContent := !case.hasContent } observation)
  let captured ← orThrow case.id <|
    findUnique s!"capture case '{case.id}'" receipt.cases
      (fun capturedCase => capturedCase.id == case.id)
  expectRejected "a Java kernel confirmation disagreement"
    (validateCaptureCase caseModel case observation
      { captured with javaStatic := captured.javaStatic ++ ["/Shipment[1]/Target|CLEARED"] })
  let equalCase ← orThrow "interpreter projection lock" <|
    findUnique "direct filled target equality case" bundle.cases
      (fun candidate => candidate.id == "direct-filled-target-equal")
  let equalModel ← orThrow equalCase.id (bundle.modelFor equalCase)
  let equalObservation ← orThrow equalCase.id
    (Observation.fromJson (← readJson (root / equalCase.caseRef)))
  let equalCapture ← orThrow equalCase.id <|
    findUnique "captured direct filled target equality case" receipt.cases
      (fun candidate => candidate.id == equalCase.id)
  expectRejected "an interpreter raw result mislabeled as a projected delta"
    (validateCaptureCase equalModel equalCase equalObservation
      { equalCapture with interpreterProjected := equalCapture.interpreterRaw })
  expectRejected "an unpinned capture source revision"
    (validateCaptureBasics bundle { receipt with
      sourceRevision := "0000000000000000000000000000000000000000" })
  let changedFlags := receipt.cases.map fun capturedCase =>
    if capturedCase.id == expectedInterpreterMismatchIds.head?.getD "" then
      { capturedCase with interpreterAgreesWithKernel := true }
    else capturedCase
  expectRejected "an interpreter mismatch reclassified as agreement"
    (validateInterpreterMismatchSet { receipt with cases := changedFlags })

/-- Strictly bind and replay the complete retained String-computation packet. -/
def checkArtifacts (root : System.FilePath) : IO Nat := do
  let projectionPath := root / "string-computation-projection.json"
  let projectionJson ← readJson projectionPath
  let bundle ← orThrow "string-computation-projection.json"
    (Bundle.fromJson projectionJson)
  orThrow "string-computation-projection.json" bundle.validate
  for model in bundle.models do
    orThrow model.id (validateRenderedIdentifiers model)
  checkPacketInventory root bundle
  let capturePath := root / bundle.captureRef
  let captureDigest ← A12Kernel.Process.Sha256.file capturePath
  orThrow "String-computation capture"
    (requireDigest "String-computation capture" bundle.captureSha256 captureDigest)
  let receipt ← orThrow "String-computation capture"
    (CaptureReceipt.fromJson (← readJson capturePath))
  orThrow "String-computation capture" (validateCaptureBasics bundle receipt)
  orThrow "String-computation capture" (validateInterpreterMismatchSet receipt)
  for model in bundle.models do
    discard <| checkModel root bundle receipt model
  checkAdversarialLocks root bundle receipt
  for case in bundle.cases do
    checkCase root bundle receipt case
  pure bundle.cases.length

end A12Kernel.Evidence.StringComputation.Binding
