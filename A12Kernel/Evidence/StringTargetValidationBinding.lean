import A12Kernel.Evidence.AuthoringIdentifier
import A12Kernel.Evidence.StringTargetValidationReplay
import A12Kernel.Process.Sha256
import A12Kernel.Reference.StrictJson

/-! # A12Kernel.Evidence.StringTargetValidationBinding — retained target-validation packet binding

This IO-only gate binds the input projection to exact retained model, case, and capture bytes. It checks the Groovy dynamic kernel anchor, Java static confirmation, and a12-dmkits interpreter triangulation separately. Exact external `absent` versus present-`empty` application tags are checked against the narrow core transition without broadening the retained case matrix.
-/

namespace A12Kernel.Evidence.StringTargetValidation.Binding

open Lean
open A12Kernel
open A12Kernel.Evidence.StringTargetValidation

private structure Placement where
  kind : String
  path : String
  reps : List Nat
  value : Option String
  deriving Repr, DecidableEq

private structure AppliedState where
  tag : String
  value : Option String
  deriving Repr, DecidableEq

private structure Observation where
  id : String
  kernelVersion : String
  source : String
  sections : List String
  tags : List String
  scenario : String
  modelRef : String
  operation : String
  placements : List Placement
  computeExpected : List String
  applyExpected : AppliedState
  deriving Repr, DecidableEq

private structure CleanResult where
  pointer : String
  value : String
  changed : Bool
  deriving Repr, DecidableEq

private structure ErroredResult where
  pointer : String
  value : String
  errorCode : String
  errorPointer : String
  deriving Repr, DecidableEq

private structure KernelStrategy where
  clean : List CleanResult
  errored : List ErroredResult
  cleared : List String
  operandErrors : List String
  appliedTarget : AppliedState
  deriving Repr, DecidableEq

private structure InterpreterResult where
  raw : List String
  projected : List String
  appliedTarget : AppliedState
  deriving Repr, DecidableEq

private structure CaptureCase where
  id : String
  modelId : String
  caseSha256 : String
  groovyDynamic : KernelStrategy
  javaStatic : KernelStrategy
  interpreter : InterpreterResult
  interpreterAgreesWithKernelDelta : Bool
  interpreterAgreesWithKernelStoredApply : Bool
  deriving Repr, DecidableEq

private structure CaptureLengthPolicy where
  minLength : Option Nat
  maxLength : Option Nat
  deriving Repr, DecidableEq

private structure CaptureModel where
  id : String
  sha256 : String
  bytes : Nat
  operation : String
  lengthPolicy : CaptureLengthPolicy
  operationShape : String
  consistencyNotifications : List Json

private structure HarnessArtifact where
  path : String
  sha256 : String
  deriving Repr, DecidableEq

private structure DisposableHarness where
  captureTest : HarnessArtifact
  runtimeLaws : HarnessArtifact
  deriving Repr, DecidableEq

private structure RuntimeDescriptor where
  javaVersion : String
  javaVendor : String
  gradleDistribution : String
  deriving Repr, DecidableEq

private structure Triangulation where
  strategy : String
  role : String
  deriving Repr, DecidableEq

private structure RequiredEnvironment where
  names : List String
  captureLabel : String
  sourceRevision : String
  captureTestSha256 : String
  runtimeLawsSha256 : String
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
  disposableHarness : DisposableHarness
  runtime : RuntimeDescriptor
  normalizedCaptureCommand : String
  requiredEnvironment : RequiredEnvironment
  computationName : String
  computationTarget : String
  models : List CaptureModel
  cases : List CaptureCase

private structure RetainedField where
  id : String
  name : String
  kind : String
  minLength : Option Nat
  maxLength : Option Nat
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

private def member [FromJson α] (json : Json) (name : String) : Except String α := do
  fromJson? (← json.getObjVal? name)

private def nullableMember [FromJson α] (json : Json) (name : String) : Except String (Option α) := do
  match ← json.getObjVal? name with
  | .null => pure none
  | value => some <$> fromJson? value

private def optionalString (json : Json) (name : String) : Except String (Option String) :=
  match json.getObjVal? name with
  | .ok .null => pure none
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
  !reference.isEmpty && !reference.startsWith "/" && !(reference.splitOn "/").contains ".."

private def basename (reference : String) : String :=
  (reference.splitOn "/").getLast?.getD ""

private def findUnique (context : String) (values : List α) (predicate : α → Bool) :
    Except String α :=
  match values.filter predicate with
  | [value] => pure value
  | [] => throw s!"{context}: no exact match"
  | _ => throw s!"{context}: duplicate matches"

private def Placement.fromJson (context : String) (json : Json) : Except String Placement := do
  let kind : String ← member json "kind"
  match kind with
  | "GROUP" => requireExactMembers context json ["kind", "path", "reps"]
  | "FIELD" => requireExactMembers context json ["kind", "path", "reps", "value"]
  | other => throw s!"{context}: unsupported placement kind '{other}'"
  pure {
    kind
    path := ← member json "path"
    reps := ← member json "reps"
    value := ← optionalString json "value" }

private def AppliedState.fromJson (context : String) (json : Json) : Except String AppliedState := do
  requireExactMembers context json ["tag", "value"]
  let result : AppliedState := {
    tag := ← member json "tag"
    value := ← nullableMember json "value" }
  match result.tag, result.value with
  | "absent", none | "empty", none => pure result
  | "string", some value =>
      if value.isEmpty then throw s!"{context}: a stored String must be nonempty"
      else pure result
  | _, _ => throw s!"{context}: invalid applied target state {repr result}"

private def Observation.fromJson (json : Json) : Except String Observation := do
  requireExactMembers "String target-validation case" json
    ["meta", "modelRef", "placements", "op", "computeExpected", "applyExpected"]
  let metadata ← json.getObjVal? "meta"
  requireExactMembers "String target-validation case metadata" metadata
    ["id", "kernelVersion", "source", "sections", "tags", "scenario"]
  let operation ← json.getObjVal? "op"
  requireExactMembers "String target-validation operation" operation ["kind"]
  let placements : List Json ← member json "placements"
  pure {
    id := ← member metadata "id"
    kernelVersion := ← member metadata "kernelVersion"
    source := ← member metadata "source"
    sections := ← member metadata "sections"
    tags := ← member metadata "tags"
    scenario := ← member metadata "scenario"
    modelRef := ← member json "modelRef"
    operation := ← member operation "kind"
    placements := ← placements.zipIdx.mapM fun entry =>
      Placement.fromJson s!"String target-validation placement {entry.2}" entry.1
    computeExpected := ← member json "computeExpected"
    applyExpected := ← AppliedState.fromJson "String target-validation applyExpected"
      (← json.getObjVal? "applyExpected") }

private def CleanResult.fromJson (context : String) (json : Json) : Except String CleanResult := do
  requireExactMembers context json ["pointer", "value", "changed"]
  pure {
    pointer := ← member json "pointer"
    value := ← member json "value"
    changed := ← member json "changed" }

private def ErroredResult.fromJson (context : String) (json : Json) : Except String ErroredResult := do
  requireExactMembers context json ["pointer", "value", "errorCode", "errorPointer"]
  pure {
    pointer := ← member json "pointer"
    value := ← member json "value"
    errorCode := ← member json "errorCode"
    errorPointer := ← member json "errorPointer" }

private def KernelStrategy.fromJson (context : String) (json : Json) : Except String KernelStrategy := do
  requireExactMembers context json ["clean", "errored", "cleared", "operandErrors", "appliedTarget"]
  let clean : List Json ← member json "clean"
  let errored : List Json ← member json "errored"
  pure {
    clean := ← clean.zipIdx.mapM fun entry => CleanResult.fromJson s!"{context}.clean[{entry.2}]" entry.1
    errored := ← errored.zipIdx.mapM fun entry => ErroredResult.fromJson s!"{context}.errored[{entry.2}]" entry.1
    cleared := ← member json "cleared"
    operandErrors := ← member json "operandErrors"
    appliedTarget := ← AppliedState.fromJson (context ++ ".appliedTarget")
      (← json.getObjVal? "appliedTarget") }

private def InterpreterResult.fromJson (json : Json) : Except String InterpreterResult := do
  requireExactMembers "String target-validation interpreter result" json ["raw", "projected", "appliedTarget"]
  pure {
    raw := ← member json "raw"
    projected := ← member json "projected"
    appliedTarget := ← AppliedState.fromJson "String target-validation interpreter appliedTarget"
      (← json.getObjVal? "appliedTarget") }

private def CaptureCase.fromJson (json : Json) : Except String CaptureCase := do
  requireExactMembers "String target-validation capture case" json [
    "id", "modelId", "caseSha256", "groovyDynamic", "javaStatic", "interpreter",
    "interpreterAgreesWithKernelDelta", "interpreterAgreesWithKernelStoredApply"]
  pure {
    id := ← member json "id"
    modelId := ← member json "modelId"
    caseSha256 := ← member json "caseSha256"
    groovyDynamic := ← KernelStrategy.fromJson "String target-validation Groovy strategy"
      (← json.getObjVal? "groovyDynamic")
    javaStatic := ← KernelStrategy.fromJson "String target-validation Java strategy"
      (← json.getObjVal? "javaStatic")
    interpreter := ← InterpreterResult.fromJson (← json.getObjVal? "interpreter")
    interpreterAgreesWithKernelDelta := ← member json "interpreterAgreesWithKernelDelta"
    interpreterAgreesWithKernelStoredApply := ← member json "interpreterAgreesWithKernelStoredApply" }

private def CaptureLengthPolicy.fromJson (json : Json) : Except String CaptureLengthPolicy := do
  requireExactMembers "String target-validation captured length policy" json ["minLength", "maxLength"]
  pure {
    minLength := ← nullableMember json "minLength"
    maxLength := ← nullableMember json "maxLength" }

private def CaptureModel.fromJson (json : Json) : Except String CaptureModel := do
  requireExactMembers "String target-validation capture model" json [
    "id", "sha256", "bytes", "operation", "lengthPolicy", "operationShape",
    "consistencyNotifications"]
  pure {
    id := ← member json "id"
    sha256 := ← member json "sha256"
    bytes := ← member json "bytes"
    operation := ← member json "operation"
    lengthPolicy := ← CaptureLengthPolicy.fromJson (← json.getObjVal? "lengthPolicy")
    operationShape := ← member json "operationShape"
    consistencyNotifications := ← member json "consistencyNotifications" }

private def HarnessArtifact.fromJson (context : String) (json : Json) : Except String HarnessArtifact := do
  requireExactMembers context json ["path", "sha256"]
  pure { path := ← member json "path", sha256 := ← member json "sha256" }

private def CaptureReceipt.fromJson (json : Json) : Except String CaptureReceipt := do
  requireExactMembers "String target-validation capture" json [
    "schemaVersion", "kernelVersion", "a12DmkitsRevision", "captureDate", "anchor",
    "confirmationStrategies", "triangulation", "operation", "modelValidation",
    "disposableHarness", "runtime", "normalizedCaptureCommand", "requiredEnvironment",
    "computation", "models", "cases"]
  let triangulation ← json.getObjVal? "triangulation"
  requireExactMembers "String target-validation triangulation" triangulation ["strategy", "role"]
  let harness ← json.getObjVal? "disposableHarness"
  requireExactMembers "String target-validation disposable harness" harness ["captureTest", "runtimeLaws"]
  let runtime ← json.getObjVal? "runtime"
  requireExactMembers "String target-validation runtime" runtime ["javaVersion", "javaVendor", "gradleDistribution"]
  let environment ← json.getObjVal? "requiredEnvironment"
  let computation ← json.getObjVal? "computation"
  requireExactMembers "String target-validation computation" computation ["name", "target"]
  let models : List Json ← member json "models"
  let cases : List Json ← member json "cases"
  pure {
    schemaVersion := ← member json "schemaVersion"
    kernelVersion := ← member json "kernelVersion"
    sourceRevision := ← member json "a12DmkitsRevision"
    captureDate := ← member json "captureDate"
    anchor := ← member json "anchor"
    confirmationStrategies := ← member json "confirmationStrategies"
    triangulation := {
      strategy := ← member triangulation "strategy"
      role := ← member triangulation "role" }
    operation := ← member json "operation"
    modelValidation := ← member json "modelValidation"
    disposableHarness := {
      captureTest := ← HarnessArtifact.fromJson "String target-validation capture-test harness"
        (← harness.getObjVal? "captureTest")
      runtimeLaws := ← HarnessArtifact.fromJson "String target-validation RuntimeLaws harness"
        (← harness.getObjVal? "runtimeLaws") }
    runtime := {
      javaVersion := ← member runtime "javaVersion"
      javaVendor := ← member runtime "javaVendor"
      gradleDistribution := ← member runtime "gradleDistribution" }
    normalizedCaptureCommand := ← member json "normalizedCaptureCommand"
    requiredEnvironment := {
      names := ← objectNames "String target-validation required environment" environment
      captureLabel := ← member environment "A12_CAPTURE_LABEL"
      sourceRevision := ← member environment "A12_DMKITS_REVISION"
      captureTestSha256 := ← member environment "A12_CAPTURE_TEST_SHA256"
      runtimeLawsSha256 := ← member environment "A12_RUNTIME_LAWS_SHA256" }
    computationName := ← member computation "name"
    computationTarget := ← member computation "target"
    models := ← models.mapM CaptureModel.fromJson
    cases := ← cases.mapM CaptureCase.fromJson }

private def RetainedField.fromJson (json : Json) : Except String RetainedField := do
  requireExactMembers "retained target-validation field" json ["type", "id", "name", "Field"]
  let elementType : String ← member json "type"
  if elementType != "Field" then
    throw s!"retained target-validation field has element type '{elementType}'"
  let body ← json.getObjVal? "Field"
  requireExactMembers "retained target-validation field body" body ["fieldType"]
  let fieldType ← body.getObjVal? "fieldType"
  let fieldTypeNames ← objectNames "retained target-validation field type" fieldType
  let kind : String ← member fieldType "type"
  if kind != "StringType" then
    throw s!"retained target-validation field has kind '{kind}'"
  let (minLength, maxLength) ←
    if sameInventory fieldTypeNames ["type"] then
      pure (none, none)
    else if sameInventory fieldTypeNames ["type", "StringType"] then do
      let constraints ← fieldType.getObjVal? "StringType"
      let constraintNames ← objectNames "retained target-validation String constraints" constraints
      if sameInventory constraintNames ["minLength"] then
        pure (some (← member constraints "minLength"), none)
      else if sameInventory constraintNames ["maxLength"] then
        pure (none, some (← member constraints "maxLength"))
      else
        throw "retained target-validation String field must carry exactly one admitted length bound"
    else
      throw "retained target-validation field type has unprojected members"
  pure {
    id := ← member json "id"
    name := ← member json "name"
    kind
    minLength
    maxLength }

private def RetainedComputation.fromJson (json : Json) : Except String RetainedComputation := do
  requireExactMembers "retained target-validation computation" json ["type", "id", "name", "Computation"]
  let elementType : String ← member json "type"
  if elementType != "Computation" then
    throw s!"retained target-validation computation has element type '{elementType}'"
  let body ← json.getObjVal? "Computation"
  requireExactMembers "retained target-validation computation body" body
    ["computedFieldRelPath", "computationAlternatives", "errorMessage"]
  let alternatives : List Json ← member body "computationAlternatives"
  for alternative in alternatives do
    requireExactMembers "retained target-validation computation alternative" alternative ["operation"]
  let messages : List Json ← member body "errorMessage"
  for message in messages do
    requireExactMembers "retained target-validation computation message" message ["locale", "text"]
  pure {
    id := ← member json "id"
    name := ← member json "name"
    targetRelPath := ← member body "computedFieldRelPath"
    operations := ← alternatives.mapM fun alternative => member alternative "operation" }

private def RetainedGroup.fromJson (json : Json) : Except String RetainedGroup := do
  requireExactMembers "retained target-validation group" json ["type", "id", "name", "Group"]
  let elementType : String ← member json "type"
  if elementType != "Group" then
    throw s!"retained target-validation root has type '{elementType}'"
  let body ← json.getObjVal? "Group"
  requireExactMembers "retained target-validation group body" body ["repeatability", "elements"]
  let elements : List Json ← member body "elements"
  let mut fields : List RetainedField := []
  let mut computations : List RetainedComputation := []
  for element in elements do
    let kind : String ← member element "type"
    match kind with
    | "Field" => fields := fields ++ [← RetainedField.fromJson element]
    | "Computation" => computations := computations ++ [← RetainedComputation.fromJson element]
    | other => throw s!"unsupported retained target-validation element type '{other}'"
  pure {
    id := ← member json "id"
    name := ← member json "name"
    repeatability := ← member body "repeatability"
    fields
    computations }

private def RetainedModel.fromJson (json : Json) : Except String RetainedModel := do
  requireExactMembers "retained target-validation model" json ["header", "content"]
  let header ← json.getObjVal? "header"
  requireExactMembers "retained target-validation header" header [
    "id", "modelType", "modelVersion", "locales", "labels", "annotations", "modelReferences"]
  let headerId : String ← member header "id"
  let modelType : String ← member header "modelType"
  let modelVersion : String ← member header "modelVersion"
  let locales : List Json ← member header "locales"
  for locale in locales do
    requireExactMembers "retained target-validation locale" locale ["code"]
  let labels : List Json ← member header "labels"
  let annotations : List Json ← member header "annotations"
  let references : List Json ← member header "modelReferences"
  if headerId != "lean-string-target-validation" || modelType != "document" ||
      modelVersion != "28.4.0" || locales.length != 1 ||
      (← member locales.head! "code") != "en_US" ||
      !labels.isEmpty || !annotations.isEmpty || !references.isEmpty then
    throw "retained target-validation header differs from the captured closed model"
  let content ← json.getObjVal? "content"
  requireExactMembers "retained target-validation content" content ["modelInfo", "modelConfig", "modelRoot"]
  let modelInfo ← content.getObjVal? "modelInfo"
  requireExactMembers "retained target-validation modelInfo" modelInfo
    ["name", "variant", "revision", "immutable"]
  let config ← content.getObjVal? "modelConfig"
  requireExactMembers "retained target-validation modelConfig" config
    ["decimalSeparator", "timeZone", "conditionLanguage", "fieldRefByShortNameAllowed"]
  let language ← config.getObjVal? "conditionLanguage"
  requireExactMembers "retained target-validation conditionLanguage" language ["code"]
  let root ← content.getObjVal? "modelRoot"
  requireExactMembers "retained target-validation modelRoot" root ["rootGroups"]
  let roots : List Json ← member root "rootGroups"
  let rootGroup ← match roots with
    | [rootGroup] => pure rootGroup
    | _ => throw "retained target-validation model must have exactly one root group"
  pure {
    conditionLanguage := ← member language "code"
    shortNamesAllowed := ← member config "fieldRefByShortNameAllowed"
    group := ← RetainedGroup.fromJson rootGroup }

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
  bundle.models.map (·.id)

private def expectedCaseIds (bundle : Bundle) : List String :=
  bundle.cases.map (·.id)

private def validateCaptureBasics (bundle : Bundle) (receipt : CaptureReceipt) : Except String Unit := do
  if receipt.schemaVersion != 1 || receipt.kernelVersion != bundle.kernelVersion ||
      receipt.sourceRevision != bundle.sourceRevision then
    throw "String target-validation capture compatibility identity differs from its projection"
  if receipt.captureDate != "2026-07-15" || receipt.anchor != "kernel-groovy-dynamic" ||
      receipt.confirmationStrategies != ["kernel-java-static"] || receipt.operation != "compute" ||
      receipt.modelValidation != "allAcceptedByKernelCheckConsistency" then
    throw "String target-validation capture provenance or model-validation posture is unsupported"
  if receipt.triangulation.strategy != "interpreter" ||
      receipt.triangulation.role != "knowledge source, not oracle" then
    throw "String target-validation interpreter is not classified solely as triangulation"
  if receipt.computationName != "StringTargetComp" || receipt.computationTarget != "../Target" then
    throw "String target-validation computation descriptor differs from the closed capsule"
  let expectedEnvironmentNames := [
    "A12_CAPTURE_LABEL", "A12_DMKITS_REVISION", "A12_CAPTURE_TEST_SHA256",
    "A12_RUNTIME_LAWS_SHA256"]
  if !sameInventory receipt.requiredEnvironment.names expectedEnvironmentNames ||
      receipt.requiredEnvironment.captureLabel != "build/lean-string-target-validation-capture" ||
      receipt.requiredEnvironment.sourceRevision != bundle.sourceRevision ||
      receipt.requiredEnvironment.captureTestSha256 != receipt.disposableHarness.captureTest.sha256 ||
      receipt.requiredEnvironment.runtimeLawsSha256 != receipt.disposableHarness.runtimeLaws.sha256 then
    throw "String target-validation normalized environment differs from its pinned harness inputs"
  if receipt.disposableHarness.captureTest.path !=
      "adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/StringTargetValidationPortableCaptureTest.kt" ||
      receipt.disposableHarness.runtimeLaws.path !=
        "adapter/src/test/java/io/github/mbackschat/a12/dm/adapter/laws/RuntimeLaws.java" ||
      !A12Kernel.Process.Sha256.isDigest receipt.disposableHarness.captureTest.sha256 ||
      !A12Kernel.Process.Sha256.isDigest receipt.disposableHarness.runtimeLaws.sha256 then
    throw "String target-validation disposable harness identity is invalid"
  if receipt.normalizedCaptureCommand !=
      "./build.sh :adapter:test --tests io.github.mbackschat.a12.dm.adapter.laws.StringTargetValidationPortableCaptureTest -PtestForks=1" then
    throw "String target-validation normalized capture command differs from the retained route"
  if receipt.runtime.javaVersion != "21.0.11" ||
      receipt.runtime.javaVendor != "Oracle Corporation" ||
      receipt.runtime.gradleDistribution !=
        "https\\://services.gradle.org/distributions/gradle-9.0.0-bin.zip" then
    throw "String target-validation runtime descriptor differs from the retained execution"
  if !sameInventory (receipt.models.map (·.id)) (expectedModelIds bundle) ||
      !sameInventory (receipt.cases.map (·.id)) (expectedCaseIds bundle) then
    throw "String target-validation capture inventory differs from its projection"

private def projectedPolicyPair : LengthPolicySpec → Option Nat × Option Nat
  | .minimum bound => (some bound, none)
  | .maximum bound => (none, some bound)

private def operationShape : OperationSpec → String
  | .copy => "copy"
  | .padded _ _ => "padded"

private def bindModel (projected : ModelSpec) (retained : RetainedModel) : Except String Unit := do
  if retained.conditionLanguage != "en_US" || !retained.shortNamesAllowed ||
      retained.group.id != "/Shipment" || retained.group.name != "Shipment" ||
      retained.group.repeatability != 1 then
    throw s!"{projected.id}: retained model configuration or declaring group differs from the closed projection"
  if retained.group.fields.length != 2 || retained.group.computations.length != 1 ||
      hasDuplicate (retained.group.fields.map (·.id)) then
    throw s!"{projected.id}: retained model must contain exactly Source, Target, and one computation"
  let source ← findUnique s!"{projected.id} Source" retained.group.fields
    (·.id == "/Shipment/Source")
  let target ← findUnique s!"{projected.id} Target" retained.group.fields
    (·.id == "/Shipment/Target")
  if source.name != "Source" || source.kind != "StringType" ||
      source.minLength.isSome || source.maxLength.isSome then
    throw s!"{projected.id}: retained Source is not the unconstrained String input"
  let expectedPolicy := projectedPolicyPair projected.policy
  if target.name != "Target" || target.kind != "StringType" ||
      (target.minLength, target.maxLength) != expectedPolicy then
    throw s!"{projected.id}: retained Target length policy differs from the positive single-bound projection"
  let computation ← findUnique s!"{projected.id} computation"
    retained.group.computations (fun _ => true)
  if computation.id != "/Shipment/StringTargetComp" || computation.name != "StringTargetComp" ||
      computation.targetRelPath != "../Target" ||
      computation.operations != [projected.operation.render] then
    throw s!"{projected.id}: retained computation identity, target, or operation differs from the projection"
  if !A12Kernel.Evidence.AuthoringIdentifier.safe source.name ||
      !A12Kernel.Evidence.AuthoringIdentifier.safe target.name ||
      !A12Kernel.Evidence.AuthoringIdentifier.safe computation.name then
    throw s!"{projected.id}: retained authoring identifiers are not safely renderable"

private def validateCaptureModel (projected : ModelSpec) (captured : CaptureModel) : Except String Unit := do
  let expectedPolicy := projectedPolicyPair projected.policy
  if captured.id != projected.id || captured.sha256 != projected.modelSha256 ||
      captured.bytes == 0 || captured.operation != projected.operation.render ||
      (captured.lengthPolicy.minLength, captured.lengthPolicy.maxLength) != expectedPolicy ||
      captured.operationShape != operationShape projected.operation ||
      !captured.consistencyNotifications.isEmpty then
    throw s!"{projected.id}: captured model metadata, operation, length policy, or consistency result differs from the projection"

private def expectedPlacements (case : CaseSpec) : List Placement :=
  let group : Placement := {
    kind := "GROUP", path := "/Shipment", reps := [1], value := none }
  let source : Placement := {
    kind := "FIELD", path := "/Shipment/Source", reps := [1, 1], value := some case.source }
  let target := match case.priorTarget with
    | .absent => []
    | .string value => [{
        kind := "FIELD", path := "/Shipment/Target", reps := [1, 1], value := some value }]
  [group, source] ++ target

private def AppliedState.normalizedValue (state : AppliedState) : Option String :=
  match state.tag with
  | "string" => state.value
  | _ => none

/-- Render the exact core state into the retained packet's three-state vocabulary. -/
private def AppliedState.fromCore : StringTargetState → AppliedState
  | .absent => { tag := "absent", value := none }
  | .presentEmpty => { tag := "empty", value := none }
  | .presentValue stored => { tag := "string", value := some stored.text }

/-- The closed target-validation packet admits only accepted and errored outcomes; their exact state is supplied by the core transition. -/
private def expectedExternalAppliedState (case : CaseSpec)
    (replay : ReplayResult) : Except String AppliedState :=
  match replay.outcome with
  | .accepted _ | .errored _ _ => pure <| AppliedState.fromCore replay.appliedState
  | .noValue | .poison _ =>
      throw s!"{case.id}: closed target-validation evidence unexpectedly produced no value or poison"

private def expectedKernelStrategy (bundle : Bundle) (case : CaseSpec)
    (replay : ReplayResult) : Except String KernelStrategy := do
  let appliedTarget ← expectedExternalAppliedState case replay
  match replay.outcome with
  | .accepted value =>
      let changed := match case.priorTarget with
        | .absent => true
        | .string previous => previous != value.text
      pure {
        clean := [{ pointer := bundle.targetPointer, value := value.text, changed }]
        errored := []
        cleared := []
        operandErrors := []
        appliedTarget }
  | .errored attempted cause =>
      let causeName := match cause with
        | .tooShort => "stringZuKurz"
        | .tooLong => "stringZuLang"
      pure {
        clean := []
        errored := [{
          pointer := bundle.targetPointer
          value := attempted.text
          errorCode := causeName
          errorPointer := bundle.targetPointer }]
        cleared := []
        operandErrors := []
        appliedTarget }
  | .noValue | .poison _ =>
      throw s!"{case.id}: closed target-validation evidence unexpectedly produced no value or poison"

private def expectedInterpreterRaw (bundle : Bundle) (case : CaseSpec)
    (replay : ReplayResult) : Except String (List String) :=
  match replay.outcome with
  | .accepted value => pure [s!"{bundle.targetPointer}|VALUE|{value.text}"]
  | .errored attempted _ => pure [s!"{bundle.targetPointer}|ERRORED|{attempted.text}"]
  | .noValue | .poison _ =>
      throw s!"{case.id}: closed target-validation evidence unexpectedly produced no value or poison"

/-- Remove only the kernel target-error cause to compare with a12-dmkits' deliberately less informative `ERRORED|attempted` triangulation signature. -/
private def normalizeKernelDelta (caseId : String) (signatures : List String) : Except String (List String) :=
  signatures.mapM fun signature =>
    match signature.splitOn "|" with
    | [pointer, "VALUE", value] => pure s!"{pointer}|VALUE|{value}"
    | [pointer, "ERRORED", attempted, _cause] => pure s!"{pointer}|ERRORED|{attempted}"
    | _ => throw s!"{caseId}: unsupported rich kernel delta '{signature}'"

private def validateObservation (bundle : Bundle) (model : ModelSpec) (case : CaseSpec)
    (observation : Observation) (replay : ReplayResult) : Except String Unit := do
  if observation.id != case.id || observation.kernelVersion != bundle.kernelVersion ||
      observation.source != "curated" || observation.sections != ["§3", "§11"] ||
      observation.tags != ["computation", "string", "target-validation", "errored", "apply"] ||
      observation.scenario != "a12-kernel-lean String target-validation capture" ||
      observation.modelRef != model.modelRef || observation.operation != "compute" then
    throw s!"{case.id}: retained observation identity, classification, or operation differs from the projection"
  if observation.placements != expectedPlacements case then
    throw s!"{case.id}: retained placements differ from the projected source and prior target"
  if observation.computeExpected != replay.delta then
    throw s!"{case.id}: retained rich delta {repr observation.computeExpected} differs from Lean {repr replay.delta}"
  let exactApplied ← expectedExternalAppliedState case replay
  if observation.applyExpected != exactApplied then
    throw s!"{case.id}: retained exact external application state differs from its captured prior-state rule"
  if observation.applyExpected.normalizedValue != replay.appliedValue then
    throw s!"{case.id}: external application state and Lean value-only application disagree"

private def validateCaptureCase (bundle : Bundle) (model : ModelSpec) (case : CaseSpec)
    (observation : Observation) (replay : ReplayResult) (captured : CaptureCase) : Except String Unit := do
  if captured.id != case.id || captured.modelId != model.id ||
      captured.caseSha256 != case.caseSha256 then
    throw s!"{case.id}: captured case identity differs from the projection"
  let expectedStrategy ← expectedKernelStrategy bundle case replay
  if captured.groovyDynamic != expectedStrategy || captured.javaStatic != captured.groovyDynamic ||
      captured.groovyDynamic.appliedTarget != observation.applyExpected then
    throw s!"{case.id}: rich Groovy anchor, Java confirmation, or retained exact application state disagree"
  let expectedRaw ← expectedInterpreterRaw bundle case replay
  let expectedProjected ← normalizeKernelDelta case.id observation.computeExpected
  let expectedInterpreterApply : AppliedState := match replay.appliedValue with
    | some value => { tag := "string", value := some value }
    | none => { tag := "empty", value := none }
  if captured.interpreter.raw != expectedRaw || captured.interpreter.projected != expectedProjected ||
      captured.interpreter.appliedTarget != expectedInterpreterApply then
    throw s!"{case.id}: interpreter raw, projected, or normalized application triangulation differs"
  let deltaAgreement := captured.interpreter.projected == expectedProjected
  let applyAgreement := captured.interpreter.appliedTarget.normalizedValue ==
    captured.groovyDynamic.appliedTarget.normalizedValue
  if captured.interpreterAgreesWithKernelDelta != deltaAgreement ||
      captured.interpreterAgreesWithKernelStoredApply != applyAgreement ||
      !deltaAgreement || !applyAgreement then
    throw s!"{case.id}: interpreter triangulation agreement flags are inconsistent"

private def expectRejected (context : String) (result : Except String α) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError s!"negative String target-validation lock accepted {context}")

private def checkDirectoryInventory (directory : System.FilePath)
    (expectedNames : List String) : IO Unit := do
  let entries ← directory.readDir
  let mut actualNames : List String := []
  for entry in entries do
    let metadata ← entry.path.symlinkMetadata
    if metadata.type != .file then
      throw (IO.userError s!"retained String target-validation path '{entry.path}' is not a regular file")
    actualNames := actualNames ++ [entry.fileName]
  if !sameInventory actualNames expectedNames then
    throw (IO.userError
      s!"retained String target-validation directory '{directory}' has stale, missing, or duplicate artifacts")

private def checkPacketInventory (root : System.FilePath) (bundle : Bundle) : IO Unit := do
  for model in bundle.models do
    if !safeRelative model.modelRef ||
        !model.modelRef.startsWith "models/lean-string-target-" then
      throw (IO.userError s!"{model.id}: unsafe or misrouted modelRef '{model.modelRef}'")
  for case in bundle.cases do
    if !safeRelative case.caseRef ||
        !case.caseRef.startsWith "cases/computation/string-target-validation-v1/" then
      throw (IO.userError s!"{case.id}: unsafe or misrouted caseRef '{case.caseRef}'")
  if !safeRelative bundle.captureRef ||
      !bundle.captureRef.startsWith "captures/string-target-validation-" then
    throw (IO.userError s!"unsafe or misrouted String target-validation captureRef '{bundle.captureRef}'")
  checkDirectoryInventory (root / "cases/computation/string-target-validation-v1")
    (bundle.cases.map (fun case => basename case.caseRef))

private def checkModel (root : System.FilePath) (receipt : CaptureReceipt)
    (projected : ModelSpec) : IO RetainedModel := do
  let path := root / projected.modelRef
  let content ← IO.FS.readFile path
  let digest ← A12Kernel.Process.Sha256.file path
  orThrow projected.id (requireDigest projected.id projected.modelSha256 digest)
  let captured ← orThrow projected.id <|
    findUnique s!"capture model '{projected.id}'" receipt.models (·.id == projected.id)
  orThrow projected.id (validateCaptureModel projected captured)
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
  let replay ← orThrow case.id (case.replay model bundle.targetPointer)
  orThrow case.id (validateObservation bundle model case observation replay)
  let captured ← orThrow case.id <|
    findUnique s!"capture case '{case.id}'" receipt.cases (·.id == case.id)
  orThrow case.id (validateCaptureCase bundle model case observation replay captured)

private def checkAdversarialLocks (root : System.FilePath) (bundle : Bundle)
    (receipt : CaptureReceipt) : IO Unit := do
  let errorCase ← orThrow "target-error lock" <|
    findUnique "max3 absent error case" bundle.cases (·.id == "max3-absent-errored")
  let errorModel ← orThrow errorCase.id (bundle.modelFor errorCase)
  let errorObservation ← orThrow errorCase.id <|
    Observation.fromJson (← readJson (root / errorCase.caseRef))
  let errorReplay ← orThrow errorCase.id <|
    errorCase.replay errorModel bundle.targetPointer
  let errorCapture ← orThrow errorCase.id <|
    findUnique "captured max3 absent error case" receipt.cases (·.id == errorCase.id)
  let changedErrors := errorCapture.groovyDynamic.errored.map fun result =>
    { result with errorCode := "stringZuKurz" }
  expectRejected "a changed target-error cause"
    (validateCaptureCase bundle errorModel errorCase errorObservation errorReplay {
      errorCapture with groovyDynamic := {
        errorCapture.groovyDynamic with errored := changedErrors } })
  let changedAttempts := errorCapture.groovyDynamic.errored.map fun result =>
    { result with value := "WXYZ" }
  expectRejected "a changed attempted target value"
    (validateCaptureCase bundle errorModel errorCase errorObservation errorReplay {
      errorCapture with groovyDynamic := {
        errorCapture.groovyDynamic with errored := changedAttempts } })
  let changedErrorPointers := errorCapture.groovyDynamic.errored.map fun result =>
    { result with errorPointer := "/Shipment[1]/Source" }
  expectRejected "a target error attached to the wrong pointer"
    (validateCaptureCase bundle errorModel errorCase errorObservation errorReplay {
      errorCapture with groovyDynamic := {
        errorCapture.groovyDynamic with errored := changedErrorPointers } })
  let changedResultPointers := errorCapture.groovyDynamic.errored.map fun result =>
    { result with pointer := "/Shipment[1]/Source" }
  expectRejected "an errored result emitted for the wrong target"
    (validateCaptureCase bundle errorModel errorCase errorObservation errorReplay {
      errorCapture with groovyDynamic := {
        errorCapture.groovyDynamic with errored := changedResultPointers } })
  let changedJavaErrors := errorCapture.javaStatic.errored.map fun result =>
    { result with errorCode := "stringZuKurz" }
  expectRejected "a Java confirmation strategy split from the Groovy anchor"
    (validateCaptureCase bundle errorModel errorCase errorObservation errorReplay {
      errorCapture with javaStatic := {
        errorCapture.javaStatic with errored := changedJavaErrors } })
  expectRejected "an absent target rewritten as present-empty"
    (validateObservation bundle errorModel errorCase {
      errorObservation with applyExpected := { tag := "empty", value := none } } errorReplay)
  let equalCase ← orThrow "changed-flag lock" <|
    findUnique "max4 equal case" bundle.cases (·.id == "max4-equal-unchanged")
  let equalModel ← orThrow equalCase.id (bundle.modelFor equalCase)
  let equalObservation ← orThrow equalCase.id <|
    Observation.fromJson (← readJson (root / equalCase.caseRef))
  let equalReplay ← orThrow equalCase.id <|
    equalCase.replay equalModel bundle.targetPointer
  let equalCapture ← orThrow equalCase.id <|
    findUnique "captured max4 equal case" receipt.cases (·.id == equalCase.id)
  let changedClean := equalCapture.groovyDynamic.clean.map fun result =>
    { result with changed := true }
  expectRejected "an unchanged accepted value marked changed"
    (validateCaptureCase bundle equalModel equalCase equalObservation equalReplay {
      equalCapture with groovyDynamic := {
        equalCapture.groovyDynamic with clean := changedClean } })
  expectRejected "an interpreter raw value mislabeled as a projected delta"
    (validateCaptureCase bundle equalModel equalCase equalObservation equalReplay {
      equalCapture with interpreter := {
        equalCapture.interpreter with projected := equalCapture.interpreter.raw } })
  expectRejected "an interpreter agreement flag inconsistent with the retained results"
    (validateCaptureCase bundle equalModel equalCase equalObservation equalReplay {
      equalCapture with interpreterAgreesWithKernelDelta := false })
  let retained ← checkModel root receipt errorModel
  let changedFields := retained.group.fields.map fun field =>
    if field.id == "/Shipment/Target" then
      { field with minLength := none, maxLength := some 4 }
    else field
  expectRejected "a retained target length bound changed independently of the projection"
    (bindModel errorModel { retained with group := { retained.group with fields := changedFields } })
  let changedComputations := retained.group.computations.map fun computation =>
    { computation with operations := computation.operations.map (· ++ " changed") }
  expectRejected "a retained computation operation changed independently of the projection"
    (bindModel errorModel {
      retained with group := { retained.group with computations := changedComputations } })
  expectRejected "an unpinned a12-dmkits revision"
    (validateCaptureBasics bundle {
      receipt with sourceRevision := "0000000000000000000000000000000000000000" })

private def absentState : AppliedState := { tag := "absent", value := none }
private def emptyState : AppliedState := { tag := "empty", value := none }

example : absentState != emptyState := by native_decide
example : absentState.normalizedValue = emptyState.normalizedValue := by native_decide

/-- Strictly bind and replay the complete retained String target-validation packet. -/
def checkArtifacts (root : System.FilePath) : IO Nat := do
  let projectionPath := root / "string-target-validation-projection.json"
  let bundle ← orThrow "string-target-validation-projection.json" <|
    Bundle.fromJson (← readJson projectionPath)
  orThrow "string-target-validation-projection.json" bundle.validate
  checkPacketInventory root bundle
  let capturePath := root / bundle.captureRef
  let captureDigest ← A12Kernel.Process.Sha256.file capturePath
  orThrow "String target-validation capture" <|
    requireDigest "String target-validation capture" bundle.captureSha256 captureDigest
  let receipt ← orThrow "String target-validation capture" <|
    CaptureReceipt.fromJson (← readJson capturePath)
  orThrow "String target-validation capture" (validateCaptureBasics bundle receipt)
  for model in bundle.models do
    discard <| checkModel root receipt model
  checkAdversarialLocks root bundle receipt
  for case in bundle.cases do
    checkCase root bundle receipt case
  pure bundle.cases.length

end A12Kernel.Evidence.StringTargetValidation.Binding
