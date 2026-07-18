import A12Kernel.Evidence.CorrelationReplay
import A12Kernel.Evidence.CorrelationElaborationReplay
import A12Kernel.Evidence.Replay
import A12Kernel.Evidence.IterationReplay
import A12Kernel.Evidence.OperatorEmptyReplay
import A12Kernel.Evidence.OperatorProtocolBridge
import A12Kernel.Evidence.ObservationBundleTest
import A12Kernel.Evidence.StringComputationBinding
import A12Kernel.Evidence.StringCascadeProjection
import A12Kernel.Evidence.StringCascadeProjectionTest
import A12Kernel.Evidence.StringTargetValidationBinding
import A12Kernel.Process.Sha256
import A12Kernel.Reference.StrictJson
import Lean.Data.Json

/-! IO-only retained-kernel-evidence replay. This module is an executable boundary and
is intentionally absent from the library, conformance, and trusted theorem roots. -/

open Lean
open A12Kernel
open A12Kernel.Evidence

private structure Observation where
  id : String
  kernelVersion : String
  modelRef : String
  expected : List String
  divergences : List Json

private structure DiagnosticObservation where
  id : String
  kernelVersion : String
  modelRef : String
  expectedCode : String
  diagnosticCodes : List String

private structure CorrelationElaborationDiagnostic where
  severity : String
  source : String
  code : String
  rule : String
  deriving Repr, DecidableEq

private structure CorrelationElaborationObservation where
  id : String
  kernelVersion : String
  source : String
  capture : String
  modelRef : String
  draft : A12Kernel.Evidence.CorrelationElaboration.DraftSignature
  diagnostics : List CorrelationElaborationDiagnostic
  diagnosticCodes : List String

private inductive ObservedPolarity where
  | value
  | omission
  deriving Repr, DecidableEq

private structure MessageSignature where
  code : String
  polarity : ObservedPolarity
  pointer : String
  deriving Repr, DecidableEq

private structure FocusObservation where
  polarity : Option ObservedPolarity
  deriving Repr, DecidableEq

private structure CorrelationFocusObservation where
  firings : List A12Kernel.Evidence.Correlation.Firing
  signatures : List MessageSignature
  deriving Repr, DecidableEq

private structure RetainedRule where
  id : String
  name : String
  parentGroup : String
  errorEntityRelPath : String
  errorCode : String
  errorCondition : String
  severity : String
  deriving Repr, DecidableEq

private structure RetainedField where
  id : String
  name : String
  parentGroup : String
  kind : String
  scale : Nat
  signed : Bool
  deriving Repr, DecidableEq

private structure RetainedGroup where
  id : String
  name : String
  parentGroup : Option String
  repeatable : Bool
  deriving Repr, DecidableEq

private structure RetainedModelIndex where
  groups : List RetainedGroup
  fields : List RetainedField
  rules : List RetainedRule
  deriving Repr, DecidableEq

private structure RetainedElaborationModel where
  conditionLanguage : String
  index : RetainedModelIndex
  deriving Repr, DecidableEq

private structure OperatorCaptureRule where
  name : String
  code : String
  errorField : String
  condition : String
  deriving Repr, DecidableEq

private structure OperatorCaptureArtifact where
  sha256 : String
  bytes : Nat
  deriving Repr, DecidableEq

private structure OperatorCaptureCase where
  id : String
  caseSha256 : String
  groovyDynamic : List String
  javaStatic : List String
  interpreter : List String
  deriving Repr, DecidableEq

private structure OperatorCasePlacement where
  kind : String
  path : String
  reps : List Nat
  value : Option String
  deriving Repr, DecidableEq

private structure OperatorCaptureReceipt where
  schemaVersion : Nat
  kernelVersion : String
  a12DmkitsRevision : String
  captureDate : String
  anchor : String
  confirmationStrategies : List String
  operation : String
  ruleValidation : String
  rules : List OperatorCaptureRule
  models : Json
  cases : List OperatorCaptureCase

private def RetainedModelIndex.append (left right : RetainedModelIndex) : RetainedModelIndex :=
  { groups := left.groups ++ right.groups
    fields := left.fields ++ right.fields
    rules := left.rules ++ right.rules }

private def RetainedModelIndex.empty : RetainedModelIndex :=
  { groups := [], fields := [], rules := [] }

private def FocusObservation.fired (observation : FocusObservation) : Bool :=
  observation.polarity.isSome

private def member [FromJson α] (json : Json) (name : String) : Except String α := do
  fromJson? (← json.getObjVal? name)

private def optionalArray (json : Json) (name : String) : Except String (List Json) :=
  match json.getObjVal? name with
  | .ok value => fromJson? value
  | .error _ => pure []

private def optionalNat (json : Json) (name : String) : Except String Nat :=
  match json.getObjVal? name with
  | .ok value => fromJson? value
  | .error _ => pure 0

private def optionalBool (json : Json) (name : String) : Except String Bool :=
  match json.getObjVal? name with
  | .ok value => fromJson? value
  | .error _ => pure false

private def optionalString (json : Json) (name : String) : Except String (Option String) :=
  match json.getObjVal? name with
  | .ok value => some <$> fromJson? value
  | .error _ => pure none

private def collectGroupIndex : Nat → Option String → Json → Except String RetainedModelIndex
  | 0, _, _ => throw "retained model group nesting exceeds maximum depth"
  | fuel + 1, parentGroup, group => do
      let groupId : String ← member group "id"
      let groupName : String ← member group "name"
      let body ← group.getObjVal? "Group"
      let repeatability ← optionalNat body "repeatability"
      let elements ← optionalArray body "elements"
      let children ← elements.mapM fun element => do
        let elementType : String ← member element "type"
        match elementType with
        | "Group" => collectGroupIndex fuel (some groupId) element
        | "Field" => do
            let fieldId : String ← member element "id"
            let fieldName : String ← member element "name"
            let fieldBody ← element.getObjVal? "Field"
            let fieldType ← fieldBody.getObjVal? "fieldType"
            let kind : String ← member fieldType "type"
            let (scale, signed) ← if kind == "NumberType" then do
              let numberType ← fieldType.getObjVal? "NumberType"
              let scale ← optionalNat numberType "maxFractionalDigits"
              let positivesOnly ← optionalBool numberType "positivesOnly"
              pure (scale, !positivesOnly)
            else pure (0, false)
            pure { RetainedModelIndex.empty with fields := [{
              id := fieldId, name := fieldName, parentGroup := groupId,
              kind, scale, signed }] }
        | "Rule" => do
            let ruleId : String ← member element "id"
            let ruleName : String ← member element "name"
            let rule ← element.getObjVal? "Rule"
            pure { RetainedModelIndex.empty with rules := [{
              id := ruleId
              name := ruleName
              parentGroup := groupId
              errorEntityRelPath := ← member rule "errorEntityRelPath"
              errorCode := ← member rule "errorCode"
              errorCondition := ← member rule "errorCondition"
              severity := ← member rule "severity" }] }
        | other => throw s!"unsupported retained model element type '{other}'"
      let own : RetainedModelIndex := {
        RetainedModelIndex.empty with
        groups := [{
          id := groupId
          name := groupName
          parentGroup := parentGroup
          repeatable := decide (repeatability > 1) }] }
      pure <| children.foldl RetainedModelIndex.append own

private def retainedModelIndex (json : Json) : Except String RetainedModelIndex := do
  let content ← json.getObjVal? "content"
  let modelRoot ← content.getObjVal? "modelRoot"
  let rootGroups : List Json ← member modelRoot "rootGroups"
  let indexes ← rootGroups.mapM (collectGroupIndex 64 none)
  pure <| indexes.foldl RetainedModelIndex.append RetainedModelIndex.empty

private def retainedElaborationModel (json : Json) :
    Except String RetainedElaborationModel := do
  let content ← json.getObjVal? "content"
  let modelConfig ← content.getObjVal? "modelConfig"
  let conditionLanguage ← modelConfig.getObjVal? "conditionLanguage"
  pure {
    conditionLanguage := ← member conditionLanguage "code"
    index := ← retainedModelIndex json }

private def Observation.fromJson (json : Json) : Except String Observation := do
  let metadata ← json.getObjVal? "meta"
  let operation ← json.getObjVal? "op"
  let operationKind : String ← member operation "kind"
  if operationKind != "validateFull" then
    throw s!"unsupported external operation '{operationKind}'"
  pure {
    id := ← member metadata "id"
    kernelVersion := ← member metadata "kernelVersion"
    modelRef := ← member json "modelRef"
    expected := ← member json "expected"
    divergences := ← optionalArray json "divergences" }

private def DiagnosticObservation.fromJson (json : Json) : Except String DiagnosticObservation := do
  let metadata ← json.getObjVal? "meta"
  let diagnostics : List Json ← member json "diagnostics"
  pure {
    id := ← member metadata "id"
    kernelVersion := ← member metadata "kernelVersion"
    modelRef := ← member json "modelRef"
    expectedCode := ← member json "expectedCode"
    diagnosticCodes := ← diagnostics.mapM fun diagnostic => member diagnostic "code" }

private def CorrelationElaborationObservation.fromJson (json : Json) :
    Except String CorrelationElaborationObservation := do
  let metadata ← json.getObjVal? "meta"
  let draft ← json.getObjVal? "draft"
  let diagnostics : List Json ← member json "diagnostics"
  let parsedDiagnostics ← diagnostics.mapM fun diagnostic => do
    let location ← diagnostic.getObjVal? "where"
    pure {
      severity := ← member diagnostic "severity"
      source := ← member diagnostic "source"
      code := ← member diagnostic "code"
      rule := ← member location "rule" }
  pure {
    id := ← member metadata "id"
    kernelVersion := ← member metadata "kernelVersion"
    source := ← member metadata "source"
    capture := ← member metadata "capture"
    modelRef := ← member json "modelRef"
    draft := {
      group := ← member draft "group"
      name := ← member draft "name"
      errorField := ← member draft "errorField"
      condition := ← member draft "condition"
      errorCode := ← member draft "errorCode"
      severity := ← member draft "severity" }
    diagnostics := parsedDiagnostics
    diagnosticCodes := parsedDiagnostics.map (·.code) }

private def OperatorCaptureRule.fromJson (json : Json) : Except String OperatorCaptureRule := do
  pure {
    name := ← member json "name"
    code := ← member json "code"
    errorField := ← member json "errorField"
    condition := ← member json "condition" }

private def OperatorCaptureArtifact.fromJson (json : Json) :
    Except String OperatorCaptureArtifact := do
  pure { sha256 := ← member json "sha256", bytes := ← member json "bytes" }

private def OperatorCaptureCase.fromJson (json : Json) : Except String OperatorCaptureCase := do
  pure {
    id := ← member json "id"
    caseSha256 := ← member json "caseSha256"
    groovyDynamic := ← member json "groovyDynamic"
    javaStatic := ← member json "javaStatic"
    interpreter := ← member json "interpreter" }

private def OperatorCasePlacement.fromJson (json : Json) : Except String OperatorCasePlacement := do
  pure {
    kind := ← member json "kind"
    path := ← member json "path"
    reps := ← member json "reps"
    value := ← optionalString json "value" }

private def operatorCasePlacements (json : Json) : Except String (List OperatorCasePlacement) := do
  let placements : List Json ← member json "placements"
  placements.mapM OperatorCasePlacement.fromJson

private def OperatorCaptureReceipt.fromJson (json : Json) :
    Except String OperatorCaptureReceipt := do
  let rules : List Json ← member json "rules"
  let cases : List Json ← member json "cases"
  pure {
    schemaVersion := ← member json "schemaVersion"
    kernelVersion := ← member json "kernelVersion"
    a12DmkitsRevision := ← member json "a12DmkitsRevision"
    captureDate := ← member json "captureDate"
    anchor := ← member json "anchor"
    confirmationStrategies := ← member json "confirmationStrategies"
    operation := ← member json "operation"
    ruleValidation := ← member json "ruleValidation"
    rules := ← rules.mapM OperatorCaptureRule.fromJson
    models := ← json.getObjVal? "models"
    cases := ← cases.mapM OperatorCaptureCase.fromJson }

private def orThrow (context : String) : Except String α → IO α
  | .ok value => pure value
  | .error message => throw (IO.userError s!"{context}: {message}")

private def readJson (path : System.FilePath) : IO Json := do
  let content ← IO.FS.readFile path
  match A12Kernel.Reference.StrictJson.parseEvidence content with
  | .ok json => pure json
  | .error error => throw (IO.userError s!"{path}: {repr error}")

private def requireSnapshotDigest (caseId expected actual : String) : Except String Unit := do
  if actual != expected then
    throw s!"{caseId}: retained model SHA-256 is {actual}, expected {expected}"

private def safeRelative (reference : String) : Bool :=
  !reference.isEmpty && !reference.startsWith "/" && !(reference.splitOn "/").contains ".."

private def MessageSignature.parse (signature : String) : Except String MessageSignature := do
  let (code, polarityName, pointer) ← match signature.splitOn "|" with
    | [code, polarity, pointer] => pure (code, polarity, pointer)
    | _ => throw s!"invalid retained message signature '{signature}'"
  if code.isEmpty then throw s!"empty code in retained message signature '{signature}'"
  if pointer.isEmpty then throw s!"empty pointer in retained message signature '{signature}'"
  let polarity ← match polarityName with
    | "VALUE_ERROR" => pure .value
    | "OMISSION_ERROR" => pure .omission
    | other => throw s!"unsupported retained message polarity '{other}'"
  pure { code, polarity, pointer }

private def focusedObservation (caseId focusCode focusPointer : String)
    (expected : List String) : Except String FocusObservation := do
  let signatures ← expected.mapM MessageSignature.parse
  let focused := signatures.filter fun signature =>
    signature.code == focusCode && signature.pointer == focusPointer
  match focused with
  | [] => pure { polarity := none }
  | [signature] => pure { polarity := some signature.polarity }
  | _ => throw s!"{caseId}: retained case has duplicate focused message signatures"

private def hasDuplicate [BEq α] (values : List α) : Bool :=
  match values with
  | [] => false
  | value :: rest => rest.contains value || hasDuplicate rest

private def focusedCorrelationObservation
    (case : A12Kernel.Evidence.Correlation.CaseSpec) (expected : List String) :
    Except String CorrelationFocusObservation := do
  let signatures ← expected.mapM MessageSignature.parse
  let focused := signatures.filter (·.code == case.focusCode)
  if hasDuplicate (focused.map (·.pointer)) then
    throw s!"{case.id}: retained case has duplicate focused correlation pointers"
  for signature in focused do
    if !(case.outerRows.any (·.pointer == signature.pointer)) then
      throw s!"{case.id}: focused message has unmapped pointer '{signature.pointer}'"
  let firings := case.outerRows.flatMap fun row =>
    if focused.any (·.pointer == row.pointer) then
      [{ rowId := row.rowId, pointer := row.pointer }]
    else
      []
  pure { firings, signatures := focused }

private def pathSegments (path : String) : List String :=
  (path.splitOn "/").filter (!·.isEmpty)

private def absolutePath (segments : List String) : String :=
  "/" ++ String.intercalate "/" segments

private def expectedEntityName (path : String) : String :=
  (pathSegments path).getLast?.getD ""

private def expectedEntityParent (path : String) : Option String :=
  match (pathSegments path).dropLast with
  | [] => none
  | parent => some (absolutePath parent)

private def isProperGroupAncestor (ancestor descendant : String) : Bool :=
  let ancestorSegments := pathSegments ancestor
  let descendantSegments := pathSegments descendant
  decide (ancestorSegments.length < descendantSegments.length) &&
    descendantSegments.take ancestorSegments.length == ancestorSegments

private def bindUniqueGroup (caseId path : String) (mustBeRepeatable : Bool)
    (index : RetainedModelIndex) : Except String RetainedGroup := do
  let group ← match index.groups.filter (·.id == path) with
    | [group] => pure group
    | [] => throw s!"{caseId}: retained model has no group '{path}'"
    | _ => throw s!"{caseId}: retained model has duplicate group '{path}'"
  if group.name != expectedEntityName path then
    throw s!"{caseId}: retained group '{path}' name is '{group.name}'"
  if group.parentGroup != expectedEntityParent path then
    throw s!"{caseId}: retained group '{path}' has noncanonical physical parent {repr group.parentGroup}"
  if mustBeRepeatable && !group.repeatable then
    throw s!"{caseId}: retained group '{path}' is not repeatable"
  pure group

private def bindUniqueField (caseId path : String) (index : RetainedModelIndex) :
    Except String RetainedField := do
  let field ← match index.fields.filter (·.id == path) with
    | [field] => pure field
    | [] => throw s!"{caseId}: retained model has no field '{path}'"
    | _ => throw s!"{caseId}: retained model has duplicate field '{path}'"
  if field.name != expectedEntityName path then
    throw s!"{caseId}: retained field '{path}' name is '{field.name}'"
  match expectedEntityParent path with
  | some parent =>
      if field.parentGroup != parent then
        throw s!"{caseId}: retained field '{path}' has physical parent '{field.parentGroup}'"
  | none => throw s!"{caseId}: retained field '{path}' has no parent path"
  pure field

private def groupBindingGuardIndex (name : String) (parent : Option String) :
    RetainedModelIndex := {
  RetainedModelIndex.empty with
  groups := [{
    id := "/Order/Items"
    name := name
    parentGroup := parent
    repeatable := true }] }

private def fieldBindingGuardIndex (name parent : String) : RetainedModelIndex := {
  RetainedModelIndex.empty with
  fields := [{
    id := "/Order/Items/Count"
    name := name
    parentGroup := parent
    kind := "NumberType"
    scale := 0
    signed := true }] }

example : (bindUniqueGroup "guard" "/Order/Items" true
    (groupBindingGuardIndex "Wrong" (some "/Order"))).isOk = false := by native_decide

example : (bindUniqueGroup "guard" "/Order/Items" true
    (groupBindingGuardIndex "Items" (some "/Else"))).isOk = false := by native_decide

example : (bindUniqueField "guard" "/Order/Items/Count"
    (fieldBindingGuardIndex "Wrong" "/Order/Items")).isOk = false := by native_decide

example : (bindUniqueField "guard" "/Order/Items/Count"
    (fieldBindingGuardIndex "Count" "/Order/Else")).isOk = false := by native_decide

private def applyRelativeSegments : List String → List String → Except String (List String)
  | base, [] => pure base
  | base, segment :: rest =>
      if segment == "." || segment.isEmpty then
        applyRelativeSegments base rest
      else if segment == ".." then
        match base with
        | [] => throw "relative entity reference escapes the model root"
        | _ => applyRelativeSegments base.dropLast rest
      else
        applyRelativeSegments (base ++ [segment]) rest

private def resolveEntityReference (entityId reference : String) : Except String String := do
  let base := if reference.startsWith "/" then [] else pathSegments entityId
  let segments ← applyRelativeSegments base (pathSegments reference)
  if segments.isEmpty then throw "entity reference resolves to the model root"
  pure ("/" ++ String.intercalate "/" segments)

private def resolveConditionReference (ruleId reference : String) : Except String String := do
  let base := if reference.startsWith "/" then [] else pathSegments ruleId |>.dropLast
  let segments ← applyRelativeSegments base (pathSegments reference)
  if segments.isEmpty then throw "condition reference resolves to the model root"
  pure ("/" ++ String.intercalate "/" segments)

private def bindCorrelationProjectionToModel
    (case : A12Kernel.Evidence.Correlation.CaseSpec) (model : Json) : Except String Unit := do
  let index ← retainedModelIndex model
  discard <| bindUniqueGroup case.id case.groupPath true index
  for projectedField in case.fields do
    let field ← bindUniqueField case.id projectedField.path index
    if field.kind != "NumberType" then
      throw s!"{case.id}: retained field '{field.id}' is {field.kind}, not NumberType"
    if field.scale != projectedField.scale then
      throw s!"{case.id}: retained field '{field.id}' scale is {field.scale}, projection says {projectedField.scale}"
    if field.signed != projectedField.signed then
      throw s!"{case.id}: retained field '{field.id}' signed={field.signed}, projection says {projectedField.signed}"
  let rule ← match index.rules.filter (·.errorCode == case.focusCode) with
    | [rule] => pure rule
    | [] => throw s!"{case.id}: retained model has no rule with code '{case.focusCode}'"
    | _ => throw s!"{case.id}: retained model has multiple rules with code '{case.focusCode}'"
  let conditionGroupPath ← resolveConditionReference rule.id case.conditionGroupPath
  if conditionGroupPath != case.groupPath then
    throw s!"{case.id}: condition group path resolves to '{conditionGroupPath}', expected '{case.groupPath}'"
  for projectedField in case.fields do
    let conditionFieldPath ← resolveConditionReference rule.id projectedField.conditionPath
    if conditionFieldPath != projectedField.path then
      throw s!"{case.id}: condition field path resolves to '{conditionFieldPath}', expected '{projectedField.path}'"
  let guardField ← match case.fields.filter (·.id == case.guardFieldId) with
    | [field] => pure field
    | [] => throw s!"{case.id}: projection has no guard field {case.guardFieldId}"
    | _ => throw s!"{case.id}: projection has duplicate guard field {case.guardFieldId}"
  let errorPath ← resolveEntityReference rule.id rule.errorEntityRelPath
  if errorPath != guardField.path then
    throw s!"{case.id}: retained rule error path resolves to '{errorPath}', expected '{guardField.path}'"
  let projectedCondition ← case.renderCondition
  if rule.errorCondition != projectedCondition then
    throw s!"{case.id}: retained condition '{rule.errorCondition}' does not equal projection '{projectedCondition}'"

private def bindCorrelationElaborationProjectionToModel
    (case : A12Kernel.Evidence.CorrelationElaboration.CaseSpec)
    (draft : A12Kernel.Evidence.CorrelationElaboration.DraftSignature)
    (model : RetainedElaborationModel) : Except String Unit := do
  if model.conditionLanguage != "en_US" then
    throw s!"{case.id}: retained condition language is '{model.conditionLanguage}', expected 'en_US'"
  let index := model.index
  let declaringGroupPath := absolutePath case.rule.declaringGroup
  discard <| bindUniqueGroup case.id declaringGroupPath false index
  for projectedGroup in case.groups do
    let groupPath := absolutePath projectedGroup.path
    discard <| bindUniqueGroup case.id groupPath true index
    if index.groups.any fun candidate =>
        candidate.repeatable && isProperGroupAncestor candidate.id groupPath then
      throw s!"{case.id}: retained group '{groupPath}' has a repeatable proper ancestor"
  for projectedField in case.fields do
    let group ← match case.groups.filter (·.level == projectedField.groupLevel) with
      | [group] => pure group
      | [] => throw s!"{case.id}: projected field {projectedField.id} has unknown group level {projectedField.groupLevel}"
      | _ => throw s!"{case.id}: projected field {projectedField.id} has ambiguous group level {projectedField.groupLevel}"
    let fieldPath := absolutePath (group.path ++ [projectedField.name])
    let field ← bindUniqueField case.id fieldPath index
    if field.kind != "NumberType" then
      throw s!"{case.id}: retained field '{field.id}' is {field.kind}, not NumberType"
    if field.scale != projectedField.scale then
      throw s!"{case.id}: retained field '{field.id}' scale is {field.scale}, projection says {projectedField.scale}"
    if field.signed != projectedField.signed then
      throw s!"{case.id}: retained field '{field.id}' signed={field.signed}, projection says {projectedField.signed}"
  let projectedDraft := case.renderDraft
  if draft != projectedDraft then
    throw s!"{case.id}: retained draft {repr draft} does not equal projection {repr projectedDraft}"
  let seedRuleId := draft.group ++ "/" ++ draft.name
  let seedRule ← match index.rules.filter (·.id == seedRuleId) with
    | [rule] => pure rule
    | [] => throw s!"{case.id}: retained model has no seed rule '{seedRuleId}'"
    | _ => throw s!"{case.id}: retained model has duplicate seed rule '{seedRuleId}'"
  if seedRule.name != draft.name || seedRule.parentGroup != draft.group then
    throw s!"{case.id}: retained seed rule identity does not match the captured draft"
  if seedRule.errorEntityRelPath != draft.errorField then
    throw s!"{case.id}: retained seed error field '{seedRule.errorEntityRelPath}' does not match '{draft.errorField}'"
  if seedRule.errorCode != draft.errorCode || seedRule.severity != draft.severity then
    throw s!"{case.id}: retained seed code/severity does not match the captured draft"
  let seedCondition := case.renderSeedCondition
  if seedRule.errorCondition != seedCondition then
    throw s!"{case.id}: retained seed condition '{seedRule.errorCondition}' does not equal '{seedCondition}'"

private def validateCorrelationElaborationObservation
    (case : A12Kernel.Evidence.CorrelationElaboration.CaseSpec)
    (observation : CorrelationElaborationObservation) : Except String Unit := do
  if observation.source != "curated" || observation.capture != "KernelAdapter.diagnose" then
    throw s!"{case.id}: unsupported capture provenance '{observation.source}/{observation.capture}'"
  let expectedRulePath := observation.draft.group ++ "/" ++ observation.draft.name
  for diagnostic in observation.diagnostics do
    if diagnostic.severity != observation.draft.severity || diagnostic.source != "KERNEL" ||
        diagnostic.rule != expectedRulePath then
      throw s!"{case.id}: diagnostic identity/routing does not match the captured draft"

private def validateCorrelationElaborationBinding
    (case : A12Kernel.Evidence.CorrelationElaboration.CaseSpec)
    (observation : CorrelationElaborationObservation)
    (model : RetainedElaborationModel) : Except String Unit := do
  validateCorrelationElaborationObservation case observation
  bindCorrelationElaborationProjectionToModel case observation.draft model

private def bindOperatorProjectionToModel
    (projected : A12Kernel.Evidence.OperatorEmpty.ModelSpec)
    (retained : RetainedElaborationModel) : Except String Unit := do
  if retained.conditionLanguage != "en_US" then
    throw s!"{projected.id}: retained condition language is '{retained.conditionLanguage}'"
  let declaringGroupPath := absolutePath projected.declaringGroup
  let declaringGroup ← bindUniqueGroup projected.id declaringGroupPath false retained.index
  if declaringGroup.repeatable then
    throw s!"{projected.id}: declaring group '{declaringGroupPath}' is unexpectedly repeatable"
  let contentFieldPath := declaringGroupPath ++ "/CustomerName"
  let contentField ← bindUniqueField projected.id contentFieldPath retained.index
  if contentField.kind != "StringType" then
    throw s!"{projected.id}: content witness '{contentFieldPath}' is {contentField.kind}, not StringType"
  for projectedField in projected.fields do
    let path := absolutePath projectedField.path
    let field ← bindUniqueField projected.id path retained.index
    match projectedField.kind with
    | .string =>
        if field.kind != "StringType" then
          throw s!"{projected.id}: retained field '{path}' is {field.kind}, not StringType"
    | .number scale signed =>
        if field.kind != "NumberType" then
          throw s!"{projected.id}: retained field '{path}' is {field.kind}, not NumberType"
        if field.scale != scale || field.signed != signed then
          throw s!"{projected.id}: retained Number metadata differs at '{path}'"
  let projectedRuleIds := (projected.rules.map fun rule =>
    declaringGroupPath ++ "/" ++ rule.name).mergeSort
  let retainedRuleIds := (retained.index.rules.map (·.id)).mergeSort
  if retainedRuleIds != projectedRuleIds then
    throw s!"{projected.id}: retained rule inventory differs from the projection"
  for projectedRule in projected.rules do
    let ruleId := declaringGroupPath ++ "/" ++ projectedRule.name
    let retainedRule ← match retained.index.rules.filter (·.id == ruleId) with
      | [rule] => pure rule
      | [] => throw s!"{projected.id}: retained model has no rule '{ruleId}'"
      | _ => throw s!"{projected.id}: retained model has duplicate rule '{ruleId}'"
    if retainedRule.name != projectedRule.name || retainedRule.parentGroup != declaringGroupPath ||
        retainedRule.errorCode != projectedRule.code || retainedRule.severity != "ERROR" then
      throw s!"{projected.id}: retained rule identity/metadata differs for '{ruleId}'"
    let errorField ← projected.findField projectedRule.errorFieldId
    let retainedErrorPath ← resolveEntityReference retainedRule.id retainedRule.errorEntityRelPath
    let expectedErrorPath := absolutePath errorField.path
    if retainedErrorPath != expectedErrorPath then
      throw s!"{projected.id}: retained rule '{ruleId}' routes to '{retainedErrorPath}'"
    let expectedPointer := declaringGroupPath ++ "[1]/" ++ errorField.name
    if projectedRule.errorPointer != expectedPointer then
      throw s!"{projected.id}: projected rule '{ruleId}' has noncanonical first-row pointer '{projectedRule.errorPointer}'"
    let condition ← projectedRule.condition.render projected
    if retainedRule.errorCondition != condition then
      throw s!"{projected.id}: retained condition '{retainedRule.errorCondition}' does not equal '{condition}'"

private def validateOperatorCaptureBasics
    (bundle : A12Kernel.Evidence.OperatorEmpty.Bundle)
    (receipt : OperatorCaptureReceipt) : Except String Unit := do
  if receipt.schemaVersion != 1 || receipt.kernelVersion != bundle.kernelVersion ||
      receipt.a12DmkitsRevision != bundle.sourceRevision then
    throw "operator-empty capture compatibility identity differs from its projection"
  if receipt.captureDate != "2026-07-15" || receipt.anchor != "kernel-groovy-dynamic" ||
      receipt.confirmationStrategies != ["kernel-java-static", "interpreter"] ||
      receipt.operation != "validateFull" ||
      receipt.ruleValidation != "allAcceptedByKernelCheckConsistency" then
    throw "operator-empty capture provenance or rule-validation posture is unsupported"
  if hasDuplicate (receipt.rules.map (·.code)) || hasDuplicate (receipt.cases.map (·.id)) then
    throw "operator-empty capture has duplicate rule or case identity"
  let projectedCodes := (bundle.models.flatMap fun model => model.rules.map (·.code)).mergeSort
  if (receipt.rules.map (·.code)).mergeSort != projectedCodes then
    throw "operator-empty capture rule inventory differs from its projection"
  if (receipt.cases.map (·.id)).mergeSort != (bundle.cases.map (·.id)).mergeSort then
    throw "operator-empty capture case inventory differs from its projection"
  let modelObject ← match receipt.models.getObj? with
    | .ok object => pure object
    | .error _ => throw "operator-empty capture models member is not an object"
  if (modelObject.toList.map (·.1)).mergeSort != (bundle.models.map (·.id)).mergeSort then
    throw "operator-empty capture model inventory differs from its projection"

private def validateOperatorCaptureRules
    (bundle : A12Kernel.Evidence.OperatorEmpty.Bundle)
    (receipt : OperatorCaptureReceipt) : Except String Unit := do
  for model in bundle.models do
    for rule in model.rules do
      let captured ← match receipt.rules.filter (·.code == rule.code) with
        | [captured] => pure captured
        | [] => throw s!"capture has no rule '{rule.code}'"
        | _ => throw s!"capture has duplicate rule '{rule.code}'"
      let errorField ← model.findField rule.errorFieldId
      let condition ← rule.condition.render model
      if captured.name != rule.name || captured.errorField != "../" ++ errorField.name ||
          captured.condition != condition then
        throw s!"capture rule '{rule.code}' differs from the typed projection"

private def operatorCaptureArtifact (receipt : OperatorCaptureReceipt) (modelId : String) :
    Except String OperatorCaptureArtifact := do
  OperatorCaptureArtifact.fromJson (← receipt.models.getObjVal? modelId)

private def operatorCaptureCase (receipt : OperatorCaptureReceipt) (caseId : String) :
    Except String OperatorCaptureCase :=
  match receipt.cases.filter (·.id == caseId) with
  | [captured] => pure captured
  | [] => throw s!"operator-empty capture has no case '{caseId}'"
  | _ => throw s!"operator-empty capture has duplicate case '{caseId}'"

private def validateOperatorCaptureCase (caseId expectedDigest : String)
    (expected : List String) (captured : OperatorCaptureCase) : Except String Unit := do
  if captured.caseSha256 != expectedDigest then
    throw s!"{caseId}: capture case digest differs from the projection"
  if captured.groovyDynamic != expected || captured.javaStatic != expected ||
      captured.interpreter != expected then
    throw s!"{caseId}: kernel strategies or interpreter differ from the retained observation"

private def expectedOperatorPlacements
    (model : A12Kernel.Evidence.OperatorEmpty.ModelSpec)
    (case : A12Kernel.Evidence.OperatorEmpty.CaseSpec) :
    Except String (List OperatorCasePlacement) := do
  if model.declaringGroup.length != 1 then
    throw s!"{case.id}: operator-empty capture admits exactly one nonrepeatable declaring group"
  let groupPath := absolutePath model.declaringGroup
  let groupPlacement : OperatorCasePlacement :=
    { kind := "GROUP", path := groupPath, reps := [1], value := none }
  let contentPlacement : OperatorCasePlacement :=
    { kind := "FIELD", path := groupPath ++ "/CustomerName", reps := [1, 1],
      value := some "Acme" }
  let contentPlacements : List OperatorCasePlacement :=
    if case.hasContent then [contentPlacement] else []
  let projectedPlacements ← case.cells.mapM fun cell => do
    let field ← model.findField cell.fieldId
    let path := absolutePath field.path
    match cell.state with
    | .empty => pure { kind := "EMPTY", path, reps := [1, 1], value := none }
    | .number value =>
        pure { kind := "FIELD", path, reps := [1, 1], value := some (toString value) }
    | .string value =>
        pure { kind := "FIELD", path, reps := [1, 1], value := some value }
  pure ([groupPlacement] ++ contentPlacements ++ projectedPlacements)

private def bindOperatorCasePlacements
    (model : A12Kernel.Evidence.OperatorEmpty.ModelSpec)
    (case : A12Kernel.Evidence.OperatorEmpty.CaseSpec)
    (retained : List OperatorCasePlacement) : Except String Unit := do
  let expected ← expectedOperatorPlacements model case
  if retained != expected then
    throw s!"{case.id}: retained placements {repr retained} differ from projection {repr expected}"

private def expectRejected (context : String) (result : Except String Unit) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok () => throw (IO.userError s!"negative evidence lock accepted {context}")

private def checkOperatorModel (root : System.FilePath)
    (receipt : OperatorCaptureReceipt)
    (model : A12Kernel.Evidence.OperatorEmpty.ModelSpec) : IO RetainedElaborationModel := do
  if !safeRelative model.modelRef then
    throw (IO.userError s!"{model.id}: unsafe modelRef '{model.modelRef}'")
  let modelPath := root / model.modelRef
  let content ← IO.FS.readFile modelPath
  let actualDigest ← A12Kernel.Process.Sha256.file modelPath
  orThrow model.id (requireSnapshotDigest model.id model.modelSha256 actualDigest)
  let captured ← orThrow model.id (operatorCaptureArtifact receipt model.id)
  if captured.sha256 != model.modelSha256 || captured.bytes != content.utf8ByteSize then
    throw (IO.userError s!"{model.id}: capture model identity differs from retained bytes")
  let retained ← orThrow model.id (retainedElaborationModel (← readJson modelPath))
  orThrow model.id (bindOperatorProjectionToModel model retained)
  pure retained

private def checkOperatorCase (root : System.FilePath)
    (bundle : A12Kernel.Evidence.OperatorEmpty.Bundle)
    (receipt : OperatorCaptureReceipt)
    (case : A12Kernel.Evidence.OperatorEmpty.CaseSpec) : IO Unit := do
  if !safeRelative case.caseRef then
    throw (IO.userError s!"{case.id}: unsafe caseRef '{case.caseRef}'")
  let casePath := root / case.caseRef
  let actualDigest ← A12Kernel.Process.Sha256.file casePath
  orThrow case.id (requireSnapshotDigest case.id case.caseSha256 actualDigest)
  let caseJson ← readJson casePath
  let observation ← orThrow case.id (Observation.fromJson caseJson)
  let model ← orThrow case.id (bundle.modelFor case)
  let placements ← orThrow case.id (operatorCasePlacements caseJson)
  orThrow case.id (bindOperatorCasePlacements model case placements)
  if observation.id != case.id || observation.kernelVersion != bundle.kernelVersion ||
      observation.modelRef != model.modelRef then
    throw (IO.userError s!"{case.id}: retained observation identity differs from the projection")
  if !observation.divergences.isEmpty then
    throw (IO.userError s!"{case.id}: retained observation records a kernel-strategy divergence")
  if observation.expected != observation.expected.mergeSort ||
      hasDuplicate observation.expected then
    throw (IO.userError s!"{case.id}: retained signatures are not canonical and duplicate-free")
  for signature in observation.expected do
    discard <| orThrow case.id (MessageSignature.parse signature)
  let captured ← orThrow case.id (operatorCaptureCase receipt case.id)
  orThrow case.id (validateOperatorCaptureCase case.id case.caseSha256
    observation.expected captured)
  let actual ← orThrow case.id (model.replay case)
  if actual != observation.expected then
    throw (IO.userError s!"{case.id}: observed {repr observation.expected}, Lean produced {repr actual}")

private def checkOperatorBindingLocks (root : System.FilePath)
    (bundle : A12Kernel.Evidence.OperatorEmpty.Bundle)
    (receipt : OperatorCaptureReceipt) : IO Unit := do
  let model ← match bundle.models with
    | model :: _ => pure model
    | [] => throw (IO.userError "operator-empty binding lock requires a model")
  let retained ← checkOperatorModel root receipt model
  let changedRules := retained.index.rules.map fun rule =>
    { rule with errorCondition := rule.errorCondition ++ " changed" }
  expectRejected "an operator-empty stored condition change"
    (bindOperatorProjectionToModel model
      { retained with index := { retained.index with rules := changedRules } })
  let renamedFields := retained.index.fields.map fun field =>
    { field with name := field.name ++ "Changed" }
  expectRejected "an operator-empty retained field rename"
    (bindOperatorProjectionToModel model
      { retained with index := { retained.index with fields := renamedFields } })
  let duplicatedRules := match retained.index.rules with
    | rule :: _ => rule :: retained.index.rules
    | [] => []
  expectRejected "an operator-empty extra retained rule"
    (bindOperatorProjectionToModel model
      { retained with index := { retained.index with rules := duplicatedRules } })
  let case ← match bundle.cases with
    | case :: _ => pure case
    | [] => throw (IO.userError "operator-empty binding lock requires a case")
  let caseJson ← readJson (root / case.caseRef)
  let observation ← orThrow case.id (Observation.fromJson caseJson)
  let placements ← orThrow case.id (operatorCasePlacements caseJson)
  let caseModel ← orThrow case.id (bundle.modelFor case)
  expectRejected "an operator-empty row-content projection change"
    (bindOperatorCasePlacements caseModel { case with hasContent := !case.hasContent } placements)
  let changedCells := case.cells.map fun cell =>
    { cell with state := match cell.state with
      | .empty => .string "Changed"
      | .number _ | .string _ => .empty }
  expectRejected "an operator-empty cell-state projection change"
    (bindOperatorCasePlacements caseModel { case with cells := changedCells } placements)
  let captured ← orThrow case.id (operatorCaptureCase receipt case.id)
  expectRejected "an operator-empty interpreter strategy disagreement"
    (validateOperatorCaptureCase case.id case.caseSha256 observation.expected
      { captured with interpreter := [] })
  expectRejected "an operator-empty capture revision change"
    (validateOperatorCaptureBasics bundle
      { receipt with a12DmkitsRevision := "0000000000000000000000000000000000000000" })

private def checkOperatorEvidence (root : System.FilePath)
    (bundle : A12Kernel.Evidence.OperatorEmpty.Bundle) : IO Unit := do
  if !safeRelative bundle.captureRef then
    throw (IO.userError s!"unsafe operator-empty captureRef '{bundle.captureRef}'")
  let capturePath := root / bundle.captureRef
  let actualCaptureDigest ← A12Kernel.Process.Sha256.file capturePath
  orThrow "operator-empty capture" (requireSnapshotDigest "operator-empty capture"
    bundle.captureSha256 actualCaptureDigest)
  let receipt ← orThrow "operator-empty capture"
    (OperatorCaptureReceipt.fromJson (← readJson capturePath))
  orThrow "operator-empty capture" (validateOperatorCaptureBasics bundle receipt)
  orThrow "operator-empty capture" (validateOperatorCaptureRules bundle receipt)
  for model in bundle.models do
    discard <| checkOperatorModel root receipt model
  checkOperatorBindingLocks root bundle receipt
  for case in bundle.cases do
    checkOperatorCase root bundle receipt case

private def checkCorrelationElaborationBindingLocks (root : System.FilePath)
    (case : A12Kernel.Evidence.CorrelationElaboration.CaseSpec) : IO Unit := do
  if !safeRelative case.caseRef then
    throw (IO.userError s!"{case.id}: unsafe correlation-elaboration caseRef '{case.caseRef}'")
  let json ← readJson (root / case.caseRef)
  let observation ← orThrow case.id (CorrelationElaborationObservation.fromJson json)
  if !safeRelative observation.modelRef then
    throw (IO.userError s!"{case.id}: unsafe modelRef '{observation.modelRef}'")
  let modelJson ← readJson (root / observation.modelRef)
  let model ← orThrow case.id (retainedElaborationModel modelJson)
  let actualDigest ← A12Kernel.Process.Sha256.file (root / observation.modelRef)
  orThrow case.id (requireSnapshotDigest case.id case.modelSha256 actualDigest)
  let wrongDigest :=
    (if case.modelSha256.startsWith "0" then "1" else "0") ++ case.modelSha256.drop 1
  expectRejected "retained model snapshot drift"
    (requireSnapshotDigest case.id wrongDigest actualDigest)
  expectRejected "a non-English retained model"
    (validateCorrelationElaborationBinding case observation
      { model with conditionLanguage := "de_DE" })
  expectRejected "a draft that differs from the structured projection"
    (validateCorrelationElaborationBinding case
      { observation with draft :=
          { observation.draft with condition := observation.draft.condition ++ " Or True" } }
      model)
  let seedRuleId := observation.draft.group ++ "/" ++ observation.draft.name
  let wrongSeedRules := model.index.rules.map fun rule =>
    if rule.id == seedRuleId then { rule with name := rule.name ++ "Changed" } else rule
  expectRejected "a retained seed rule with a different identity"
    (validateCorrelationElaborationBinding case observation
      { model with index := { model.index with rules := wrongSeedRules } })
  let nestedGroups := model.index.groups.map fun group =>
    if group.id == observation.draft.group then { group with repeatable := true } else group
  expectRejected "a projected group below another repeatable group"
    (validateCorrelationElaborationBinding case observation
      { model with index := { model.index with groups := nestedGroups } })
  expectRejected "unsupported capture provenance"
    (validateCorrelationElaborationBinding case
      { observation with source := "generated" } model)
  if observation.diagnostics.isEmpty then
    throw (IO.userError "correlation-elaboration binding lock requires a diagnostic fixture")
  let wrongSourceDiagnostics := observation.diagnostics.map fun diagnostic =>
    { diagnostic with source := "NOT_KERNEL" }
  expectRejected "a diagnostic from another source"
    (validateCorrelationElaborationBinding case
      { observation with diagnostics := wrongSourceDiagnostics } model)
  let wrongRouteDiagnostics := observation.diagnostics.map fun diagnostic =>
    { diagnostic with rule := diagnostic.rule ++ "/Else" }
  expectRejected "a diagnostic routed to another rule"
    (validateCorrelationElaborationBinding case
      { observation with diagnostics := wrongRouteDiagnostics } model)

private def checkCase (root : System.FilePath) (bundle : Bundle) (case : CaseSpec) : IO Unit := do
  if !safeRelative case.caseRef then
    throw (IO.userError s!"{case.id}: unsafe caseRef '{case.caseRef}'")
  let json ← readJson (root / case.caseRef)
  let (externalId, externalVersion, modelRef, observed) ← match case.operation with
    | .resolve _ _ => do
        let observation ← orThrow case.id (DiagnosticObservation.fromJson json)
        if !(observation.diagnosticCodes.contains observation.expectedCode) then
          throw (IO.userError s!"{case.id}: expected diagnostic code is absent from retained diagnostics")
        pure (observation.id, observation.kernelVersion, observation.modelRef,
          [observation.expectedCode])
    | _ => do
        let observation ← orThrow case.id (Observation.fromJson json)
        if !observation.divergences.isEmpty then
          throw (IO.userError s!"{case.id}: external capture records a kernel-strategy divergence")
        pure (observation.id, observation.kernelVersion, observation.modelRef,
          observation.expected.filter (·.startsWith s!"{case.focusCode}|"))
  if externalId != case.id then
    throw (IO.userError s!"{case.id}: external id is '{externalId}'")
  if externalVersion != bundle.kernelVersion then
    throw (IO.userError s!"{case.id}: external kernel version is {externalVersion}")
  if !safeRelative modelRef then
    throw (IO.userError s!"{case.id}: unsafe modelRef '{modelRef}'")
  if !(← System.FilePath.pathExists (root / modelRef)) then
    throw (IO.userError s!"{case.id}: missing retained model '{modelRef}'")
  let actual ← orThrow case.id case.replay
  if actual != observed then
    throw (IO.userError s!"{case.id}: observed {repr observed}, Lean produced {repr actual}")

private def checkIterationCase (root : System.FilePath)
    (bundle : A12Kernel.Evidence.Iteration.Bundle)
    (case : A12Kernel.Evidence.Iteration.CaseSpec) : IO Unit := do
  if !safeRelative case.caseRef then
    throw (IO.userError s!"{case.id}: unsafe iteration caseRef '{case.caseRef}'")
  let json ← readJson (root / case.caseRef)
  let observation ← orThrow case.id (Observation.fromJson json)
  if !observation.divergences.isEmpty then
    throw (IO.userError s!"{case.id}: external capture records a kernel-strategy divergence")
  if observation.id != case.id then
    throw (IO.userError s!"{case.id}: external id is '{observation.id}'")
  if observation.kernelVersion != bundle.kernelVersion then
    throw (IO.userError s!"{case.id}: external kernel version is {observation.kernelVersion}")
  if !safeRelative observation.modelRef then
    throw (IO.userError s!"{case.id}: unsafe modelRef '{observation.modelRef}'")
  if !(← System.FilePath.pathExists (root / observation.modelRef)) then
    throw (IO.userError s!"{case.id}: missing retained model '{observation.modelRef}'")
  let observed ← orThrow case.id
    (focusedObservation case.id case.focusCode case.focusPointer observation.expected)
  let actual ← orThrow case.id case.replay
  let actualFired := actual == .tru
  if actualFired != observed.fired then
    throw (IO.userError
      s!"{case.id}: observed fired={observed.fired} polarity={repr observed.polarity}, Lean produced {repr actual}")

private def checkCorrelationCase (root : System.FilePath)
    (bundle : A12Kernel.Evidence.Correlation.Bundle)
    (case : A12Kernel.Evidence.Correlation.CaseSpec) : IO Unit := do
  if !safeRelative case.caseRef then
    throw (IO.userError s!"{case.id}: unsafe correlation caseRef '{case.caseRef}'")
  let json ← readJson (root / case.caseRef)
  let observation ← orThrow case.id (Observation.fromJson json)
  if !observation.divergences.isEmpty then
    throw (IO.userError s!"{case.id}: external capture records a kernel-strategy divergence")
  if observation.id != case.id then
    throw (IO.userError s!"{case.id}: external id is '{observation.id}'")
  if observation.kernelVersion != bundle.kernelVersion then
    throw (IO.userError s!"{case.id}: external kernel version is {observation.kernelVersion}")
  if !safeRelative observation.modelRef then
    throw (IO.userError s!"{case.id}: unsafe modelRef '{observation.modelRef}'")
  if !(← System.FilePath.pathExists (root / observation.modelRef)) then
    throw (IO.userError s!"{case.id}: missing retained model '{observation.modelRef}'")
  let model ← readJson (root / observation.modelRef)
  orThrow case.id (bindCorrelationProjectionToModel case model)
  let observed ← orThrow case.id (focusedCorrelationObservation case observation.expected)
  let actual ← orThrow case.id case.replay
  if actual != observed.firings then
    throw (IO.userError
      s!"{case.id}: observed {repr observed.signatures}, Lean produced ordered firings {repr actual}")

private def checkCorrelationElaborationCase (root : System.FilePath)
    (bundle : A12Kernel.Evidence.CorrelationElaboration.Bundle)
    (case : A12Kernel.Evidence.CorrelationElaboration.CaseSpec) : IO Unit := do
  if !safeRelative case.caseRef then
    throw (IO.userError s!"{case.id}: unsafe correlation-elaboration caseRef '{case.caseRef}'")
  let json ← readJson (root / case.caseRef)
  let observation ← orThrow case.id (CorrelationElaborationObservation.fromJson json)
  if observation.id != case.id then
    throw (IO.userError s!"{case.id}: external id is '{observation.id}'")
  if observation.kernelVersion != bundle.kernelVersion then
    throw (IO.userError s!"{case.id}: external kernel version is {observation.kernelVersion}")
  if !safeRelative observation.modelRef then
    throw (IO.userError s!"{case.id}: unsafe modelRef '{observation.modelRef}'")
  let modelPath := root / observation.modelRef
  if !(← System.FilePath.pathExists modelPath) then
    throw (IO.userError s!"{case.id}: missing retained model '{observation.modelRef}'")
  let actualDigest ← A12Kernel.Process.Sha256.file modelPath
  orThrow case.id (requireSnapshotDigest case.id case.modelSha256 actualDigest)
  let modelJson ← readJson modelPath
  let model ← orThrow case.id (retainedElaborationModel modelJson)
  orThrow case.id (validateCorrelationElaborationBinding case observation model)
  let actual ← orThrow case.id case.replayDiagnosticCodes
  if actual != observation.diagnosticCodes then
    throw (IO.userError
      s!"{case.id}: observed diagnostic codes {repr observation.diagnosticCodes}, Lean produced {repr actual}")

def main : IO Unit := do
  let root : System.FilePath := "evidence/kernel-30.8.1"
  A12Kernel.Evidence.ObservationBundleTest.checkIo
  let directCascadeCount ←
    A12Kernel.Evidence.StringCascadeProjection.checkArtifacts
      (root / "captures/string-direct-cascade-v1")
  let bundle ← orThrow "projection.json"
    (Bundle.fromJson (← readJson (root / "projection.json")))
  orThrow "projection.json" bundle.validate
  for case in bundle.cases do
    checkCase root bundle case
  let operatorBundle ← orThrow "operator-empty-projection.json"
    (A12Kernel.Evidence.OperatorEmpty.Bundle.fromJson
      (← readJson (root / "operator-empty-projection.json")))
  orThrow "operator-empty-projection.json" operatorBundle.validate
  let _operatorProtocolCase ←
    A12Kernel.Evidence.OperatorEmpty.ProtocolBridge.checkArtifacts
  checkOperatorEvidence root operatorBundle
  let stringComputationCount ←
    A12Kernel.Evidence.StringComputation.Binding.checkArtifacts root
  let stringTargetValidationCount ←
    A12Kernel.Evidence.StringTargetValidation.Binding.checkArtifacts root
  let iterationBundle ← orThrow "iteration-projection.json"
    (A12Kernel.Evidence.Iteration.Bundle.fromJson
      (← readJson (root / "iteration-projection.json")))
  orThrow "iteration-projection.json" iterationBundle.validate
  for case in iterationBundle.cases do
    checkIterationCase root iterationBundle case
  let correlationBundle ← orThrow "correlation-projection.json"
    (A12Kernel.Evidence.Correlation.Bundle.fromJson
      (← readJson (root / "correlation-projection.json")))
  orThrow "correlation-projection.json" correlationBundle.validate
  for case in correlationBundle.cases do
    checkCorrelationCase root correlationBundle case
  let correlationElaborationBundle ← orThrow "correlation-elaboration-projection.json"
    (A12Kernel.Evidence.CorrelationElaboration.Bundle.fromJson
      (← readJson (root / "correlation-elaboration-projection.json")))
  orThrow "correlation-elaboration-projection.json" correlationElaborationBundle.validate
  match correlationElaborationBundle.cases with
  | first :: _ => checkCorrelationElaborationBindingLocks root first
  | [] => throw (IO.userError "correlation-elaboration evidence bundle is empty")
  for case in correlationElaborationBundle.cases do
    checkCorrelationElaborationCase root correlationElaborationBundle case
  let total := bundle.cases.length + operatorBundle.cases.length + iterationBundle.cases.length +
    correlationBundle.cases.length + correlationElaborationBundle.cases.length +
    stringComputationCount + stringTargetValidationCount + directCascadeCount
  IO.println s!"kernel evidence: {total}/{total} projections agree; String computation: {stringComputationCount}/{stringComputationCount} cases bound; String target validation: {stringTargetValidationCount}/{stringTargetValidationCount} cases bound; direct String cascade: {directCascadeCount}/{directCascadeCount} producer-certified cases replayed ({bundle.kernelVersion})"
