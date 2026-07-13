import A12Kernel.Evidence.CorrelationReplay
import A12Kernel.Evidence.Replay
import A12Kernel.Evidence.IterationReplay
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
  errorEntityRelPath : String
  errorCode : String
  errorCondition : String
  deriving Repr, DecidableEq

private structure RetainedField where
  id : String
  kind : String
  scale : Nat
  signed : Bool
  deriving Repr, DecidableEq

private structure RetainedModelIndex where
  groups : List String
  fields : List RetainedField
  rules : List RetainedRule
  deriving Repr, DecidableEq

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

private def collectGroupIndex : Nat → Json → Except String RetainedModelIndex
  | 0, _ => throw "retained model group nesting exceeds maximum depth"
  | fuel + 1, group => do
      let groupId : String ← member group "id"
      let body ← group.getObjVal? "Group"
      let elements ← optionalArray body "elements"
      let children ← elements.mapM fun element => do
        let elementType : String ← member element "type"
        match elementType with
        | "Group" => collectGroupIndex fuel element
        | "Field" => do
            let fieldId : String ← member element "id"
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
              id := fieldId, kind, scale, signed }] }
        | "Rule" => do
            let ruleId : String ← member element "id"
            let rule ← element.getObjVal? "Rule"
            pure { RetainedModelIndex.empty with rules := [{
              id := ruleId
              errorEntityRelPath := ← member rule "errorEntityRelPath"
              errorCode := ← member rule "errorCode"
              errorCondition := ← member rule "errorCondition" }] }
        | other => throw s!"unsupported retained model element type '{other}'"
      pure <| children.foldl RetainedModelIndex.append
        { RetainedModelIndex.empty with groups := [groupId] }

private def retainedModelIndex (json : Json) : Except String RetainedModelIndex := do
  let content ← json.getObjVal? "content"
  let modelRoot ← content.getObjVal? "modelRoot"
  let rootGroups : List Json ← member modelRoot "rootGroups"
  let indexes ← rootGroups.mapM (collectGroupIndex 64)
  pure <| indexes.foldl RetainedModelIndex.append RetainedModelIndex.empty

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

private def orThrow (context : String) : Except String α → IO α
  | .ok value => pure value
  | .error message => throw (IO.userError s!"{context}: {message}")

private def readJson (path : System.FilePath) : IO Json := do
  let content ← IO.FS.readFile path
  orThrow path.toString (Json.parse content)

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
  match index.groups.filter (· == case.groupPath) with
  | [_] => pure ()
  | [] => throw s!"{case.id}: retained model has no group '{case.groupPath}'"
  | _ => throw s!"{case.id}: retained model has duplicate group '{case.groupPath}'"
  for projectedField in case.fields do
    match index.fields.filter (·.id == projectedField.path) with
    | [field] =>
        if field.kind != "NumberType" then
          throw s!"{case.id}: retained field '{field.id}' is {field.kind}, not NumberType"
        if field.scale != projectedField.scale then
          throw s!"{case.id}: retained field '{field.id}' scale is {field.scale}, projection says {projectedField.scale}"
        if field.signed != projectedField.signed then
          throw s!"{case.id}: retained field '{field.id}' signed={field.signed}, projection says {projectedField.signed}"
    | [] => throw s!"{case.id}: retained model has no field '{projectedField.path}'"
    | _ => throw s!"{case.id}: retained model has duplicate field '{projectedField.path}'"
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

def main : IO Unit := do
  let root : System.FilePath := "evidence/kernel-30.8.1"
  let bundle ← orThrow "projection.json"
    (Bundle.fromJson (← readJson (root / "projection.json")))
  orThrow "projection.json" bundle.validate
  for case in bundle.cases do
    checkCase root bundle case
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
  let total := bundle.cases.length + iterationBundle.cases.length + correlationBundle.cases.length
  IO.println s!"kernel evidence: {total}/{total} projections agree ({bundle.kernelVersion})"
