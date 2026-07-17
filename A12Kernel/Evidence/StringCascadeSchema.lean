import Lean.Data.Json

/-! # A12Kernel.Evidence.StringCascadeSchema — closed direct-cascade transport

This module decodes only the input-only scenario and `compute-observation-v1` shapes needed by the retained direct String-cascade capsule. It preserves raw list order and multiplicity. Relational packet checks and semantic replay remain separate.
-/

namespace A12Kernel.Evidence.StringCascade

open Lean

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

private def requireOneOfMembers (context : String) (json : Json)
    (expected : List (List String)) : Except String Unit := do
  let actual ← objectNames context json
  if !(expected.any (sameInventory actual)) then
    throw s!"{context} has unknown, missing, or duplicate members"

inductive Availability where
  | available
  | notExposedByRunner
  deriving Repr, DecidableEq

namespace Availability

def fromString (context : String) : String → Except String Availability
  | "available" => pure .available
  | "notExposedByRunner" => pure .notExposedByRunner
  | other => throw s!"{context}: unsupported availability '{other}'"

end Availability

structure ValueView where
  availability : Availability
  kind : Option String
  value : Option String
  deriving Repr, DecidableEq

namespace ValueView

def fromJson (context : String) (json : Json) : Except String ValueView := do
  let availability ← Availability.fromString context (← member json "availability" context)
  match availability with
  | .notExposedByRunner =>
      requireMembers context json ["availability"]
      pure { availability, kind := none, value := none }
  | .available =>
      requireOneOfMembers context json [
        ["availability", "value"],
        ["availability", "kind", "value"]]
      let names ← objectNames context json
      let kind ← if names.contains "kind" then
        some <$> member json "kind" context
      else
        pure none
      let value : String ← member json "value" context
      pure { availability, kind, value := some value }

end ValueView

structure TransportValue where
  typed : ValueView
  rendered : ValueView
  deriving Repr, DecidableEq

namespace TransportValue

def fromJson (context : String) (json : Json) : Except String TransportValue := do
  requireMembers context json ["typed", "rendered"]
  let typed ← ValueView.fromJson (context ++ ".typed") (← json.getObjVal? "typed")
  let rendered ← ValueView.fromJson (context ++ ".rendered") (← json.getObjVal? "rendered")
  match typed.availability, typed.kind, typed.value with
  | .available, some "STRING", some _ => pure ()
  | .available, _, _ => throw s!"{context}: available typed value must be a STRING"
  | .notExposedByRunner, none, none => pure ()
  | _, _, _ => throw s!"{context}: malformed typed value availability"
  match rendered.availability, rendered.kind, rendered.value with
  | .available, none, some _ => pure ()
  | .notExposedByRunner, none, none => pure ()
  | _, _, _ => throw s!"{context}: malformed rendered value availability"
  match typed.value, rendered.value with
  | some typed, some rendered =>
      if typed != rendered then
        throw s!"{context}: typed and rendered String values disagree"
  | _, _ => pure ()
  pure { typed, rendered }

def text? (value : TransportValue) : Option String :=
  value.typed.value.orElse fun _ => value.rendered.value

end TransportValue

structure CleanEntry where
  target : String
  declaredComputation : String
  value : TransportValue
  deriving Repr, DecidableEq

namespace CleanEntry

def fromJson (context : String) (json : Json) : Except String CleanEntry := do
  requireMembers context json ["target", "declaredComputation", "value"]
  pure {
    target := ← member json "target" context
    declaredComputation := ← member json "declaredComputation" context
    value := ← TransportValue.fromJson (context ++ ".value")
      (← json.getObjVal? "value") }

end CleanEntry

structure ErrorCause where
  availability : Availability
  code : Option String
  messageType : Option String
  errorPointer : Option String
  deriving Repr, DecidableEq

namespace ErrorCause

def fromJson (context : String) (json : Json) : Except String ErrorCause := do
  let availability ← Availability.fromString context (← member json "availability" context)
  match availability with
  | .notExposedByRunner =>
      requireMembers context json ["availability"]
      pure {
        availability
        code := none
        messageType := none
        errorPointer := none }
  | .available =>
      requireMembers context json [
        "availability", "code", "messageType", "errorPointer"]
      pure {
        availability
        code := some (← member json "code" context)
        messageType := some (← member json "messageType" context)
        errorPointer := some (← member json "errorPointer" context) }

end ErrorCause

structure ErrorEntry where
  target : String
  declaredComputation : String
  attempted : TransportValue
  cause : ErrorCause
  deriving Repr, DecidableEq

namespace ErrorEntry

def fromJson (context : String) (json : Json) : Except String ErrorEntry := do
  requireMembers context json [
    "target", "declaredComputation", "attempted", "cause"]
  pure {
    target := ← member json "target" context
    declaredComputation := ← member json "declaredComputation" context
    attempted := ← TransportValue.fromJson (context ++ ".attempted")
      (← json.getObjVal? "attempted")
    cause := ← ErrorCause.fromJson (context ++ ".cause")
      (← json.getObjVal? "cause") }

end ErrorEntry

structure ClearedEntry where
  target : String
  declaredComputation : String
  deriving Repr, DecidableEq

namespace ClearedEntry

def fromJson (context : String) (json : Json) : Except String ClearedEntry := do
  requireMembers context json ["target", "declaredComputation"]
  pure {
    target := ← member json "target" context
    declaredComputation := ← member json "declaredComputation" context }

end ClearedEntry

inductive AppliedState where
  | absent
  | presentEmpty
  | noValueIndeterminate
  | presentValue (value : TransportValue)
  deriving Repr, DecidableEq

structure AppliedEntry where
  pointer : String
  state : AppliedState
  deriving Repr, DecidableEq

namespace AppliedEntry

def fromJson (context : String) (json : Json) : Except String AppliedEntry := do
  let stateTag : String ← member json "state" context
  let pointer : String ← member json "pointer" context
  let state ← match stateTag with
    | "absent" =>
        requireMembers context json ["pointer", "state"]
        pure .absent
    | "presentEmpty" =>
        requireMembers context json ["pointer", "state"]
        pure .presentEmpty
    | "noValueIndeterminate" =>
        requireMembers context json ["pointer", "state"]
        pure .noValueIndeterminate
    | "presentValue" =>
        requireMembers context json ["pointer", "state", "value"]
        let value ← TransportValue.fromJson (context ++ ".value")
          (← json.getObjVal? "value")
        match value.text? with
        | some text =>
            if text.isEmpty then
              throw s!"{context}: presentValue must not encode an empty stored String"
            pure (.presentValue value)
        | none =>
            throw s!"{context}: presentValue must expose a String value"
    | other => throw s!"{context}: unsupported applied state '{other}'"
  pure { pointer, state }

end AppliedEntry

structure Channel (α : Type) where
  availability : Availability
  granularity : String
  order : String
  entries : List α
  deriving Repr, DecidableEq

namespace Channel

def fromJson (context : String) (parseEntry : String → Json → Except String α)
    (json : Json) : Except String (Channel α) := do
  requireMembers context json ["availability", "granularity", "order", "entries"]
  let availability ← Availability.fromString context (← member json "availability" context)
  let granularity : String ← member json "granularity" context
  let order : String ← member json "order" context
  let entriesJson : List Json ← member json "entries" context
  let entries ← entriesJson.zipIdx.mapM fun (entry, index) =>
    parseEntry s!"{context}.entries[{index}]" entry
  match availability with
  | .available =>
      if order != "observed" then
        throw s!"{context}: an available channel must retain observed order"
  | .notExposedByRunner =>
      if granularity != "notExposed" || order != "notApplicable" || !entries.isEmpty then
        throw s!"{context}: an unavailable channel must expose no entries"
  pure { availability, granularity, order, entries }

end Channel

structure ConsumedModel where
  ref : String
  suppliedSha256 : String
  adaptedSha256 : String
  deriving Repr, DecidableEq

structure ConsumedDocument where
  placements : Nat
  canonicalSha256 : String
  deriving Repr, DecidableEq

structure Observation where
  caseId : String
  runner : String
  status : String
  statusDetail : Option String
  consumedModel : ConsumedModel
  consumedDocument : ConsumedDocument
  withoutErrors : Channel CleanEntry
  changedSubset : Channel CleanEntry
  withErrors : Channel ErrorEntry
  cleared : Channel ClearedEntry
  formalErrorsInOperands : Channel Unit
  appliedState : Channel AppliedEntry
  deriving Repr, DecidableEq

namespace Observation

private def parseNoEntry (context : String) (_json : Json) : Except String Unit :=
  throw s!"{context}: the direct-cascade capsule admits no operand formal errors"

def fromJson (json : Json) : Except String Observation := do
  requireMembers "compute observation" json [
    "schema", "caseId", "runner", "status", "statusDetail",
    "consumedModel", "consumedDocument", "channels"]
  let schema : String ← member json "schema" "compute observation"
  if schema != "compute-observation-v1" then
    throw s!"compute observation: unsupported schema '{schema}'"
  let consumedModelJson ← json.getObjVal? "consumedModel"
  requireMembers "compute observation.consumedModel" consumedModelJson [
    "ref", "suppliedSha256", "adaptedSha256"]
  let consumedDocumentJson ← json.getObjVal? "consumedDocument"
  requireMembers "compute observation.consumedDocument" consumedDocumentJson [
    "placements", "canonicalSha256"]
  let channels ← json.getObjVal? "channels"
  requireMembers "compute observation.channels" channels [
    "withoutErrors", "changedSubset", "withErrors", "cleared",
    "formalErrorsInOperands", "appliedState"]
  let formalErrorsInOperands ← Channel.fromJson
    "compute observation.channels.formalErrorsInOperands" parseNoEntry
    (← channels.getObjVal? "formalErrorsInOperands")
  pure {
    caseId := ← member json "caseId" "compute observation"
    runner := ← member json "runner" "compute observation"
    status := ← member json "status" "compute observation"
    statusDetail := ← member json "statusDetail" "compute observation"
    consumedModel := {
      ref := ← member consumedModelJson "ref" "compute observation.consumedModel"
      suppliedSha256 := ← member consumedModelJson "suppliedSha256"
        "compute observation.consumedModel"
      adaptedSha256 := ← member consumedModelJson "adaptedSha256"
        "compute observation.consumedModel" }
    consumedDocument := {
      placements := ← member consumedDocumentJson "placements"
        "compute observation.consumedDocument"
      canonicalSha256 := ← member consumedDocumentJson "canonicalSha256"
        "compute observation.consumedDocument" }
    withoutErrors := ← Channel.fromJson
      "compute observation.channels.withoutErrors" CleanEntry.fromJson
      (← channels.getObjVal? "withoutErrors")
    changedSubset := ← Channel.fromJson
      "compute observation.channels.changedSubset" CleanEntry.fromJson
      (← channels.getObjVal? "changedSubset")
    withErrors := ← Channel.fromJson
      "compute observation.channels.withErrors" ErrorEntry.fromJson
      (← channels.getObjVal? "withErrors")
    cleared := ← Channel.fromJson
      "compute observation.channels.cleared" ClearedEntry.fromJson
      (← channels.getObjVal? "cleared")
    formalErrorsInOperands
    appliedState := ← Channel.fromJson
      "compute observation.channels.appliedState" AppliedEntry.fromJson
      (← channels.getObjVal? "appliedState") }

end Observation

structure Placement where
  kind : String
  path : String
  reps : List Nat
  value : Option String
  deriving Repr, DecidableEq

namespace Placement

def fromJson (context : String) (json : Json) : Except String Placement := do
  let kind : String ← member json "kind" context
  match kind with
  | "GROUP" =>
      requireMembers context json ["kind", "path", "reps"]
      pure {
        kind
        path := ← member json "path" context
        reps := ← member json "reps" context
        value := none }
  | "FIELD" =>
      requireMembers context json ["kind", "path", "reps", "value"]
      pure {
        kind
        path := ← member json "path" context
        reps := ← member json "reps" context
        value := some (← member json "value" context) }
  | other => throw s!"{context}: unsupported placement kind '{other}'"

end Placement

structure ScenarioCase where
  caseId : String
  modelRef : String
  operation : String
  placements : List Placement
  probes : List String
  deriving Repr, DecidableEq

structure ScenarioRequest where
  scenarioId : String
  scenarioVersion : String
  operationSchema : String
  capabilitiesSchema : String
  capabilitiesVersion : String
  worldProfile : String
  locale : String
  modelRef : String
  modelSha256 : String
  requiredRunners : List String
  qualificationPolicy : String
  observationRequirementId : String
  observationRequirementVersion : String
  requiredChannels : List String
  comparisonProjections : List String
  cases : List ScenarioCase
  deriving Repr, DecidableEq

namespace ScenarioRequest

private def parseCase (index : Nat) (json : Json) : Except String ScenarioCase := do
  let context := s!"cascade scenario case {index}"
  requireMembers context json [
    "caseId", "modelRef", "operation", "placements", "probes"]
  let placementsJson : List Json ← member json "placements" context
  pure {
    caseId := ← member json "caseId" context
    modelRef := ← member json "modelRef" context
    operation := ← member json "operation" context
    placements := ← placementsJson.zipIdx.mapM fun (placement, placementIndex) =>
      Placement.fromJson s!"{context}.placements[{placementIndex}]" placement
    probes := ← member json "probes" context }

def fromJson (json : Json) : Except String ScenarioRequest := do
  requireMembers "cascade scenario request" json [
    "schema", "scenarioSet", "operationSchema", "requiredCapabilities", "world",
    "models", "requiredRunners", "qualificationPolicy", "observationRequirement", "cases"]
  let schema : String ← member json "schema" "cascade scenario request"
  if schema != "capture-scenario-set-v1" then
    throw s!"cascade scenario request: unsupported schema '{schema}'"
  let scenario ← json.getObjVal? "scenarioSet"
  requireMembers "cascade scenario request.scenarioSet" scenario ["id", "version"]
  let capabilities ← json.getObjVal? "requiredCapabilities"
  requireMembers "cascade scenario request.requiredCapabilities" capabilities ["schema", "version"]
  let world ← json.getObjVal? "world"
  requireMembers "cascade scenario request.world" world ["profile", "locale"]
  let models : List Json ← member json "models" "cascade scenario request"
  if models.length != 1 then
    throw "cascade scenario request must contain exactly one model"
  let model ← match models with
    | [model] => pure model
    | _ => throw "cascade scenario request must contain exactly one model"
  requireMembers "cascade scenario request.models[0]" model ["ref", "sha256"]
  let requirement ← json.getObjVal? "observationRequirement"
  requireMembers "cascade scenario request.observationRequirement" requirement [
    "id", "version", "requiredChannels", "comparisonProjections"]
  let cases : List Json ← member json "cases" "cascade scenario request"
  pure {
    scenarioId := ← member scenario "id" "cascade scenario request.scenarioSet"
    scenarioVersion := ← member scenario "version" "cascade scenario request.scenarioSet"
    operationSchema := ← member json "operationSchema" "cascade scenario request"
    capabilitiesSchema := ← member capabilities "schema"
      "cascade scenario request.requiredCapabilities"
    capabilitiesVersion := ← member capabilities "version"
      "cascade scenario request.requiredCapabilities"
    worldProfile := ← member world "profile" "cascade scenario request.world"
    locale := ← member world "locale" "cascade scenario request.world"
    modelRef := ← member model "ref" "cascade scenario request.models[0]"
    modelSha256 := ← member model "sha256" "cascade scenario request.models[0]"
    requiredRunners := ← member json "requiredRunners" "cascade scenario request"
    qualificationPolicy := ← member json "qualificationPolicy" "cascade scenario request"
    observationRequirementId := ← member requirement "id"
      "cascade scenario request.observationRequirement"
    observationRequirementVersion := ← member requirement "version"
      "cascade scenario request.observationRequirement"
    requiredChannels := ← member requirement "requiredChannels"
      "cascade scenario request.observationRequirement"
    comparisonProjections := ← member requirement "comparisonProjections"
      "cascade scenario request.observationRequirement"
    cases := ← cases.zipIdx.mapM fun (case, index) => parseCase index case }

end ScenarioRequest

end A12Kernel.Evidence.StringCascade
