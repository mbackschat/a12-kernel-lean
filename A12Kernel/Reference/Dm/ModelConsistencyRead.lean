import Lean.Data.Json
import A12Kernel.Elaboration.ModelConsistency
import A12Kernel.Reference.Dm.Model

/-! # Reading a DM-JSON model for the consistency check

The consistency check judges the authored model, so this reader keeps every field, those removed by the
variant filter included, and marks each by `inVariant` instead of dropping it as `readModel` does. It
reads only the facts `ModelConsistency` consumes. An absent identifier, name or text member reads as the
empty text, which the check then reports; a field whose type is absent is a read error, since no capture
measures it.

It is an input adapter, differentially tested by the model-consistency captures rather than proved.
-/

namespace A12Kernel.Dm

open Lean

private def text (json : Json) (key : String) : String :=
  (json.getObjValAs? String key).toOption.getD ""

/-- The members of an array-valued key; an absent or `null` key is empty. -/
private def members (json : Json) (key : String) : Except String (List Json) :=
  match json.getObjVal? key with
  | .error _ | .ok .null => pure []
  | .ok value => (value.getArr?).map Array.toList

private def whole (json : Json) (key : String) : Except String Int :=
  match json.getObjVal? key with
  | .error _ | .ok .null => pure 0
  | .ok value => fromJson? value

/-- A field type from its `fieldType` object; the body sits under the type's own name. -/
private def readConsistencyFieldType (fieldType : Json) : Except String ConsistencyFieldType := do
  let typeName ← fieldType.getObjValAs? String "type"
  let body := (fieldType.getObjVal? typeName).toOption.getD (Json.mkObj [])
  match typeName with
  | "NumberType" =>
      pure (.number (← whole body "minFractionalDigits") (← whole body "maxFractionalDigits")
        (← decimalMember? body "minValue") (← decimalMember? body "maxValue"))
  | "StringType" => pure (.string (← booleanMember? body "noValueValidation") (← booleanMember? body "lineBreaksPermitted"))
  | "EnumerationType" =>
      pure (.enumeration ((← members body "categories").map (text · "name")))
  | "TypeDefType" => pure (.typeDefinition (text body "typeDefinitionId"))
  | other => pure (.other other)

private def readField (variant : Option String) (definitions : List (String × Json)) (id name : String)
    (body : Json) : Except String ConsistencyField := do
  let declared ← readConsistencyFieldType (← body.getObjVal? "fieldType")
  let effective ← match declared with
    | .typeDefinition _ =>
        match resolveTypeDefinition definitions body with
        | .error _ => pure none
        | .ok resolved => some <$> readConsistencyFieldType (← resolved.getObjVal? "fieldType")
    | other => pure (some other)
  pure { id, name, declared, effective
         requirednessDeclared := (body.getObjVal? "requirednessConfig").toOption.any (· != .null)
         inVariant := ← acceptedByVariant variant body }

private partial def readElement (variant : Option String) (definitions : List (String × Json))
    (element : Json) : Except String ConsistencyElement := do
  let kind ← element.getObjValAs? String "type"
  let body := (element.getObjVal? kind).toOption.getD (Json.mkObj [])
  let id := text element "id"
  let name := text element "name"
  match kind with
  | "Group" =>
      pure (.group id name ((body.getObjValAs? Nat "repeatability").toOption.getD 1)
        (body.getObjValAs? String "usageType").toOption
        (body.getObjValAs? String "indexFieldName").toOption
        ((← members body "sortFields").map (text · "name"))
        (← (← members body "elements").mapM (readElement variant definitions)))
  | "Field" => .field <$> readField variant definitions id name body
  | "Rule" => pure (.rule id name (text body "errorCondition") (text body "errorEntityRelPath")
      (← acceptedByVariant variant body))
  | "Computation" =>
      pure (.computation id name (text body "computedFieldRelPath")
        ((← members body "computationAlternatives").map (text · "operation"))
        (← acceptedByVariant variant body))
  | other => throw s!"element {other}"

/-- Read the model the consistency check judges, for the variant a field survives the filter of. An
absent condition language is en_US. -/
def readConsistencyModel (json : Json) (variant : Option String := none) :
    Except String ConsistencyModel := do
  let content ← json.getObjVal? "content"
  bindLocalizedTextMembers content
  let definitions ← members content "typeDefinitions"
  let rootGroups ← match content.getObjVal? "modelRoot" with
    | .error _ | .ok .null => pure []
    | .ok root => members root "rootGroups"
  pure {
    typeDefinitions := definitions.map fun definition =>
      { id := text definition "id", name := text definition "name" }
    rootGroups := ← rootGroups.mapM (readElement variant (definitions.map fun definition =>
      (text definition "id", definition)))
    conditionLanguage := ((content.getObjVal? "modelConfig").toOption.bind fun config =>
      (config.getObjVal? "conditionLanguage").toOption.bind fun language =>
        (language.getObjValAs? String "code").toOption).getD "en_US"
    declaredLocales := ← headerLocales json }

/-- Read the model for `variant` and run the consistency check. -/
def checkModelConsistency (json : Json) (variant : Option String := none) :
    Except String ModelConsistencyOutcome := do
  ModelConsistency.check (← readConsistencyModel json variant)

end A12Kernel.Dm
