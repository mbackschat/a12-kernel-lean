import Lean.Data.Json
import A12Kernel.Elaboration.ModelConsistency
import A12Kernel.Reference.Dm.ModelFrame
import A12Kernel.Reference.Dm.Model
import A12Kernel.Reference.Dm.ModelConversion

/-! # Reading a DM-JSON model for the consistency check

The consistency check judges the authored model, so this reader keeps every element, a declaration the
validation-model converter drops included, and records only whether that conversion builds a model
(`convertModel`). It reads only the facts `ModelConsistency` consumes. An absent identifier, name or text
member reads as the empty text, which the check then reports; a field whose type is absent is a read
error, since no capture measures it.

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

/-- A fractional-digit count, a primitive `int` member: absent reads as zero. -/
private def whole (json : Json) (key : String) : Except String Int := do
  pure ((← primitiveIntMember? json key).getD 0)

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

private def readField (definitions : List (String × Json)) (id name : String)
    (body : Json) : Except String ConsistencyField := do
  let declared ← readConsistencyFieldType (← body.getObjVal? "fieldType")
  let effective ← match declared with
    | .typeDefinition _ =>
        match resolveTypeDefinition definitions body with
        | .error _ => pure none
        | .ok resolved => some <$> readConsistencyFieldType (← resolved.getObjVal? "fieldType")
    | other => pure (some other)
  pure { id, name, declared, effective
         requirednessDeclared := (body.getObjVal? "requirednessConfig").toOption.any (· != .null) }

private partial def readElement (definitions : List (String × Json))
    (element : Json) : Except String ConsistencyElement := do
  let kind ← element.getObjValAs? String "type"
  let body ← elementBody element kind
  let id := text element "id"
  let name := elementName element
  match kind with
  | "Group" =>
      -- A negative count reads as a single group and zero as zero, as this reader read them before.
      let count := match ← primitiveIntMember? body "repeatability" with
        | some count => if 0 ≤ count then count.toNat else 1
        | none => 1
      -- An index or sort name binds as its text whatever scalar is written, an array or object leaving no model.
      let sortNames ← (← members body "sortFields").mapM fun entry => do pure ((← frameText entry "name").getD "")
      pure (.group id name count
        (body.getObjValAs? String "usageType").toOption
        (← frameText body "indexFieldName")
        sortNames
        (← (← groupElements body).mapM (readElement definitions)))
  | "Field" => .field <$> readField definitions id name body
  | "Rule" => pure (.rule id name (text body "errorCondition") (text body "errorEntityRelPath"))
  | "Computation" =>
      pure (.computation id name (text body "computedFieldRelPath")
        ((← members body "computationAlternatives").map (text · "operation")))
  | other => throw s!"element {other}"

/-- Read the model the consistency check judges. An absent condition language is en_US. -/
def readConsistencyModel (json : Json) : Except String ConsistencyModel := do
  let frame ← bindModelFrame json
  let content := frame.content
  bindLocalizedTextMembers content
  bindModelMembers frame
  let definitions := frame.typeDefinitions.toList
  let rootGroups := frame.rootGroups.toList
  pure {
    typeDefinitions := definitions.map fun definition =>
      { id := text definition "id", name := text definition "name" }
    rootGroups := ← rootGroups.mapM (readElement (definitions.map fun definition =>
      (text definition "id", definition)))
    conditionLanguage := frame.conditionLanguage.getD "en_US"
    declaredLocales := ← headerLocales json
    frameCheckFailure? := frame.checkFailure?
    validationModelUnbuilt := (convertModel frame).unbuilt }

/-- Read the model and run the consistency check. -/
def checkModelConsistency (json : Json) : Except String ModelConsistencyOutcome := do
  ModelConsistency.check (← readConsistencyModel json)

end A12Kernel.Dm
