import Lean.Data.Json
import A12Kernel.Reference.Dm.MemberBinding
import A12Kernel.Reference.Dm.ModelFrame

/-! # How the Kernel binds a model's elements, type bodies and rule members

Kernel 31.1.1 deserializes a model with Jackson 3 before any check, and a member it cannot bind leaves
no model at all, whatever else the model holds (a12-dmkits `1124b523f`; peer KF654, 2026-11-02).
The three DM readers (the model reader, the consistency reader and the declaration walk) each call this
one pass first, so a binding failure is the same read failure on all of them rather than a refusal one
reader happens to notice. The pass walks every type definition, referenced or not, and every group
recursively, and binds:

* every primitive `boolean` and `int` member and every boxed `Integer` member of the model info, the
  configuration, a group, a field and a field type's body, by the laws of `MemberBinding`;
* a body as an object: a Group's missing or `null` body is an empty group, built and checked like `{}`,
  while a Field, a Rule and a Computation have no empty reading, and no other non-object body binds;
* a field type: `UnspecifiedType` is a type the Kernel no longer reads, with a body or without one, while
  a field type written without its body is the same type with an empty body, on all twelve types;
* the members the Kernel reads and never defaults: a rule's `errorCode`, `errorEntityRelPath` and
  `errorCondition`, a computation's `computedFieldRelPath` and a sort field's `name` leave no model when
  absent or `null`, and a hint entry's `locale` and `values` when absent; a rule's `severity` is absent
  or exactly one of three names.

A member the Kernel does not know is read past, so the pass never refuses one. It binds no element name,
row-key nomination or enumeration category: the readers that judge those do. A present empty member is a
value, judged by its own reader.
-/

namespace A12Kernel.Dm

open Lean A12Kernel

/-- A member the Kernel reads and never defaults: absent or `null` leaves no model. -/
private def requireValue (parent : Json) (key : String) : Except String Unit :=
  match parent.getObjVal? key with
  | .ok .null | .error _ => throw s!"member {key} is absent or null"
  | .ok _ => pure ()

private def elementKinds : List String := ["Group", "Field", "Rule", "Computation"]

/-- The body an element's own kind names, bound as an object. A Group's missing or `null` body is an
empty group; the other three kinds have no empty reading, and no kind binds another non-object body. An
element of any other kind has no body to bind. -/
def elementBody (element : Json) (kind : String) : Except String Json :=
  match element.getObjVal? kind with
  | .ok body@(.obj _) => pure body
  | .ok .null | .error _ =>
      if kind == "Group" || !elementKinds.contains kind then pure (Json.mkObj [])
      else throw s!"{kind} element has no body"
  | .ok other =>
      if elementKinds.contains kind then throw s!"{kind} body {other.compress} is no object"
      else pure (Json.mkObj [])

/-- The child elements of a group's body: none when absent, and no other list kind, `null` included, binds.
Measured on an included model's root group (a12-dmkits `WorkspaceIncludeStructureKernelTest` at
`1124b523f`); that the entry's groups bind the member alike is assumed, unmeasured on 31.1.1. -/
def groupElements (body : Json) : Except String (List Json) :=
  match body.getObjVal? "elements" with
  | .error _ => pure []
  | .ok (.arr children) => pure children.toList
  | .ok other => throw s!"group elements {other.compress} is no list"

/-- The integer members of a field type's body, by type name, each with whether it is a primitive `int`
(`true`) or a boxed `Integer`. Every other member of those bodies is read by its own law. -/
def fieldTypeIntegerMembers : String → List (String × Bool)
  | "NumberType" =>
      [("minFractionalDigits", true), ("maxFractionalDigits", true), ("minLength", false), ("maxLength", false),
        ("maxIntegerDigits", false)]
  | "StringType" | "CustomFieldType" => [("minLength", false), ("maxLength", false)]
  | _ => []

/-- A hint entry's locale and values, which the Kernel reads without a default. -/
private def bindHintList (body : Json) : Except String Unit :=
  match body.getObjVal? "hintList" with
  | .ok (.arr entries) => entries.forM fun entry => do
      for key in ["locale", "values"] do requireMember entry key
  | _ => pure ()

/-- The twelve field types the Kernel reads, by their exact discriminator. -/
def readFieldTypes : List String :=
  ["StringType", "NumberType", "BooleanType", "ConfirmType", "EnumerationType", "DateType", "TimeType",
    "DateTimeType", "DateFragmentType", "DateRangeType", "CustomFieldType", "TypeDefType"]

/-- A field's `fieldType`: an object whose `type` is one of the twelve read types, exactly spelled. No
member, `null`, a scalar, a list, `{}`, a missing or wrong-case discriminator and an unknown name leave no
model (a12-dmkits `FieldTypeBindingLawsTest` at `1124b523f`, kernel 31.1.1). A type definition's envelope
is not measured and stays lenient. -/
private def requireFieldType (field : Json) : Except String Json := do
  let .ok fieldType@(.obj _) := field.getObjVal? "fieldType" | throw "field has no fieldType object"
  let .ok typeName := fieldType.getObjValAs? String "type" | throw "fieldType has no type"
  unless readFieldTypes.contains typeName || typeName == "UnspecifiedType" do
    throw s!"field type {typeName} is no type the Kernel reads"
  pure fieldType

/-- Bind a `fieldType` object: its `type` names the one body that is read, and a body that is absent is
the empty body, which binds nothing. -/
def bindFieldType (fieldType : Json) : Except String Unit := do
  let some typeName := (fieldType.getObjValAs? String "type").toOption | pure ()
  if typeName == "UnspecifiedType" then throw "UnspecifiedType is no field type the Kernel reads"
  let .ok body@(.obj _) := fieldType.getObjVal? typeName | pure ()
  for key in fieldTypeBooleanMembers typeName do discard <| booleanMember? body key
  for (key, primitive) in fieldTypeIntegerMembers typeName do
    discard <| if primitive then primitiveIntMember? body key else intMember? body key
  if typeName == "StringType" then bindHintList body

/-- A rule's severity: absent, or exactly one of the three names. -/
private def bindSeverity (rule : Json) : Except String Unit :=
  match rule.getObjVal? "severity" with
  | .error _ | .ok (.str "ERROR") | .ok (.str "WARNING") | .ok (.str "INFO") => pure ()
  | .ok other => throw s!"severity {other.compress} is no severity"

/-- Bind one element and, below a group, every element under it. `fuel` bounds the nesting depth. -/
private def bindElement : Nat → Json → Except String Unit
  | 0, _ => throw "model elements nest deeper than the model is long"
  | fuel + 1, element => do
      let some kind := (element.getObjValAs? String "type").toOption | pure ()
      let body ← elementBody element kind
      match kind with
      | "Group" =>
          discard <| primitiveIntMember? body "repeatability"
          if let .ok (.arr sorts) := body.getObjVal? "sortFields" then
            for sort in sorts do requireValue sort "name"
          for child in ← groupElements body do bindElement fuel child
      | "Field" =>
          for key in ["global", "transient"] do discard <| booleanMember? body key
          bindFieldType (← requireFieldType body)
      | "Rule" =>
          for key in ["errorCode", "errorEntityRelPath", "errorCondition"] do requireValue body key
          bindSeverity body
      | "Computation" => requireValue body "computedFieldRelPath"
      | _ => pure ()

/-- Bind every member of a framed model that a DM reader reads before it judges anything, failing on the
first the Kernel cannot bind. Run it once, right after the localized-text members. -/
def bindModelMembers (frame : ModelFrame) : Except String Unit := do
  for key in ["immutable", "metaData"] do discard <| booleanMember? frame.info key
  discard <| intMember? frame.info "baseYear"
  discard <| booleanMember? frame.config "fieldRefByShortNameAllowed"
  for definition in frame.typeDefinitions do
    if let .ok fieldType := definition.getObjVal? "fieldType" then bindFieldType fieldType
  -- Nesting never exceeds the characters of the text that holds it.
  let fuel := frame.content.compress.length + 1
  for root in frame.rootGroups do bindElement fuel root

end A12Kernel.Dm
