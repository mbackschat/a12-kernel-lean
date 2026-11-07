import Lean.Data.Json
import A12Kernel.Elaboration.Enumeration
import A12Kernel.Elaboration.ErrorTargetDeclaration
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
  or exactly one of three names;
* a container, an object or an array, in a rule's `errorEntityRelPath` or `errorCondition` or in a computation
  alternative's `precondition` leaves no model (`refuseContainer`);
* an element's `name` as a text member: an object or an array leaves no model (a12-dmkits
  `CheckerConverterSentenceAgreementTest` at `1124b523f`, kernel 31.1.1), while an absent or `null` name
  and every string bind. A number or Boolean name binds as its text as the other text members of the model
  do, an assumption no measurement settles for element names.

* an Enumeration's categories (`boundCategories`): a `name` that is `null`, an object or an array, and a token
  that is an object or an array, leave no model, while an absent or empty name and a `null` or empty token are
  values the readers judge.

A member the Kernel does not know is read past, so the pass never refuses one. It binds no row-key
nomination: the readers that judge those do. A present empty member is a value, judged by its own reader.
-/

namespace A12Kernel.Dm

open Lean A12Kernel

/-- A member the Kernel reads and never defaults: absent or `null` leaves no model. -/
private def requireValue (parent : Json) (key : String) : Except String Unit :=
  match parent.getObjVal? key with
  | .ok .null | .error _ => throw s!"member {key} is absent or null"
  | .ok _ => pure ()

/-- The element kinds a group body may hold. -/
def elementKinds : List String := ["Group", "Field", "Rule", "Computation"]

/-- The name an element declares, read as `bindModelMembers` binds it: an absent or `null` name is the
empty name, which every reader then treats as blank. -/
def elementName (element : Json) : String :=
  match frameText element "name" with
  | .ok (some name) => name
  | _ => ""

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

/-- The categories of an `EnumerationType` body as the Kernel's reader binds them, in declared order. A name
binds as a text member does, so an absent one is the empty name, which reads as the same null key as `""`, and
a `null`, an object or an array leaves no model (a12-dmkits `CheckerEmptyMemberAgreementTest` at `1124b523f`,
kernel 31.1.1). A token list that is absent or `null` is empty, and each token binds as a string: a number or
a Boolean as its text, `null` as the empty token, which is no token as a blank one is not (peer KF660,
`CheckerCategoryTokenAgreementTest`), and an object or an array leaves no model. A `categories` member that
is no list binds no category, as the readers have always read it. -/
def boundCategories (body : Json) : Except String (List EnumerationCategoryDeclaration) := do
  let entries : List Json := match body.getObjVal? "categories" with
    | .ok (.arr entries) => entries.toList
    | _ => []
  entries.mapM fun entry => do
    let .obj _ := entry | throw s!"category {entry.compress} is no object"
    let name := (← frameText entry "name" (nonNull := true)).getD ""
    let tokens ← match ← frameList entry "values" with
      | none => pure []
      | some tokens => tokens.toList.mapM fun
          | .null => pure ""
          | token => do
              let some text ← scalarText? token | throw s!"category token {token.compress} is no string"
              pure text
    pure { name, tokens }

/-- Whether an `EnumerationType` body declares no value: `values` absent or an empty list. A `null` list reads
as absent, as the other list members of the model do, which no measurement settles. -/
def enumerationDeclaresNoValues (body : Json) : Bool :=
  match body.getObjVal? "values" with
  | .error _ | .ok .null => true
  | .ok (.arr entries) => entries.isEmpty
  | .ok _ => false

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
  if typeName == "EnumerationType" then discard <| boundCategories body

/-- A rule's severity: absent, or exactly one of the three names. -/
private def bindSeverity (rule : Json) : Except String Unit :=
  match rule.getObjVal? "severity" with
  | .error _ | .ok (.str "ERROR") | .ok (.str "WARNING") | .ok (.str "INFO") => pure ()
  | .ok other => throw s!"severity {other.compress} is no severity"

/-- A string slot holding an object or an array leaves no model, every container shape alike (a12-dmkits
`StringSlotContainerLawsTest` at `35a09951f`, kernel 31.1.1, KF304). Only containers are refused here: a
scalar in these slots is unmeasured and keeps the readers' own reading. -/
private def refuseContainer (body : Json) (key : String) : Except String Unit :=
  match body.getObjVal? key with
  | .ok (.obj _) | .ok (.arr _) => throw s!"model member {key} is a container"
  | _ => pure ()

/-- A sort entry as kernel 31.3.1 binds it (a12-dmkits KF680, amended at `1d6762340`): an object whose `name`
is a scalar and whose `order` is one of the enum's two constants. The order text is trimmed at both ends of
characters at or below U+0020, as Java's `trim` does, and must then be `ASC`, `DESC`, `0` or `1`; the integer
`0` or `1`, `-0` included, binds too. `"ASC "` and `"DESC\n"` are measured admitted and `"ASC"` followed by an
em space unreadable, so the trim stops at U+0020. -/
private def bindSortEntry (entry : Json) : Except String Unit := do
  let .obj _ := entry | throw "sort entry is no object"
  requireValue entry "name"
  refuseContainer entry "name"
  let admitted := match entry.getObjVal? "order" with
    | .ok (.str text) => ["ASC", "DESC", "0", "1"].contains (javaTrim text)
    | .ok (.num value) => value.exponent == 0 && (value.mantissa == 0 || value.mantissa == 1)
    | _ => false
  if !admitted then throw "sort entry order is unreadable"

/-- The DM-JSON member holding a rule's possible-cause filter, and its two lists in slot order. -/
def possibleCauseFilterKey : String := "filterForPossiblyCausingEntities"

def possibleCauseListKey : CustomErrorEntitySlot → String
  | .ifFilled => "entitiesEnabledAsPossibleCauseIfFilled"
  | .ifNotFilled => "entitiesEnabledAsPossibleCauseIfNotFilled"

/-- One possible-cause entry's `relativePath` as its text, bound as every scalar member is (`scalarText?`): a
string, or an integer read as its text (a12-dmkits KF682, kernel 31.3.1). A Boolean is read as its text too,
which no row measures. An entry that is no object, and a path that is absent, `null` or a container, leave
no model. -/
private def possibleCausePath (entry : Json) : Except String String := do
  let .obj _ := entry | throw "possible-cause entry is no object"
  let some text ← scalarText? ((entry.getObjVal? "relativePath").toOption.getD .null)
    | throw "possible-cause entry has no readable relativePath"
  pure text

/-- How many `..` steps a relative path text leads with, the run a reader compares with the levels between its
base and the technical model root. -/
def leadingUpSteps (text : String) : Nat :=
  ((text.splitOn "/").takeWhile (· == "..")).length

/-- A rule's possible-cause filter as kernel 31.3.1 reads it (a12-dmkits KF682): `none` when the member is
absent or `null`, else both lists, an absent list empty. A filter that is no object, a list that is no
list, `null` included, and an unreadable entry leave no model, and so does an absolute path or a leading
`..` run climbing above the technical model root from the rule's group, `depth` levels below that root.
An unknown key and an extra member of an entry are read past. -/
def readPossibleCauseFilter (depth : Nat) (body : Json) : Except String (Option CustomErrorEntityDeclaration) := do
  let filter ← match body.getObjVal? possibleCauseFilterKey with
    | .error _ | .ok .null => return none
    | .ok filter@(.obj _) => pure filter
    | .ok _ => throw "possible-cause filter is no object"
  let slot (slot : CustomErrorEntitySlot) : Except String (List String) := do
    let entries := (← frameList filter (possibleCauseListKey slot) (nonNull := true)).getD #[]
    entries.toList.mapM fun entry => do
      let path ← possibleCausePath entry
      if path.startsWith "/" then throw s!"possible-cause path {path} is absolute"
      if depth < leadingUpSteps path then
        throw s!"possible-cause path {path} climbs above the model root"
      pure path
  pure (some { ifFilled := ← slot .ifFilled, ifNotFilled := ← slot .ifNotFilled })

/-- Bind one element and, below a group, every element under it. `fuel` bounds the nesting depth, and
`depth` is the element's own: the length of the group path holding it. -/
private def bindElement : Nat → Nat → Json → Except String Unit
  | 0, _, _ => throw "model elements nest deeper than the model is long"
  | fuel + 1, depth, element => do
      discard <| frameText element "name"
      let some kind := (element.getObjValAs? String "type").toOption | pure ()
      let body ← elementBody element kind
      match kind with
      | "Group" =>
          discard <| primitiveIntMember? body "repeatability"
          if let .ok (.arr sorts) := body.getObjVal? "sortFields" then
            for sort in sorts do bindSortEntry sort
          for child in ← groupElements body do bindElement fuel (depth + 1) child
      | "Field" =>
          for key in ["global", "transient"] do discard <| booleanMember? body key
          bindFieldType (← requireFieldType body)
      | "Rule" =>
          for key in ["errorCode", "errorEntityRelPath", "errorCondition"] do requireValue body key
          for key in ["errorEntityRelPath", "errorCondition"] do refuseContainer body key
          bindSeverity body
          discard <| readPossibleCauseFilter depth body
      | "Computation" =>
          requireValue body "computedFieldRelPath"
          if let .ok (.arr alternatives) := body.getObjVal? "computationAlternatives" then
            for alternative in alternatives do refuseContainer alternative "precondition"
      | _ => pure ()

/-- Bind every member of a framed model that a DM reader reads before it judges anything, failing on the
first the Kernel cannot bind. Run it once, right after the localized-text members. -/
def bindModelMembers (frame : ModelFrame) : Except String Unit := do
  for key in ["immutable", "metaData"] do discard <| booleanMember? frame.info key
  discard <| intMember? frame.info "baseYear"
  discard <| booleanMember? frame.config "fieldRefByShortNameAllowed"
  for definition in frame.typeDefinitions do
    if let .ok fieldType := definition.getObjVal? "fieldType" then bindFieldType fieldType
  for root in frame.rootGroups do bindElement frame.nestingFuel 0 root

end A12Kernel.Dm
