import A12Kernel.Reference.Dm.ModelVerdictFixture
import A12Kernel.Reference.Dm.MemberBinding

/-! # What kernel 31.1.1's binding leaves of a model, on all three DM readers

The Kernel deserializes a model before any check, so a member it cannot bind leaves no model, and a
member it reads past or defaults leaves the same model as without it. Each cluster states one binding law
over every carrier it governs and asks it of the three readers at once: the model reader, the
consistency reader and the declaration walk. Each reader maps a model the Kernel does not bind to its own
error, so "no model" here is that error on all three; "reads" is the absence of that error on all three.
Equality rows compare the readers' whole output, so a reader that treats a member differently from its
twin shows up whichever output carries the difference.

Each cluster names the peer lock it mirrors. The elements outside this module are other steps': the
included models and workspaces, the version value and ordering members. An element's name binds in the
same pass, which [the converter locks](ConverterSentenceLocks.lean) state with the converter's sentences.
-/

namespace A12Kernel.Dm.ReaderBindingLocks

open Lean A12Kernel

private def baseText : String := r#"{
 "header":{"id":"Binding_DM","modelType":"document","modelVersion":"29.4.0","locales":[{"code":"en_US"}]},
 "content":{"modelInfo":{"name":"Binding"},
  "modelConfig":{"conditionLanguage":{"code":"en_US"}},
  "typeDefinitions":[
   {"id":"Unref","name":"Unref","fieldType":{"type":"NumberType","NumberType":{"maxFractionalDigits":2}}},
   {"id":"Refd","name":"Refd","fieldType":{"type":"NumberType","NumberType":{"maxFractionalDigits":2}}}],
  "modelRoot":{"rootGroups":[{"type":"Group","id":"/Form","name":"Form","Group":{"elements":[
   {"type":"Field","id":"/Form/Note","name":"Note","Field":{"fieldType":{"type":"StringType","StringType":{}}}},
   {"type":"Field","id":"/Form/Amount","name":"Amount","Field":{"fieldType":{"type":"NumberType","NumberType":{"maxFractionalDigits":2}}}},
   {"type":"Field","id":"/Form/Filed","name":"Filed","Field":{"fieldType":{"type":"DateType","DateType":{"format":"yyyy-MM-dd"}}}},
   {"type":"Field","id":"/Form/Tier","name":"Tier","Field":{"fieldType":{"type":"EnumerationType","EnumerationType":{"values":[{"value":"GOLD"},{"value":"SILVER"}]}}}},
   {"type":"Field","id":"/Form/Code","name":"Code","Field":{"fieldType":{"type":"CustomFieldType","CustomFieldType":{"name":"PolicyCode"}}}},
   {"type":"Field","id":"/Form/Hinted","name":"Hinted","Field":{"fieldType":{"type":"StringType","StringType":{"hintList":[{"locale":"en_US","values":["AB"]}]}}}},
   {"type":"Field","id":"/Form/Linked","name":"Linked","Field":{"fieldType":{"type":"TypeDefType","TypeDefType":{"typeDefinitionId":"Refd"}}}},
   {"type":"Group","id":"/Form/Rows","name":"Rows","Group":{"repeatability":3,"sortFields":[{"name":"K"}],"elements":[
     {"type":"Field","id":"/Form/Rows/K","name":"K","Field":{"fieldType":{"type":"StringType","StringType":{}}}}]}},
   {"type":"Rule","id":"/Form/R","name":"R","Rule":{"errorEntityRelPath":"../Note","errorCode":"R1","errorCondition":"FieldFilled(Note)","severity":"ERROR"}},
   {"type":"Computation","id":"/Form/C","name":"C","Computation":{"computedFieldRelPath":"../Amount","computationAlternatives":[{"operation":"1"}]}}
  ]}}]}}}"#

private def literal (text : String) : Json := (Json.parse text).toOption.getD .null

/-- A sound model with one carrier of every member the clusters vary. -/
private def base : Json := literal baseText

/-- `json` with the member at `path` set to `value`, or removed when `value` is `none`. A path segment
indexes an array when it is a number. -/
private def edited : List String → Option Json → Json → Json
  | [], _, json => json
  | [key], value, json => match json, key.toNat? with
      | .arr items, some index => match value with
          | some value => .arr (items.set! index value)
          | none => json
      | .obj members, _ => match value with
          | some value => json.setObjVal! key value
          | none => .obj (members.erase key)
      | other, _ => other
  | key :: rest, value, json =>
      let child? := match json, key.toNat? with
        | .arr items, some index => items[index]?
        | _, _ => (json.getObjVal? key).toOption
      match child?, json, key.toNat? with
      | some child, .arr items, some index => .arr (items.set! index (edited rest value child))
      | some child, _, _ => json.setObjVal! key (edited rest value child)
      | none, _, _ => json

/-- `base` with `value` written at `path`; `none` removes the member. -/
private def with_ (path : List String) (value : Option Json) : Json := edited path value base

/-- Indices of the base model's root-group elements. -/
private def note := 0
private def amount := 1
private def filed := 2
private def tier := 3
private def custom := 4
private def hinted := 5
private def linked := 6
private def rows := 7
private def rule := 8
private def computation := 9

private def element (index : Nat) (rest : List String) : List String :=
  ["content", "modelRoot", "rootGroups", "0", "Group", "elements", toString index] ++ rest

private def fieldTypePath (index : Nat) (rest : List String) : List String :=
  element index (["Field", "fieldType"] ++ rest)

private def definitionPath (index : Nat) (rest : List String) : List String :=
  ["content", "typeDefinitions", toString index, "fieldType"] ++ rest

private def declarations (json : Json) := fieldTypeDeclarationNotifications json fun _ => .compiled fun _ => true

/-- Whether all three readers leave no model. The model reader's admission failures are a model built
and judged, so only its input error counts. -/
private def noModel (json : Json) : Bool :=
  (match readModelWithAdmission json with | .error (.input _) => true | _ => false) &&
    !(checkModelConsistency json).isOk && !(declarations json).isOk

/-- Whether all three readers read a model, whatever classes it then draws. -/
private def reads (json : Json) : Bool :=
  (match readModelWithAdmission json with | .error (.input _) => false | _ => true) &&
    (checkModelConsistency json).isOk && (declarations json).isOk

/-- The labels of the rows that do not hold. -/
private def failures (rows : List (String × Bool)) : List String :=
  rows.filterMap fun (label, holds) => if holds then none else some label

/-- The control of every cluster: the base model is read by all three readers. -/
example : reads base = true := by native_decide

/-! ## Primitive `boolean` members

Locked: a12-dmkits BooleanMemberBindingDiffTest, CheckerDeclarationAdmissionAgreementTest and
ShortNameFlagSpellingLawsTest at 1124b523f, kernel 31.1.1. The blank text, the text `null` and JSON `null`
reach Jackson 3's refusal of a null for a primitive and leave no model; 30.8.1 read each as `false`. -/

private def booleanCarriers : List (String × List String) := [
  ("modelInfo.immutable", ["content", "modelInfo", "immutable"]),
  ("modelInfo.metaData", ["content", "modelInfo", "metaData"]),
  ("modelConfig.fieldRefByShortNameAllowed", ["content", "modelConfig", "fieldRefByShortNameAllowed"]),
  ("Field.global", element note ["Field", "global"]),
  ("Field.transient", element note ["Field", "transient"]),
  ("StringType.lineBreaksPermitted", fieldTypePath note ["StringType", "lineBreaksPermitted"]),
  ("StringType.noValueValidation", fieldTypePath note ["StringType", "noValueValidation"]),
  ("StringType.alphabeticalSorting", fieldTypePath note ["StringType", "alphabeticalSorting"]),
  ("NumberType.zeroNotAllowed", fieldTypePath amount ["NumberType", "zeroNotAllowed"]),
  ("NumberType.positivesOnly", fieldTypePath amount ["NumberType", "positivesOnly"]),
  ("NumberType.leadingZerosAllowed", fieldTypePath amount ["NumberType", "leadingZerosAllowed"]),
  ("DateType.youngerThan1900Check", fieldTypePath filed ["DateType", "youngerThan1900Check"]),
  ("EnumerationType.alphabeticalSorting", fieldTypePath tier ["EnumerationType", "alphabeticalSorting"]),
  ("referenced definition positivesOnly", definitionPath 1 ["NumberType", "positivesOnly"]),
  ("unreferenced definition positivesOnly", definitionPath 0 ["NumberType", "positivesOnly"])]

/-- Spellings no carrier binds. The peers measure them on a sample: most on `fieldRefByShortNameAllowed`
(`ShortNameFlagSpellingLawsTest`) and the blank, `null` and empty texts on every carrier; applying the whole
list to every carrier, and the tab-only text anywhere, is the one law's derivation, unmeasured. -/
private def unbindableBooleans : List String :=
  ["null", "\"\"", "\" \"", "\"\\t\"", "\"null\"", "\" null\"", "\"yes\"", "\"1\"", "\"NULL\"", "\"FaLsE\"",
    "\"\\u00A0true\"", "\"\\u2003true\"", "0.5", "1.5", "{}", "[]"]

private def boundBooleans : List String :=
  ["true", "false", "\"true\"", "\"True\"", "\"TRUE\"", "\"false\"", "\"False\"", "\"FALSE\"", "\" true\"",
    "\" TRUE\"", "\"\\ttrue\"", "\"true\\n\"", "1", "2", "-1", "0"]

private def booleanRows : List (String × Bool) :=
  booleanCarriers.flatMap fun (label, path) =>
    (unbindableBooleans.map fun spelling =>
      (s!"{label} = {spelling}", noModel (with_ path (some (literal spelling))))) ++
    (boundBooleans.map fun spelling =>
      (s!"{label} = {spelling}", reads (with_ path (some (literal spelling))))) ++
    [(s!"{label} absent", reads (with_ path none))]

example : failures booleanRows = [] := by native_decide

/-! ## Primitive `int` and boxed `Integer` members

Locked: a12-dmkits FieldTypeIntMemberBindingDiffTest and RepeatabilityTextReadingDiffTest at 1124b523f,
kernel 31.1.1. A primitive member refuses every spelling that binds no value, as it refuses a boolean's;
a boxed one reads that spelling as the member left out. A number with a fraction and a numeric text bind
the same integer on both, on every carrier, a type definition no field names included. The refutation of
the rival reading "kernel 31 refuses null for every integer member" is the boxed rows. -/

/-- An integer member: its carrier, its path, and whether a reader output carries its bound value. -/
private structure IntMember where
  label : String
  primitive : Bool
  path : List String
  /-- Whether the readers' output shows the bound value, so that it differs from the member's absence. -/
  visible : Bool := true

private def integerMembers : List IntMember := [
  { label := "root group repeatability", primitive := true,
    path := ["content", "modelRoot", "rootGroups", "0", "Group", "repeatability"] },
  { label := "nested group repeatability", primitive := true, path := element rows ["Group", "repeatability"] },
  { label := "NumberType.minFractionalDigits", primitive := true,
    path := fieldTypePath amount ["NumberType", "minFractionalDigits"] },
  { label := "NumberType.maxFractionalDigits", primitive := true,
    path := fieldTypePath amount ["NumberType", "maxFractionalDigits"] },
  { label := "referenced definition minFractionalDigits", primitive := true,
    path := definitionPath 1 ["NumberType", "minFractionalDigits"] },
  { label := "unreferenced definition minFractionalDigits", primitive := true,
    path := definitionPath 0 ["NumberType", "minFractionalDigits"], visible := false },
  { label := "unreferenced definition maxFractionalDigits", primitive := true,
    path := definitionPath 0 ["NumberType", "maxFractionalDigits"], visible := false },
  -- `baseYear` is boxed by the peer's source reading; no lock measures this carrier on kernel 31.1.1.
  { label := "modelInfo.baseYear", primitive := false, path := ["content", "modelInfo", "baseYear"] },
  { label := "NumberType.minLength", primitive := false, path := fieldTypePath amount ["NumberType", "minLength"] },
  { label := "NumberType.maxLength", primitive := false, path := fieldTypePath amount ["NumberType", "maxLength"] },
  { label := "NumberType.maxIntegerDigits", primitive := false,
    path := fieldTypePath amount ["NumberType", "maxIntegerDigits"] },
  { label := "referenced definition maxIntegerDigits", primitive := false,
    path := definitionPath 1 ["NumberType", "maxIntegerDigits"] },
  { label := "unreferenced definition maxLength", primitive := false,
    path := definitionPath 0 ["NumberType", "maxLength"], visible := false },
  { label := "unreferenced definition minLength", primitive := false,
    path := definitionPath 0 ["NumberType", "minLength"], visible := false },
  { label := "unreferenced definition maxIntegerDigits", primitive := false,
    path := definitionPath 0 ["NumberType", "maxIntegerDigits"], visible := false },
  { label := "StringType.minLength", primitive := false, path := fieldTypePath note ["StringType", "minLength"] },
  { label := "StringType.maxLength", primitive := false, path := fieldTypePath note ["StringType", "maxLength"] },
  { label := "CustomFieldType.minLength", primitive := false,
    path := fieldTypePath custom ["CustomFieldType", "minLength"] },
  { label := "CustomFieldType.maxLength", primitive := false,
    path := fieldTypePath custom ["CustomFieldType", "maxLength"] }]

private def noValueSpellings : List String := ["null", "\"\"", "\" \"", "\"null\"", "\" null \""]

/-- Spellings no integer member binds. `"abc"` and `true` are measured on every carrier and `"NULL"` on
`repeatability` only; the containers, and `"NULL"` on the other members, are derived, unmeasured. -/
private def unbindableIntegers : List String := ["\"abc\"", "true", "{}", "[]", "\"NULL\""]

private def integerRows : List (String × Bool) :=
  integerMembers.flatMap fun member =>
    let at_ (spelling : String) := with_ member.path (some (literal spelling))
    let absent := with_ member.path none
    (noValueSpellings.map fun spelling =>
      (s!"{member.label} = {spelling}",
        if member.primitive then noModel (at_ spelling)
        else reads (at_ spelling) && modelVerdict (at_ spelling) == modelVerdict absent)) ++
    (unbindableIntegers.map fun spelling => (s!"{member.label} = {spelling}", noModel (at_ spelling))) ++
    [(s!"{member.label} = 2.7", reads (at_ "2.7") && modelVerdict (at_ "2.7") == modelVerdict (at_ "2")),
      (s!"{member.label} = \"2\"", reads (at_ "\"2\"") && modelVerdict (at_ "\"2\"") == modelVerdict (at_ "2")),
      (s!"{member.label} bound", !member.visible || modelVerdict (at_ "2") != modelVerdict absent)]

example : failures integerRows = [] := by native_decide

/-- A count below one is `MVK_MAX_VALUES_INVALID` and is read on as a single group. -/
example :
    (["0", "-1", "\"-1\"", "-3.7"].all fun spelling =>
      reads (with_ (element rows ["Group", "repeatability"]) (some (literal spelling)))) = true := by
  native_decide

/-- The bound a spelling carries is the one the readers use: written `"3"` or `3.7`, a member reads as `3`
and not as the base model's value, on each integer carrier the model reader keeps. -/
private def field? (json : Json) (name : String) : Option FlatFieldDecl :=
  (readModel json).toOption.bind (·.flat.fields.find? (·.name == name))

private def scale? : Option FlatFieldDecl → Option Nat
  | some { policy := { kind := .number info }, .. } => some info.scale
  | _ => none

example :
    ["\"3\"", "3.7"].all (fun spelling =>
      scale? (field? (with_ (fieldTypePath amount ["NumberType", "maxFractionalDigits"]) (some (literal spelling)))
        "Amount") == some 3 &&
      (field? (with_ (fieldTypePath note ["StringType", "maxLength"]) (some (literal spelling))) "Note").map
        (·.stringPolicy.maxLength) == some (some 3) &&
      (field? (with_ (fieldTypePath amount ["NumberType", "maxIntegerDigits"]) (some (literal spelling))) "Amount").map
        (·.numericTargetConstraints.maxIntegerDigits) == some (some 3) &&
      (field? (with_ (fieldTypePath custom ["CustomFieldType", "maxLength"]) (some (literal spelling))) "Code").map
        (·.customType.map (·.maxLength)) == some (some (some 3)) &&
      (field? (with_ (fieldTypePath amount ["NumberType", "minLength"]) (some (literal spelling))) "Amount").map
        (·.numericTargetConstraints.minStoredLength) == some (some 3) &&
      (readModel (with_ ["content", "modelInfo", "baseYear"] (some (literal spelling)))).toOption.map
        (·.flat.baseYear) == some (some 3)) = true := by
  native_decide

/-- A group's count binds through the one `int` law on all three readers: numeric text after `trim`, a
non-ASCII digit and a fraction read as the count `3`, and no other text, a count past `int`, a boolean or a
container leaves no model. -/
example :
    (["\"3\"", "\" 3 \"", "\"\\t3\\n\"", "\"+3\"", "\"03\"", "\"\\u0663\"", "\"\\uFF13\"", "3.7"].all fun spelling =>
      modelVerdict (with_ (element rows ["Group", "repeatability"]) (some (literal spelling))) ==
        modelVerdict base) &&
    (["\"3.7\"", "\"1e1\"", "\"0x3\"", "\"\\u00A03\"", "\"3\\u00A0\"", "\"99999999999\"", "2147483648",
      "true", "{}", "[]"].all fun spelling =>
      noModel (with_ (element rows ["Group", "repeatability"]) (some (literal spelling)))) = true := by
  native_decide

/-! ## Element bodies

Locked: a12-dmkits ElementBodyReadingDiffTest at 1124b523f, kernel 31.1.1, on its three entry carriers (the
entry's root group, a nested group, a field), and WorkspaceIncludeStructureKernelTest on the rule and the
computation, whose missing and `null` bodies it measures. A missing or `null` Group
body is an empty group, built and checked like `{}`; a Field, a Rule and a Computation have no empty
reading, so theirs is no model; and no other non-object body binds on any carrier. 30.8.1 refused a
group body written so. A scalar Rule or Computation body is unmeasured on 31.1.1 and refused like a
Field's. -/

private def bodySpellings : List (String × Option Json) :=
  [("missing", none), ("null", some .null), ("true", some (literal "true")), ("7", some (literal "7")),
    ("\"x\"", some (literal "\"x\"")), ("[]", some (literal "[]"))]

/-- A carrier: the element holding the body and the member the body is under. -/
private def bodyCarriers : List (String × List String × Bool) := [
  ("root group", ["content", "modelRoot", "rootGroups", "0", "Group"], true),
  ("nested group", element rows ["Group"], true),
  ("field", element note ["Field"], false),
  ("rule", element rule ["Rule"], false),
  ("computation", element computation ["Computation"], false)]

private def bodyRows : List (String × Bool) :=
  bodyCarriers.flatMap fun (label, path, isGroup) =>
    let control := with_ path (some (literal "{}"))
    bodySpellings.map fun (spelling, body) =>
      let written := with_ path body
      (s!"{label} body {spelling}",
        if isGroup && (body.isNone || body == some .null) then
          reads control && modelVerdict written == modelVerdict control
        else noModel written)

example : failures bodyRows = [] := by native_decide

/-- A group's `elements` is a list: absent holds no children, and `null`, a Boolean, a number, a text or an
object leaves no model. WorkspaceIncludeStructureKernelTest measures this on a provider root's group; the
entry's own groups are assumed to bind the same member alike, which no row states. -/
example :
    (["null", "true", "7", "\"x\"", "{}"].all fun spelling =>
      noModel (with_ ["content", "modelRoot", "rootGroups", "0", "Group", "elements"] (some (literal spelling))) &&
      noModel (with_ (element rows ["Group", "elements"]) (some (literal spelling)))) &&
    reads (with_ (element rows ["Group", "elements"]) none) &&
    reads (with_ (element rows ["Group", "elements"]) (some (literal "[]"))) = true := by
  native_decide

/-- The empty-group control is not vacuous: an empty group differs from the group it replaces. -/
example :
    modelVerdict (with_ (element rows ["Group"]) (some (literal "{}"))) != modelVerdict base := by
  native_decide

/-! ## Field types

Locked: a12-dmkits FieldTypeBindingLawsTest and CheckerReaderBindingAgreementTest at 1124b523f, kernel
31.1.1. A field type written without its body draws what the same type with an empty body draws, on each of
the twelve types the Kernel reads, where 30.8.1 refused eight of thirteen, among them the three temporal
kinds read here. `UnspecifiedType` is no type the Kernel reads, with a body or without one, on a root and
on a nested field. -/

private def declaredTypes : List String :=
  ["StringType", "NumberType", "DateType", "DateTimeType", "DateRangeType", "DateFragmentType",
    "EnumerationType", "TimeType", "TypeDefType", "CustomFieldType", "ConfirmType", "BooleanType"]

private def typed (index : Nat) (typeName : String) (body : Option Json) : Json :=
  with_ (element index ["Field", "fieldType"])
    (some (Json.mkObj ([("type", .str typeName)] ++ body.toList.map (typeName, ·))))

private def typeRows : List (String × Bool) :=
  declaredTypes.map (fun typeName =>
    (s!"{typeName} without a body",
      modelVerdict (typed note typeName none) == modelVerdict (typed note typeName (some (literal "{}"))))) ++
  ["StringType", "NumberType", "DateType", "DateTimeType", "TimeType", "ConfirmType", "BooleanType"].map
    (fun typeName => (s!"{typeName} without a body is read", reads (typed note typeName none))) ++
  [("UnspecifiedType without a body", noModel (typed note "UnspecifiedType" none)),
    ("UnspecifiedType with a body", noModel (typed note "UnspecifiedType" (some (literal "{}")))),
    ("UnspecifiedType nested", noModel (with_ (element rows ["Group", "elements", "0", "Field", "fieldType"])
      (some (literal "{\"type\":\"UnspecifiedType\"}"))))]

example : failures typeRows = [] := by native_decide

/- The envelope: a field whose `fieldType` is not an object naming one of the twelve types by its exact
   discriminator leaves no model, while the plain String control reads. -/
example :
    reads (with_ (element note ["Field", "fieldType"]) (some (literal "{\"type\":\"StringType\"}"))) = true ∧
    [none, some "{}", some "{\"StringType\":{}}", some "{\"type\":\"NotAType\",\"NotAType\":{}}",
        some "{\"type\":\"stringtype\"}", some "\"StringType\"", some "7",
        some "[{\"type\":\"StringType\"}]", some "null"].all
      (fun spelling => noModel (with_ (element note ["Field", "fieldType"]) (spelling.map literal))) = true := by
  native_decide

/-! ## Required members

Locked: a12-dmkits RuleCodeAndSeverityLawsTest, RuleConditionAndTargetSlotLawsTest, ModelHeaderSlotLawsTest,
WorkspaceBlankTextDiffTest and CheckerReaderBindingAgreementTest at 1124b523f, kernel 31.1.1. A rule's
`errorCode`, `errorEntityRelPath` and `errorCondition`, a computation's `computedFieldRelPath`, a sort
field's `name` and the header's `id` leave no model when absent or `null`; 30.8.1 admitted an absent header
`id` and drew `MVK_ERROR_CODE_MISSING` for an absent code. Each present empty or blank spelling is a member
the model builds with, and a number is the code's text. A severity is absent or exactly one of three
names. -/

private def required : List (String × List String) := [
  ("rule errorCode", element rule ["Rule", "errorCode"]),
  ("rule errorEntityRelPath", element rule ["Rule", "errorEntityRelPath"]),
  ("rule errorCondition", element rule ["Rule", "errorCondition"]),
  ("computation computedFieldRelPath", element computation ["Computation", "computedFieldRelPath"]),
  ("sort field name", element rows ["Group", "sortFields", "0", "name"]),
  ("header id", ["header", "id"])]

private def requiredRows : List (String × Bool) :=
  required.flatMap fun (label, path) =>
    [(s!"{label} absent", noModel (with_ path none)), (s!"{label} null", noModel (with_ path (some .null))),
      (s!"{label} empty", reads (with_ path (some (literal "\"\""))))]

example : failures requiredRows = [] := by native_decide

/-- The header's `id` is admitted as an empty text, a number and a Boolean. -/
example :
    (["\"\"", "\"  \"", "5", "true"].all fun spelling => reads (with_ ["header", "id"] (some (literal spelling)))) =
      true := by
  native_decide

/-- A rule's code is read as its text where a scalar, and an empty or blank one is judged, not unread. -/
example :
    (["7", "true", "\"\"", "\"   \""].all fun spelling =>
      match readModelWithAdmission (with_ (element rule ["Rule", "errorCode"]) (some (literal spelling))) with
      | .error (.input _) => false
      | _ => true) = true := by
  native_decide

private def severityRows : List (String × Bool) :=
  let at_ (spelling : Option String) := with_ (element rule ["Rule", "severity"]) (spelling.map literal)
  [("absent", reads (at_ none)), ("ERROR", reads (at_ (some "\"ERROR\""))),
    ("WARNING", reads (at_ (some "\"WARNING\""))), ("INFO", reads (at_ (some "\"INFO\"")))] ++
  ["null", "\"\"", "\"   \"", "\"error\"", "\"Error\"", "\"FATAL\"", "7", "{\"code\":\"ERROR\"}"].map
    fun spelling => (s!"severity {spelling}", noModel (at_ (some spelling)))

example : failures severityRows = [] := by native_decide

/-! ## Empty versus absent

Locked: a12-dmkits CheckerEmptyMemberAgreementTest at 1124b523f, kernel 31.1.1. The header's `modelVersion`
and `locales` are no model when absent, where 30.8.1 built the model and failed its check; their empty
spellings keep their classes. A hint entry's `locale` and `values` are no model when absent and admitted
empty. The rows for `indexFieldName`, `includeConfig` and `precondition` are other steps'. -/

private def hintEntry (member : String) : List String :=
  fieldTypePath hinted ["StringType", "hintList", "0", member]

private def emptyRows : List (String × Bool) := [
  ("modelVersion absent", noModel (with_ ["header", "modelVersion"] none)),
  ("locales absent", noModel (with_ ["header", "locales"] none)),
  ("modelVersion empty", reads (with_ ["header", "modelVersion"] (some (literal "\"\"")))),
  ("locales empty", reads (with_ ["header", "locales"] (some (literal "[]")))),
  ("hint locale absent", noModel (with_ (hintEntry "locale") none)),
  ("hint values absent", noModel (with_ (hintEntry "values") none)),
  ("hint locale empty", reads (with_ (hintEntry "locale") (some (literal "\"\"")))),
  ("hint values empty", reads (with_ (hintEntry "values") (some (literal "[]"))))]

example : failures emptyRows = [] := by native_decide

/-! ## Members read past

Locked: a12-dmkits FieldTypeBindingLawsTest, EnumCategoryWireShapeLawsTest, EnumDeclarationShapeLawsTest,
TemporalConfigWireShapeLawsTest and CheckerReaderBindingAgreementTest at 1124b523f, kernel 31.1.1. A member
no field, rule, group or type body declares is read past, so the model is the one without it, where 30.8.1
refused it on a field, a rule and a type body. An Enumeration's misspelled `values` is the Enumeration
without values, and a misspelled `categories` the one without categories. -/

private def readPast : List (String × Json) := [
  ("a field", with_ (element note ["Field", "colourScheme"]) (some (literal "\"red\""))),
  ("a rule", with_ (element rule ["Rule", "colourScheme"]) (some (literal "\"red\""))),
  ("a type body", with_ (fieldTypePath note ["StringType", "colourScheme"]) (some (literal "\"red\""))),
  ("a date body", with_ (fieldTypePath filed ["DateType", "formatt"]) (some (literal "\"yyyy\""))),
  ("a fieldType on a rule", with_ (element rule ["Rule", "fieldType"])
    (some (literal "{\"type\":\"NotAType\",\"NotAType\":{}}"))),
  ("a group", with_ (element rows ["Group", "colourScheme"]) (some (literal "1"))),
  ("a tableName beside values", with_ (fieldTypePath tier ["EnumerationType", "tableName"])
    (some (literal "\"Tiers\"")))]

example : readPast.all (fun (_, json) => reads json && modelVerdict json == modelVerdict base) = true := by
  native_decide

private def enumeration (members : String) : Json :=
  with_ (fieldTypePath tier ["EnumerationType"]) (some (literal members))

/-- The misspelled members are the members left out: `categories` misspelled admits the enumeration as
without categories, and `values` misspelled is the enumeration with no values, which the declaration reader
reports as the unbuilt model. -/
example :
    (modelVerdict (enumeration "{\"values\":[{\"value\":\"GOLD\"}],\"categoriez\":[{\"name\":\"B\",\"values\":[\"X\"]}]}") ==
      modelVerdict (enumeration "{\"values\":[{\"value\":\"GOLD\"}]}") &&
    modelVerdict (enumeration "{\"valuez\":[{\"value\":\"GOLD\"}],\"categories\":[{\"name\":\"B\",\"values\":[\"X\"]}]}") ==
      modelVerdict (enumeration "{\"categories\":[{\"name\":\"B\",\"values\":[\"X\"]}]}") &&
    (declarations (enumeration "{\"valuez\":[{\"value\":\"GOLD\"}]}")).toOption ==
      some [(modelNotBuiltLabel, "")]) = true := by
  native_decide

/-- A rule listing a token the enumeration does not declare. -/
private def undeclaredToken : Json :=
  with_ (element rule ["Rule"]) (some (literal
    "{\"errorEntityRelPath\":\"../Tier\",\"errorCode\":\"R1\",\"errorCondition\":\"FieldValueIncludedInValueList(Tier, \\\"GOLD\\\", \\\"PENDING\\\")\",\"severity\":\"ERROR\"}"))

/-- A table name beside the values is a member no enumeration declares, so the undeclared token is judged
as without it, and draws the class the token's twin draws. -/
example :
    (modelVerdict (edited (fieldTypePath tier ["EnumerationType", "tableName"]) (some (literal "\"Tiers\"")) undeclaredToken) ==
      modelVerdict undeclaredToken &&
    (modelVerdict undeclaredToken).statics.head? ==
      some "refused ParallelAdmission MVK_INVALID_STRING_CONSTANT_FOR_ENUMERATION") = true := by
  native_decide

end A12Kernel.Dm.ReaderBindingLocks
