import Lean.Data.Json
import A12Kernel.Elaboration.ModelConsistency
import A12Kernel.Reference.Dm.ModelConsistencyRead

/-! # Reader integration for the model consistency check

Each row mirrors one model of the retained real-Kernel captures of the model consistency check
(`evidence/kernel-30.8.1/captures/model-consistency-2026-10-13/` and
`evidence/kernel-30.8.1/captures/model-consistency-bound-order-2026-10-13/`): a base model with one root
group `Form`, to whose elements a row appends its own, and which it may give type definitions or another
condition language. The assertion is the retained observation: the ordered notification labels the check
reports, or the one unbuilt-model label. A capture also records codes other owners carry
(`MVK_*`, rule and Enumeration declarations); only the labels of `ModelConsistencyClass` are compared, and
the unbuilt-model label. Row `b-localized-null` is not replayed: the capture recorded an instrument
fault (`admitted: null`), not an observation of the Kernel. Peer KF646 has since measured that shape,
which the [text-binding locks](LocalizedTextBindingLocks.lean) fix for this reader too.

Two parts replay other measurements: `liftedBuildFailureRows`, a peer measurement of the build failures
a variant filter lifts, and the type-definition section at the end, peer and local rows of 2026-10-29.

The captures record labels, not payloads, so the paths the check attaches are checked only by the
examples at the end. Those pin this module's choice and no observation, except in the type-definition
section, whose oracles compare which definition each notification names.
-/

namespace A12Kernel.Dm.ModelConsistencyLocks

open Lean A12Kernel

/-- The capture's base model (`Wh_DM.json`), compacted. -/
private def baseModel : Json := (Json.parse r#"
{"header":{"id":"Wh_DM","modelType":"document","modelVersion":"28.4.0","locales":[{"code":"en_US"}],"labels":[],"annotations":[],"modelReferences":[]},"content":{"modelInfo":{"name":"Wh_DM","variant":"cockpit","revision":"Arbeitsversion","immutable":false},"modelConfig":{"decimalSeparator":".","timeZone":"Europe/Berlin","conditionLanguage":{"code":"en_US"},"fieldRefByShortNameAllowed":true},"modelRoot":{"rootGroups":[
{"type":"Group","id":"/Form","name":"Form","Group":{"repeatability":1,"elements":[
{"type":"Field","id":"/Form/Value","name":"Value","Field":{"fieldType":{"type":"StringType"}}},
{"type":"Field","id":"/Form/Other","name":"Other","Field":{"fieldType":{"type":"StringType"}}},
{"type":"Field","id":"/Form/Total","name":"Total","Field":{"fieldType":{"type":"NumberType","NumberType":{"maxFractionalDigits":0}}}},
{"type":"Group","id":"/Form/Items","name":"Items","Group":{"repeatability":4,"elements":[
{"type":"Field","id":"/Form/Items/K","name":"K","Field":{"fieldType":{"type":"StringType"}}},
{"type":"Field","id":"/Form/Items/V","name":"V","Field":{"fieldType":{"type":"StringType"}}},
{"type":"Field","id":"/Form/Items/NVV","name":"NVV","Field":{"fieldType":{"type":"StringType","StringType":{"lineBreaksPermitted":true,"noValueValidation":true}}}},
{"type":"Field","id":"/Form/Items/NVV2","name":"NVV2","Field":{"fieldType":{"type":"StringType","StringType":{"lineBreaksPermitted":true,"noValueValidation":true}}}}]}}]}}]}}}
"#).toOption.getD .null

/-! ## Building a row's model -/

/-- An authored decimal, kept as written so its exact digits reach the reader. -/
private def decimal (written : String) : Json := (Json.parse written).toOption.getD .null

private def typeOf (name : String) (body : Option (List (String × Json)) := none) : Json :=
  Json.mkObj ([("type", .str name)] ++ (body.map fun members => [(name, Json.mkObj members)]).getD [])

/-- A String type; a body appears only when a flag is authored. -/
private def stringType (flags : List (String × Bool) := []) : Json :=
  typeOf "StringType" (if flags.isEmpty then none else
    some (flags.map fun (key, value) => (key, Json.bool value)))

private def bothFlags : List (String × Bool) := [("noValueValidation", true), ("lineBreaksPermitted", true)]

/-- A Number type whose body holds exactly the authored members; `numberType` alone is an empty body. -/
private def numberType (maxFractional minFractional minValue maxValue : Option String := none) : Json :=
  typeOf "NumberType" (some ([("maxFractionalDigits", maxFractional), ("minFractionalDigits", minFractional),
    ("minValue", minValue), ("maxValue", maxValue)].filterMap fun (key, written) =>
      written.map fun text => (key, decimal text)))

private def enumerationType (values : List String) (categories : List (String × List String) := []) : Json :=
  typeOf "EnumerationType" (some ([("values", Json.arr (values.map fun value =>
      Json.mkObj [("value", .str value)]).toArray)] ++
    if categories.isEmpty then [] else
      [("categories", Json.arr (categories.map fun (name, names) =>
        Json.mkObj [("name", .str name), ("values", toJson names)]).toArray)]))

private def typedefType (id : String) : Json :=
  typeOf "TypeDefType" (some [("typeDefinitionId", .str id)])

/-- A type-definition reference whose body authors no `typeDefinitionId`. -/
private def typedefTypeWithoutId : Json := typeOf "TypeDefType" (some [])

private def required : String × Json :=
  ("requirednessConfig", Json.mkObj [("mode", "relativeToParent")])

private def onlyV1 : String × Json :=
  ("variantFilter", Json.mkObj [("filterType", "ONLY"), ("variants", toJson ["V1"])])

private def element (kind id name : String) (body : List (String × Json)) : Json :=
  Json.mkObj [("type", .str kind), ("id", .str id), ("name", .str name), (kind, Json.mkObj body)]

private def fieldEl (id name : String) (fieldType : Json) (extra : List (String × Json) := []) : Json :=
  element "Field" id name (("fieldType", fieldType) :: extra)

private def ruleEl (id name errorEntityRelPath errorCondition : String)
    (extra : List (String × Json) := []) : Json :=
  element "Rule" id name (([("errorEntityRelPath", .str errorEntityRelPath), ("errorCode", "C"),
    ("errorCondition", .str errorCondition), ("severity", "ERROR"),
    ("errorMessage", Json.arr #[Json.mkObj [("locale", "en_US"), ("text", "m")]])] :
      List (String × Json)) ++ extra)

private def computationEl (id name computedFieldRelPath : String) (operations : List String)
    (extra : List (String × Json) := []) : Json :=
  element "Computation" id name ([("computedFieldRelPath", .str computedFieldRelPath),
    ("computationAlternatives", Json.arr (operations.map fun operation =>
      Json.mkObj [("operation", .str operation)]).toArray),
    ("errorMessage", Json.arr #[Json.mkObj [("locale", "en_US"), ("text", "m")]])] ++ extra)

private def groupEl (id name : String) (repeatability : Nat) (children : List Json)
    (usageType indexFieldName : Option String := none) (sortFieldNames : Option (List String) := none) :
    Json :=
  element "Group" id name ([("repeatability", toJson repeatability),
    ("elements", Json.arr children.toArray)] ++
    (usageType.map fun value => [("usageType", Json.str value)]).getD [] ++
    (indexFieldName.map fun value => [("indexFieldName", Json.str value)]).getD [] ++
    (sortFieldNames.map fun names => [("sortFields", Json.arr (names.map fun sortName =>
      Json.mkObj [("name", .str sortName)]).toArray)]).getD [])

private def typedefEl (id name : String) (fieldType : Json) : Json :=
  Json.mkObj [("id", .str id), ("name", .str name), ("fieldType", fieldType)]

/-- The four conditions an attachment group carries under each condition language, as the captures
author them (`a-ok`, `a-de-ok`). -/
private def english : List String := [
  "GroupFilled(RuleGroup) and NotExactlyOneFieldFilled(attachment_id, content)",
  "FieldFilled(content) and FieldNotFilled(size)",
  "GroupFilled(RuleGroup) and FieldNotFilled(internal_filename)",
  "GroupFilled(RuleGroup) and FieldNotFilled(mime_type)"]

private def german : List String := [
  "KontextAngegeben(RegelKontext) und NichtGenauEinFeldAngegeben(attachment_id, content)",
  "FeldAngegeben(content) und FeldNichtAngegeben(size)",
  "KontextAngegeben(RegelKontext) und FeldNichtAngegeben(internal_filename)",
  "KontextAngegeben(RegelKontext) und FeldNichtAngegeben(mime_type)"]

private def attachmentEntities : List String :=
  ["../attachment_id", "../size", "../internal_filename", "../mime_type"]

/-- The capture's attachment group `Att`: the eight fields in the order `a-ok` authors them, minus
`without`, the named ones carrying a variant filter, then one rule per condition, then any extras. -/
private def attachmentGroup (without : List String := [])
    (content : Json := stringType bothFlags) (filtered : List String := [])
    (conditions : List String := english) (extraElements : List Json := []) : Json :=
  let fields : List (String × Json) := [("original_filename", stringType), ("internal_filename", stringType),
    ("content", content), ("attachment_id", stringType), ("size", numberType (maxFractional := "0")),
    ("mime_type", stringType), ("category", stringType), ("description", stringType)]
  let rules := (conditions.zip attachmentEntities).mapIdx fun index (condition, entity) =>
    ruleEl s!"/Form/Att/AttRule{index}" s!"AttRule{index}" entity condition
  groupEl "/Form/Att" "Att" 3
    ((fields.filter (fun (name, _) => !without.contains name)).map (fun (name, fieldType) =>
      fieldEl s!"/Form/Att/{name}" name fieldType (if filtered.contains name then [onlyV1] else [])) ++
      rules ++ extraElements)
    (usageType := "attachment")

/-- One retained model: what it appends to `Form`, the type definitions that replace the base model's,
its condition language, and the labels the capture observed in order. -/
private structure Row where
  append : List Json := []
  typeDefinitions : Option (List Json) := none
  language : Option String := none
  observed : List String

private def withMember (json : Json) (key : String) (change : Json → Json) : Json :=
  json.setObjVal! key (change (json.getObjValD key))

private def modelOf (row : Row) : Json :=
  withMember baseModel "content" fun content =>
    let content := withMember content "modelRoot" fun root =>
      withMember root "rootGroups" fun
        | .arr groups => .arr (groups.modify 0 fun form =>
            withMember form "Group" fun body => withMember body "elements" fun
              | .arr elements => .arr (elements ++ row.append.toArray)
              | other => other)
        | other => other
    let content := match row.typeDefinitions with
      | some definitions => content.setObjVal! "typeDefinitions" (Json.arr definitions.toArray)
      | none => content
    match row.language with
    | some code => withMember content "modelConfig" fun config =>
        config.setObjVal! "conditionLanguage" (Json.mkObj [("code", .str code)])
    | none => content

/-! ## Comparing with the observation -/

private def notBuilt : String := "codeless:model-not-built"

/-- The labels of the check's classes, as the captures spell them. -/
private def idNotUnique : String := "codeless:id-not-unique"
private def maxExceeded : String := "codeless:number-max-value-exceeded"
private def minExceeded : String := "codeless:number-min-value-exceeded"
private def missingField : String := "codeless:attachment-missing-field"
private def requiredRules : String := "codeless:attachment-required-rules"
private def contentConfig : String := "codeless:attachment-content-config"
private def repeatableGroup : String := "codeless:multi-select-repeatable-group"
private def requiredField : String := "codeless:multi-select-required-field"
private def requiredFlag : String := "codeless:multi-select-required-flag"
private def indexField : String := "codeless:multi-select-index-field"
private def wrongFieldType : String := "codeless:multi-select-fieldtype"
private def otherElements : String := "codeless:multi-select-other-elements"
private def tooLong : String := "codeless:metamodel-formal:STELLIGKEIT_ZU_LANG"
private def signedZero : String := "codeless:metamodel-formal:ZAHL_NULL_ENTHAELT_VORZEICHEN"
private def idEmpty : String := "codeless:id-empty"
private def conditionEmpty : String := "codeless:error-condition-empty"
private def entityNotSet : String := "codeless:error-entity-not-set"
private def operationEmpty : String := "codeless:computation-operation-empty"
private def typedefNameEmpty : String := "codeless:typedef-name-empty"
private def elementNameEmpty : String := "codeless:element-name-empty"
private def typedefRefEmpty : String := "codeless:typedef-reference-empty"
private def computedFieldEmpty : String := "codeless:computed-field-empty"
private def enumCategoryDuplicate : String := "codeless:enum-category-duplicate"

/-- The capture's labels this check owns: codes other owners carry are dropped. -/
private def projected (observed : List String) : List String :=
  observed.filter fun label =>
    label == notBuilt || ModelConsistencyClass.all.any (·.observedLabel == label)

private def agrees (row : Row) : Bool :=
  match checkModelConsistency (modelOf row) with
  | .ok outcome => outcome.observedLabels == projected row.observed
  | .error _ => false

private def disagreeing (rows : List (String × Row)) : List String :=
  (rows.filter fun (_, row) => !agrees row).map (·.1)

/-- Every class has a capture label, so a class added without one cannot escape the projection. -/
example (kind : ModelConsistencyClass) : kind ∈ ModelConsistencyClass.all := by
  cases kind <;> simp [ModelConsistencyClass.all]

/-- A bound past the limit its declared fraction digits allow raises a value-limit class, and one that
also prints past the stored digit limit raises a formal class after it. A field the variant filter
removes still draws the limit class but never the formal one, and a type definition's bounds are judged
through the field that uses it, not on their own. -/
private def numberLimitRows : List (String × Row) := [
  ("v0-ok", { append := [fieldEl "/Form/N" "N" (numberType (maxFractional := "0") (maxValue := "999999999999999"))], observed := [] }),
  ("v0-max", { append := [fieldEl "/Form/N" "N" (numberType (maxFractional := "0") (maxValue := "1000000000000000"))], observed := [maxExceeded, tooLong] }),
  ("v0-min-neg", { append := [fieldEl "/Form/N" "N" (numberType (maxFractional := "0") (minValue := "-1000000000000000"))], observed := [minExceeded, tooLong] }),
  ("v0-min-pos", { append := [fieldEl "/Form/N" "N" (numberType (maxFractional := "0") (minValue := "1000000000000000"))], observed := [minExceeded, tooLong] }),
  ("v0-both", { append := [fieldEl "/Form/N" "N" (numberType (maxFractional := "0") (minValue := "-1000000000000000") (maxValue := "1000000000000000"))], observed := [maxExceeded, minExceeded, tooLong] }),
  ("v2-ok", { append := [fieldEl "/Form/N" "N" (numberType (maxFractional := "2") (maxValue := "9999999999999.99"))], observed := [] }),
  ("v2-over", { append := [fieldEl "/Form/N" "N" (numberType (maxFractional := "2") (maxValue := "10000000000000"))], observed := [maxExceeded] }),
  ("v2-fine", { append := [fieldEl "/Form/N" "N" (numberType (maxFractional := "2") (maxValue := "9999999999999.991"))], observed := [] }),
  ("v2-fine-over", { append := [fieldEl "/Form/N" "N" (numberType (maxFractional := "2") (maxValue := "9999999999999.995"))], observed := [maxExceeded, tooLong] }),
  ("v14-ok", { append := [fieldEl "/Form/N" "N" (numberType (maxFractional := "14") (maxValue := "9.99999999999999"))], observed := [] }),
  ("v14-fine-over", { append := [fieldEl "/Form/N" "N" (numberType (maxFractional := "14") (maxValue := "9.999999999999991"))], observed := [maxExceeded, tooLong] }),
  ("v14-over", { append := [fieldEl "/Form/N" "N" (numberType (maxFractional := "14") (maxValue := "10"))], observed := [maxExceeded] }),
  ("v-filtered", { append := [fieldEl "/Form/N" "N" (numberType (maxFractional := "0") (maxValue := "1000000000000000")) [onlyV1]], observed := [maxExceeded] }),
  ("v-typedef", { append := [fieldEl "/Form/N" "N" (typedefType "BigTd")], typeDefinitions := [typedefEl "BigTd" "BigTd" (numberType (maxFractional := "0") (maxValue := "1000000000000000"))], observed := [maxExceeded, tooLong] }),
  ("v-typedef-unused", { typeDefinitions := [typedefEl "BigTd" "BigTd" (numberType (maxFractional := "0") (maxValue := "1000000000000000"))], observed := [] }),
  ("v-neg-fine", { append := [fieldEl "/Form/N" "N" (numberType (maxFractional := "2") (minValue := "-9999999999999.991"))], observed := [] })]

example : disagreeing numberLimitRows = [] := by native_decide

/-- The formal class follows the printed bound, not the authored one: a bound that prints within the
stored digit limit is clean however many digits were authored, and only a declaration fixing its
fraction digits prints a negative zero. -/
private def printedBoundRows : List (String × Row) := [
  ("bp-short-min", { append := [fieldEl "/Form/N" "N" (numberType (maxFractional := "2") (minValue := "1.00000000000000001"))], observed := [] }),
  ("bp-16sig", { append := [fieldEl "/Form/N" "N" (numberType (maxFractional := "14") (maxValue := "1.000000000000001"))], observed := [tooLong] }),
  ("bp-var-wide", { append := [fieldEl "/Form/N" "N" (numberType (maxFractional := "2") (maxValue := "5.555"))], observed := [] }),
  ("bp-fixed-round", { append := [fieldEl "/Form/N" "N" (numberType (maxFractional := "2") (minFractional := "2") (maxValue := "5.555"))], observed := [] }),
  ("bp-fixed-half", { append := [fieldEl "/Form/N" "N" (numberType (maxFractional := "2") (minFractional := "2") (maxValue := "0.125"))], observed := [] }),
  ("bp-fixed-int", { append := [fieldEl "/Form/N" "N" (numberType (maxFractional := "0") (minFractional := "0") (maxValue := "12.5"))], observed := [] }),
  ("bp-negzero-fixed", { append := [fieldEl "/Form/N" "N" (numberType (maxFractional := "2") (minFractional := "2") (minValue := "-0.0001"))], observed := [signedZero] }),
  ("bp-negzero-var", { append := [fieldEl "/Form/N" "N" (numberType (maxFractional := "2") (minValue := "-0.0001"))], observed := [] }),
  ("bp-frac14", { append := [fieldEl "/Form/N" "N" (numberType (maxFractional := "14") (maxValue := "0.00000000000001"))], observed := [] }),
  ("bp-frac15", { append := [fieldEl "/Form/N" "N" (numberType (maxFractional := "14") (maxValue := "0.000000000000001"))], observed := [tooLong] }),
  ("bp-tiny", { append := [fieldEl "/Form/N" "N" (numberType (maxFractional := "14") (maxValue := "0.0000000000000000001"))], observed := [tooLong] }),
  ("bp-filtered", { append := [fieldEl "/Form/N" "N" (numberType (maxFractional := "14") (maxValue := "1.000000000000001")) [onlyV1]], observed := [] })]

example : disagreeing printedBoundRows = [] := by native_decide

/-- Fraction-digit declarations draw codes this check does not own and no class of its own; a negative
declared maximum still reaches the limit check unchanged. -/
private def declaredDigitsRows : List (String × Row) := [
  ("s-min-1", { append := [fieldEl "/Form/N" "N" (numberType (maxFractional := "2") (minFractional := "-1"))], observed := [] }),
  ("s-max-1", { append := [fieldEl "/Form/N" "N" (numberType (maxFractional := "-1"))], observed := [] }),
  ("s-both-1", { append := [fieldEl "/Form/N" "N" (numberType (maxFractional := "-1") (minFractional := "-1"))], observed := ["MVK_FRACT_DIGITS_MISSING"] }),
  ("s-max-1-bound", { append := [fieldEl "/Form/N" "N" (numberType (maxFractional := "-1") (maxValue := "1000"))], observed := [] }),
  ("s-min-1-fixed2", { append := [fieldEl "/Form/N" "N" (numberType (maxFractional := "2") (minFractional := "-1") (maxValue := "5.555"))], observed := [] }),
  ("s-max-absent", { append := [fieldEl "/Form/N" "N" (numberType)], observed := [] }),
  ("s-max-absent-min2", { append := [fieldEl "/Form/N" "N" (numberType (minFractional := "2"))], observed := ["MVK_FRACT_DIGITS_INVALID"] })]

example : disagreeing declaredDigitsRows = [] := by native_decide

/-- The maximum's formal class precedes the minimum's within a field, whichever bound is long and
whichever a negative zero; a class both bounds of one field raise is reported once, but once per field
across fields. -/
private def boundOrderRows : List (String × Row) := [
  ("d1-min-negzero-max-long", { append := [fieldEl "/Form/N" "N" (numberType (maxFractional := "14") (minFractional := "14") (minValue := "-0.000000000000001") (maxValue := "10.00000000000001"))], observed := [maxExceeded, tooLong, signedZero] }),
  ("d2-two-fields-long", { append := [fieldEl "/Form/N" "N" (numberType (maxFractional := "14") (maxValue := "1.000000000000001")), fieldEl "/Form/M" "M" (numberType (maxFractional := "14") (maxValue := "2.000000000000001"))], observed := [tooLong, tooLong] }),
  ("d3a-min-fifteen-max-negzero", { append := [fieldEl "/Form/N" "N" (numberType (maxFractional := "2") (minFractional := "2") (minValue := "1000000000000.001") (maxValue := "-0.0001"))], observed := [signedZero] }),
  ("d3-min-long-max-negzero", { append := [fieldEl "/Form/N" "N" (numberType (maxFractional := "2") (minFractional := "2") (minValue := "-10000000000000.12") (maxValue := "-0.0001"))], observed := [minExceeded, signedZero, tooLong] }),
  ("d4-min-long-max-long-distinct", { append := [fieldEl "/Form/N" "N" (numberType (maxFractional := "2") (minValue := "-10000000000000.12") (maxValue := "10000000000000.13"))], observed := [maxExceeded, minExceeded, tooLong] })]

example : disagreeing boundOrderRows = [] := by native_decide

/-- Each occurrence of a shared identifier is reported, the empty identifier included; a filtered field,
a rule, a group and a computation share the namespace, the root group's identifier too. -/
private def identifierRows : List (String × Row) := [
  ("i-empty-id2", { append := [fieldEl "" "A1" (stringType), fieldEl "" "A2" (stringType)], observed := [idNotUnique, idNotUnique, idEmpty, idEmpty] }),
  ("i-empty-id1", { append := [fieldEl "" "A1" (stringType)], observed := [idEmpty] }),
  ("i-root-id", { append := [fieldEl "/Form" "A1" (stringType)], observed := [idNotUnique, idNotUnique] }),
  ("i-dup2", { append := [fieldEl "/Form/Value" "N" (stringType)], observed := [idNotUnique, idNotUnique] }),
  ("i-dup3", { append := [fieldEl "/Form/Value" "N" (stringType), fieldEl "/Form/Value" "M" (stringType)], observed := [idNotUnique, idNotUnique, idNotUnique] }),
  ("i-dup-rule", { append := [ruleEl "/Form/Value" "R" "../Value" "FieldFilled(Value)"], observed := [idNotUnique, idNotUnique] }),
  ("i-dup-group", { append := [groupEl "/Form/Value" "G" 1 [fieldEl "/Form/G/X" "X" (stringType)]], observed := [idNotUnique, idNotUnique] }),
  ("i-dup-filtered", { append := [fieldEl "/Form/Value" "N" (stringType) [onlyV1]], observed := [idNotUnique, idNotUnique] }),
  ("i-dup-comp", { append := [computationEl "/Form/Value" "C" "../Total" ["1"]], observed := [idNotUnique, idNotUnique] }),
  ("i-dup-two-ids", { append := [fieldEl "/Form/Value" "N" (stringType), fieldEl "/Form/Other" "M" (stringType)], observed := [idNotUnique, idNotUnique, idNotUnique, idNotUnique] })]

example : disagreeing identifierRows = [] := by native_decide

/-- A defect that stops the build leaves no class; an empty identifier, condition, error entity,
operation or type definition name is a class of its own. -/
private def emptinessRows : List (String × Row) := [
  ("b-field-name-empty", { append := [fieldEl "/Form/Nameless" "" (stringType)], observed := [notBuilt] }),
  ("b-error-entity-empty", { append := [ruleEl "/Form/R" "R" "" "FieldFilled(Value)"], observed := ["MVK_ERROR_FIELD_MISSING", "MVK_MISSING_ERROR_FIELD", entityNotSet] }),
  ("b-error-condition-empty", { append := [ruleEl "/Form/R" "R" "../Value" ""], observed := ["MVK_CONDITION_MISSING", "MVK_INCOMPLETE_INPUT", conditionEmpty] }),
  ("b-computed-field-empty", { append := [computationEl "/Form/C" "C" "" ["1"]], observed := [notBuilt] }),
  ("b-operation-empty", { append := [computationEl "/Form/C" "C" "../Total" [""]], observed := ["MVK_INCOMPLETE_INPUT", operationEmpty] }),
  ("b-enum-dup-categories", { append := [fieldEl "/Form/E" "E" (enumerationType ["a", "b"] [("K", ["a"]), ("K", ["b"])])], observed := [notBuilt] }),
  ("b-index-name-empty", { append := [groupEl "/Form/G" "G" 3 [fieldEl "/Form/G/K" "K" (stringType)] (indexFieldName := "")], observed := [notBuilt] }),
  ("b-sort-name-empty", { append := [groupEl "/Form/G" "G" 3 [fieldEl "/Form/G/K" "K" (stringType)] (sortFieldNames := [""])], observed := [notBuilt] }),
  ("b-typedef-ref-empty", { append := [fieldEl "/Form/T" "T" (typedefType "")], typeDefinitions := [typedefEl "Td" "Td" (stringType)], observed := [notBuilt] }),
  ("b-typedef-id-empty", { typeDefinitions := [typedefEl "" "Td" (stringType)], observed := [idEmpty] }),
  ("b-typedef-name-empty", { typeDefinitions := [typedefEl "Td" "" (stringType)], observed := [typedefNameEmpty] })]

example : disagreeing emptinessRows = [] := by native_decide

/-- A declaration the default variant's `ONLY` filter deletes is never converted, so the conversion
failures of its kept twin are lifted: the model builds and the deleted declaration draws one codeless
notification for its defect (an empty or absent type-definition reference, an empty computed-field path,
two categories of one name whether their values are equal or differ). Each kept twin still leaves no
model. The sentences of an empty operation survive the filter as before, so the deletion lifts build
failures only. The rows are not capture rows: they replay the peer measurement of a12-dmkits `fecf8552`,
`CheckerBasicSentenceAgreementTest` (BoundModel oracle, kernel 30.8.1), recorded at
`docs/sources/inbound-handbacks.md#src-inbound-2026-10-27`. That measurement compares sets of classes,
so no row here carries two lifted notifications and their order is not claimed. -/
private def liftedBuildFailureRows : List (String × Row) := [
  ("o-computed-field-empty-kept", { append := [computationEl "/Form/C" "C" "" ["1"]], observed := [notBuilt] }),
  ("o-computed-field-empty-only", { append := [computationEl "/Form/C" "C" "" ["1"] [onlyV1]], observed := [computedFieldEmpty] }),
  ("o-computed-field-set-only", { append := [computationEl "/Form/C" "C" "../Total" ["1"] [onlyV1]], observed := [] }),
  ("o-operation-empty-only", { append := [computationEl "/Form/C" "C" "../Total" [""] [onlyV1]], observed := ["MVK_INCOMPLETE_INPUT", operationEmpty] }),
  ("o-enum-dup-different-kept", { append := [fieldEl "/Form/E" "E" (enumerationType ["a", "b"] [("K", ["a"]), ("K", ["b"])])], observed := [notBuilt] }),
  ("o-enum-dup-different-only", { append := [fieldEl "/Form/E" "E" (enumerationType ["a", "b"] [("K", ["a"]), ("K", ["b"])]) [onlyV1]], observed := [enumCategoryDuplicate] }),
  ("o-enum-dup-equal-kept", { append := [fieldEl "/Form/E" "E" (enumerationType ["a", "b"] [("K", ["a"]), ("K", ["a"])])], observed := [notBuilt] }),
  ("o-enum-dup-equal-only", { append := [fieldEl "/Form/E" "E" (enumerationType ["a", "b"] [("K", ["a"]), ("K", ["a"])]) [onlyV1]], observed := [enumCategoryDuplicate] }),
  ("o-enum-distinct-only", { append := [fieldEl "/Form/E" "E" (enumerationType ["a", "b"] [("K", ["a"]), ("L", ["b"])]) [onlyV1]], observed := [] }),
  ("o-typedef-ref-empty-kept", { append := [fieldEl "/Form/T" "T" (typedefType "")], typeDefinitions := [typedefEl "Td" "Td" (stringType)], observed := [notBuilt] }),
  ("o-typedef-ref-empty-only", { append := [fieldEl "/Form/T" "T" (typedefType "") [onlyV1]], typeDefinitions := [typedefEl "Td" "Td" (stringType)], observed := [typedefRefEmpty] }),
  ("o-typedef-ref-absent-kept", { append := [fieldEl "/Form/T" "T" typedefTypeWithoutId], typeDefinitions := [typedefEl "Td" "Td" (stringType)], observed := [notBuilt] }),
  ("o-typedef-ref-absent-only", { append := [fieldEl "/Form/T" "T" typedefTypeWithoutId [onlyV1]], typeDefinitions := [typedefEl "Td" "Td" (stringType)], observed := [typedefRefEmpty] }),
  ("o-typedef-ref-resolved-only", { append := [fieldEl "/Form/T" "T" (typedefType "Td") [onlyV1]], typeDefinitions := [typedefEl "Td" "Td" (stringType)], observed := [] }),
  -- An empty name is `isEmpty`, a one-space name only blank: a deleted declaration with an empty name
  -- draws one codeless notification, one with a one-space name draws nothing, and either name on a
  -- kept declaration leaves the model unbuilt (KF626).
  ("o-field-name-empty-kept", { append := [fieldEl "/Form/N" "" (stringType)], observed := [notBuilt] }),
  ("o-field-name-empty-only", { append := [fieldEl "/Form/N" "" (stringType) [onlyV1]], observed := [elementNameEmpty] }),
  ("o-field-name-blank-kept", { append := [fieldEl "/Form/N" " " (stringType)], observed := [notBuilt] }),
  ("o-field-name-blank-only", { append := [fieldEl "/Form/N" " " (stringType) [onlyV1]], observed := [] }),
  ("o-rule-name-empty-kept", { append := [ruleEl "/Form/R" "" "../Value" "FieldFilled(Value)"], observed := [notBuilt] }),
  ("o-rule-name-empty-only", { append := [ruleEl "/Form/R" "" "../Value" "FieldFilled(Value)" [onlyV1]], observed := [elementNameEmpty] }),
  ("o-rule-name-blank-kept", { append := [ruleEl "/Form/R" " " "../Value" "FieldFilled(Value)"], observed := [notBuilt] }),
  ("o-rule-name-blank-only", { append := [ruleEl "/Form/R" " " "../Value" "FieldFilled(Value)" [onlyV1]], observed := [] }),
  ("o-computation-name-empty-kept", { append := [computationEl "/Form/C" "" "../Total" ["1"]], observed := [notBuilt] }),
  ("o-computation-name-empty-only", { append := [computationEl "/Form/C" "" "../Total" ["1"] [onlyV1]], observed := [elementNameEmpty] }),
  ("o-computation-name-blank-kept", { append := [computationEl "/Form/C" " " "../Total" ["1"]], observed := [notBuilt] }),
  ("o-computation-name-blank-only", { append := [computationEl "/Form/C" " " "../Total" ["1"] [onlyV1]], observed := [] })]

example : disagreeing liftedBuildFailureRows = [] := by native_decide

/-- A multi-select group needs repeatability above one, exactly one direct field that is an Enumeration
or String, is required and is not the group's index field, and no nested group; a field the variant
filter removes still counts. -/
private def multiSelectRows : List (String × Row) := [
  ("ms-ok", { append := [groupEl "/Form/MS" "MS" 3 [fieldEl "/Form/MS/Choice" "Choice" (enumerationType ["a", "b"]) [required]] (usageType := "multi-select")], observed := [] }),
  ("ms-string", { append := [groupEl "/Form/MS" "MS" 3 [fieldEl "/Form/MS/Choice" "Choice" (stringType) [required]] (usageType := "multi-select")], observed := [] }),
  ("ms-rule", { append := [groupEl "/Form/MS" "MS" 3 [fieldEl "/Form/MS/Choice" "Choice" (enumerationType ["a", "b"]) [required], ruleEl "/Form/MS/R" "R" "../Choice" "FieldFilled(Choice)"] (usageType := "multi-select")], observed := [] }),
  ("ms-fixed", { append := [groupEl "/Form/MS" "MS" 1 [fieldEl "/Form/MS/Choice" "Choice" (enumerationType ["a", "b"]) [required]] (usageType := "multi-select")], observed := [repeatableGroup] }),
  ("ms-no-field", { append := [groupEl "/Form/MS" "MS" 3 [] (usageType := "multi-select")], observed := [requiredField] }),
  ("ms-two-fields", { append := [groupEl "/Form/MS" "MS" 3 [fieldEl "/Form/MS/Choice" "Choice" (enumerationType ["a", "b"]) [required], fieldEl "/Form/MS/Other2" "Other2" (enumerationType ["a", "b"]) [required]] (usageType := "multi-select")], observed := [requiredField] }),
  ("ms-number", { append := [groupEl "/Form/MS" "MS" 3 [fieldEl "/Form/MS/Choice" "Choice" (numberType (maxFractional := "0")) [required]] (usageType := "multi-select")], observed := [wrongFieldType] }),
  ("ms-no-req", { append := [groupEl "/Form/MS" "MS" 3 [fieldEl "/Form/MS/Choice" "Choice" (enumerationType ["a", "b"])] (usageType := "multi-select")], observed := [requiredFlag] }),
  ("ms-index", { append := [groupEl "/Form/MS" "MS" 3 [fieldEl "/Form/MS/Choice" "Choice" (enumerationType ["a", "b"]) [required]] (usageType := "multi-select") (indexFieldName := "Choice")], observed := [indexField] }),
  ("ms-subgroup", { append := [groupEl "/Form/MS" "MS" 3 [fieldEl "/Form/MS/Choice" "Choice" (enumerationType ["a", "b"]) [required], groupEl "/Form/MS/Sub" "Sub" 1 [fieldEl "/Form/MS/Sub/Y" "Y" (stringType)]] (usageType := "multi-select")], observed := [otherElements] }),
  ("ms-filtered-second", { append := [groupEl "/Form/MS" "MS" 3 [fieldEl "/Form/MS/Choice" "Choice" (enumerationType ["a", "b"]) [required], fieldEl "/Form/MS/Other2" "Other2" (enumerationType ["a", "b"]) [required, onlyV1]] (usageType := "multi-select")], observed := [requiredField] }),
  ("ms-all", { append := [groupEl "/Form/MS" "MS" 1 [fieldEl "/Form/MS/Choice" "Choice" (numberType (maxFractional := "0")), groupEl "/Form/MS/Sub" "Sub" 1 [fieldEl "/Form/MS/Sub/Y" "Y" (stringType)]] (usageType := "multi-select")], observed := [repeatableGroup, requiredFlag, wrongFieldType, otherElements] }),
  ("ms-typedef-enum", { append := [groupEl "/Form/MS" "MS" 3 [fieldEl "/Form/MS/Choice" "Choice" (typedefType "EnTd") [required]] (usageType := "multi-select")], typeDefinitions := [typedefEl "EnTd" "EnTd" (enumerationType ["a", "b"])], observed := [] })]

example : disagreeing multiSelectRows = [] := by native_decide

/-- An attachment group needs its eight fields, four rules compared as exact text under the model's
condition language, and a String `content` allowing both line breaks and unvalidated values. -/
private def attachmentRows : List (String × Row) := [
  ("a-content-typedef", { append := [attachmentGroup (content := typedefType "StrTd")], typeDefinitions := [typedefEl "StrTd" "StrTd" (stringType)], observed := [] }),
  ("a-ok", { append := [attachmentGroup], observed := [] }),
  ("a-missing-field", { append := [attachmentGroup (without := ["description"])], observed := [missingField] }),
  ("a-missing-two", { append := [attachmentGroup (without := ["category", "description"])], observed := [missingField] }),
  ("a-content-config", { append := [attachmentGroup (content := stringType [("noValueValidation", true)])], observed := [contentConfig, "MVK_STRING_TYPE_NO_VAL_AND_NO_LINE_BREAK"] }),
  ("a-content-string", { append := [attachmentGroup (content := stringType)], observed := [contentConfig] }),
  ("a-missing-rule", { append := [attachmentGroup (conditions := (english.take 3))], observed := [requiredRules] }),
  ("a-rule-spacing", { append := [attachmentGroup (conditions := (english.set 3 "GroupFilled(RuleGroup)  and FieldNotFilled(mime_type)"))], observed := [requiredRules] }),
  ("a-content-number", { append := [attachmentGroup (content := numberType (maxFractional := "0"))], observed := [] }),
  ("a-rule-case", { append := [attachmentGroup (conditions := (english.set 3 "GroupFilled(RuleGroup) And FieldNotFilled(mime_type)"))], observed := [requiredRules] }),
  ("a-extra", { append := [attachmentGroup (extraElements := [fieldEl "/Form/Att/extra" "extra" (stringType)])], observed := [] }),
  ("a-filtered-field", { append := [attachmentGroup (filtered := ["description"])], observed := [] }),
  ("a-de-ok", { append := [attachmentGroup (conditions := german)], language := "de_DE", observed := [] }),
  ("a-de-en-order", { append := [attachmentGroup (conditions := (german.take 3))], language := "de_DE", observed := [requiredRules] }),
  ("a-all", { append := [attachmentGroup (without := ["description"]) (content := stringType) (conditions := (english.take 3))], observed := [missingField, requiredRules, contentConfig] })]

example : disagreeing attachmentRows = [] := by native_decide

/-! ## Paths

The captures observe no paths; these pin the element paths the check attaches. -/

private def rowNamed (id : String) : Option Row :=
  ((numberLimitRows ++ boundOrderRows ++ identifierRows ++ emptinessRows ++ liftedBuildFailureRows ++
      multiSelectRows).find?
    (·.1 == id)).map (·.2)

private def outcomeOf (id : String) : Option ModelConsistencyOutcome :=
  (rowNamed id).bind fun row => (checkModelConsistency (modelOf row)).toOption

example : outcomeOf "i-root-id" = some (.checked [
    { path := ["Form"], kind := .idNotUnique }, { path := ["Form", "A1"], kind := .idNotUnique }]) := by
  native_decide

example : outcomeOf "b-index-name-empty" = some (.notBuilt ["Form", "G"] .indexFieldNameEmpty) := by
  native_decide

example : outcomeOf "d3-min-long-max-negzero" = some (.checked [
    { path := ["Form", "N"], kind := .numberMinValueExceeded },
    { path := ["Form", "N"], kind := .boundSignedZero },
    { path := ["Form", "N"], kind := .boundTotalDigitsTooLong }]) := by
  native_decide

example : outcomeOf "b-typedef-id-empty" = some (.checked [
    { path := ["Td"], kind := .idEmpty }]) := by
  native_decide

example : outcomeOf "o-computed-field-empty-only" = some (.checked [
    { path := ["Form", "C"], kind := .computedFieldEmpty }]) := by
  native_decide

/-! ## Type definitions in id order, and a repeated id

Peer KF647 (a12-dmkits `ceabf655`, `CheckerBasicSentenceOrderAgreementTest`) and a local `model check`
probe of 2026-10-29 ([inbound 2026-10-29](../../../docs/sources/inbound-handbacks.md#src-inbound-2026-10-29)),
which compare the Kernel's sentences in order, each naming its definition. -/

/-- The definitions each name-empty notification names, in order, for definitions with empty names. -/
private def namedDefinitions (ids : List String) : Option (List String) :=
  (checkModelConsistency (modelOf { typeDefinitions := some (ids.map (typedefEl · "" stringType)), observed := [] })).toOption.bind
    fun | .checked notifications => some (notifications.filterMap fun notification =>
            if notification.kind == .typeDefinitionNameEmpty then notification.path.head? else none)
        | .notBuilt _ _ => none

/-- Declared `Beta`, `""` named `Alpha` and `Gamma`, beside a deleted field with an empty name: the
id-empty sentence of `Alpha` first, then the two name sentences, then the field's (peer row). -/
private def peerDefinitionRow : Row where
  append := [fieldEl "/Form/X" "" stringType [onlyV1]]
  typeDefinitions := [typedefEl "Beta" "" stringType, typedefEl "" "Alpha" stringType, typedefEl "Gamma" "" stringType]
  observed := []

example : (checkModelConsistency (modelOf peerDefinitionRow)).toOption = some (.checked [
      { path := ["Alpha"], kind := .idEmpty }, { path := ["Beta"], kind := .typeDefinitionNameEmpty },
      { path := ["Gamma"], kind := .typeDefinitionNameEmpty }, { path := ["Form", ""], kind := .elementNameEmpty }]) := by
  native_decide

/-- The walk sorts the ids, uppercase before lowercase as Java's string order puts them (local probe:
`Beta`, `Zeta`, `alpha` from `Zeta`, `alpha`, `Beta`), whatever the declaration order (peer probes). -/
example :
    namedDefinitions ["Zeta", "alpha", "Beta"] = some ["Beta", "Zeta", "alpha"] ∧
    namedDefinitions ["Beta", "Gamma", "Alpha"] = some ["Alpha", "Beta", "Gamma"] ∧
    namedDefinitions ["Gamma", "Alpha", "Beta"] = some ["Alpha", "Beta", "Gamma"] := by
  native_decide

/-- Two definitions sharing an id, the empty one or `Beta`, leave no model in both readers (peer rows). -/
example :
    ["", "Beta"].all fun id =>
      let json := modelOf { typeDefinitions := some [typedefEl id "A" stringType, typedefEl id "B" stringType], observed := [] }
      (checkModelConsistency json).toOption == some (.notBuilt [id] .typeDefinitionIdRepeated) &&
        (readModel json).toOption.isNone := by
  native_decide

end A12Kernel.Dm.ModelConsistencyLocks
