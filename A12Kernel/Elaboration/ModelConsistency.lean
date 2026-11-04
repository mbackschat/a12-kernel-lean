import A12Kernel.Elaboration.CharsetSpec
import A12Kernel.Elaboration.DeclaredLocale
import A12Kernel.Elaboration.IndexAndSortDeclaration
import A12Kernel.Elaboration.StaticDiagnostic
import A12Kernel.Elaboration.ValidationMessageTypes
import A12Kernel.Semantics.NumberBound

/-! # A12Kernel.Elaboration.ModelConsistency — the notifications a model's consistency check raises

The Kernel checks a whole model by collecting notifications, not by stopping at the first refusal, so
the multiplicity, the class and the order of each notification are observable. This module is the
collection over an already-read model, measured against kernel 30.8.1 over two retained captures
(`evidence/kernel-30.8.1/captures/model-consistency-2026-10-13/` and
`evidence/kernel-30.8.1/captures/model-consistency-bound-order-2026-10-13/`). The captures record
class labels only, so a notification's path is the model's own element path and is not an observed
quantity.

A model that cannot be built yields no notification at all: a conversion that builds no validation model, or
the first element, in walk order, with one of the other `ModelBuildFailure` defects, stops the check. A
group's index or sort spelling is one of them when it leaves no model (`NominationFailure`, a sort name
written empty included); an index written empty is not, and draws a class of its own in check 6 (peer
KF653, a12-dmkits `1124b523f`, kernel 31.1.1). So is a field whose Enumeration declares no values, or two
categories of one name, the empty name and an absent one reading as one key (peer KF654, KF660). An
empty or blank name, a type-definition reference with no id and a computation with no computed-field path
are not such defects on kernel 31.1.1: its converter states a sentence and goes on without the declaration
(the validation-model converter, `Reference/Dm/ModelConversion.lean`), while this basic check still walks
the authored model. Otherwise six checks run in this registration order and their notifications concatenate
in it, so a class is never interleaved with another check's. The numbered ones follow spec/01 §1.2, whose
second rule, the Number value limit, kernel 31.1.0 deleted (peer KF582, a12-dmkits
`CheckerNumberBoundMagnitudeAgreementTest` at `1124b523f`): a bound is judged by no magnitude its fractional
digits allow, and its number is not reused.

1. Element identifier uniqueness, over every group, field, rule and computation; a type definition is
   outside it. The empty identifier is an ordinary identifier here.
3. Attachment groups: the required fields, the required rules and the `content` field's String
   configuration.
4. Multi-select groups: repeatability, the single Enumeration or String field and its requiredness, and
   the absence of nested groups and computations.
   Then, unnumbered in spec/01 §1.2, the document uniqueness criteria (spec/01 §1.5). This placement follows
   the registration order reported for kernel 31.1.1, after the multi-select rule and before code generation;
   it is not separately measured here, and the criteria's order against every other rule is unmeasured.
5. The formal check of each printed bound (`NumberBound.printed?`), maximum first.
6. Emptiness of identifiers, element names, type-definition references, computed-field paths, group index
   fields, rule conditions, rule error entities, computation operations and type definition names.

A declaration's `variantFilter` and a rule's `variantErrorMessages` are retired (DM 29.1) and read past
as an unknown member is, so no element is deleted and every check walks every element.
The walk visits the model's own type definitions first, as declared when the model has nothing to expand and
sorted by id case-sensitively, by UTF-16 code unit, when it has (`ConsistencyModel.expands`; a12-dmkits
`CheckerBasicSentenceOrderAgreementTest` at `1124b523f`, kernel 31.1.1, where 30.8.1 always sorted), then
elements depth-first, a group before its children. Within one check the notifications follow the walk. Two
type definitions sharing an id leave the model unbuilt before any element is judged (peer KF647 and a local
probe, `docs/sources/inbound-handbacks.md#src-inbound-2026-10-29`).

The captures fix identifier uniqueness before emptiness and the maximum's printed-bound class before the
minimum's (kernel 30.8.1); the remaining registration order, a `content` field missing either String flag,
the nested-element test regardless of the field count, and the first child named `content` of any kind are
read from the Kernel's consistency rule sources at kernel 30.8.1, not separately measured ([checkpoint](../../docs/sources/model-structure-and-declaration-probes.md#src-model-consistency-k17)).
Two build failures in one model and the order across distinct duplicated identifiers are unmeasured;
a label-only capture cannot separate the latter. The order of one element's classes in check 6 is
unmeasured too: a peer measurement of a12-dmkits `1124b523f` (`CheckerConverterSentenceAgreementTest`,
kernel 31.1.1) compares sets of classes.

The criteria check is measured on one "en_US" model, so each declared locale needing a text, and the order of
one criterion's refusals, are derived and unmeasured (`uniquenessCriterionNotifications`).

Not claimed: type definitions' own bodies, a bound outside the normal double range (an error, not a
class), attachment condition texts under a language the captures do not cover, the combination of
an invalid multi-select field count with nested groups, and the resolution of a computed field's path.
-/

namespace A12Kernel

/-- The type of a field as the consistency check reads it. -/
inductive ConsistencyFieldType where
  | number (minFractionalDigits maxFractionalDigits : Int) (minValue maxValue : Option Rat)
  | string (noValueValidation lineBreaksPermitted : Bool)
  /-- An Enumeration as the check reads it: its category names as bound, and whether it declares a value. -/
  | enumeration (categoryNames : List String) (hasValues : Bool)
  /-- A reference to a declared type definition, unresolved. -/
  | typeDefinition (id : String)
  | other (typeName : String)
  deriving Repr, DecidableEq

/-- A field with the facts the checks consume. `declared` is what the field authors; `effective` is the
type after a type definition is resolved, which is `declared` itself otherwise and absent when the
reference resolves to nothing. -/
structure ConsistencyField where
  id : String
  name : String
  declared : ConsistencyFieldType
  effective : Option ConsistencyFieldType
  /-- Whether a requiredness configuration is authored. -/
  requirednessDeclared : Bool
  /-- The text of the requiredness configuration's `mode`, absent when the field authors none. -/
  requirednessMode : Option String := none
  /-- Whether the field is not persisted. -/
  transient : Bool := false
  deriving Repr, DecidableEq

/-- One authored element. A group lists its children in authored order. -/
inductive ConsistencyElement where
  | group (id name : String) (repeatability : Nat) (usageType : Option String)
      (indexFieldName : Option String) (sortFieldNames : List String)
      (elements : List ConsistencyElement)
  | field (field : ConsistencyField)
  | rule (id name errorCondition errorEntityRelPath : String)
  | computation (id name computedFieldRelPath : String) (operations : List String)

structure ConsistencyTypeDefinition where
  id : String
  name : String
  deriving Repr, DecidableEq

/-- A frame shape the Kernel builds a model from but whose entry consistency check then fails without a
class: `header.modelVersion` or `header.locales` written `null` (kernel 30.8.1 rows; an absent one leaves no
model on 31.1.1), no `content.modelInfo`, or a `null` supported character (peer KF650), and a condition language that parses as a locale other than "en_US"
and "de_DE", measured for the codes the peer letter of 2026-10-30a lists. -/
inductive FrameCheckFailure where
  | versionMissing
  | modelInfoMissing
  | localesMissing
  | supportedCharacterNull
  | conditionLanguageUnsupported
  deriving Repr, DecidableEq

/-- One document uniqueness criterion as the check reads it (spec/01 §1.5): its name, each field's full path
as written, and each error text with its locale as `ParsedLocale.key`. -/
structure ConsistencyUniquenessCriterion where
  name : String
  fieldPaths : List String
  errorTexts : List (String × String)
  deriving Repr, DecidableEq

structure ConsistencyModel where
  typeDefinitions : List ConsistencyTypeDefinition
  rootGroups : List ConsistencyElement
  /-- The model's condition language code, which selects the attachment rules' required texts. -/
  conditionLanguage : String
  /-- The locales the header declares, in declaration order. -/
  declaredLocales : List ParsedLocale := []
  /-- The check-only frame shape the model is written with, if any. -/
  frameCheckFailure? : Option FrameCheckFailure := none
  /-- A label locale the JDK tags specially, which leaves no model. -/
  jdkTaggedLabel? : Option String := none
  /-- Whether the validation-model converter builds no model from the authored one. -/
  validationModelUnbuilt : Bool := false
  /-- Whether the model has something to expand before its check: a header entry naming a model to import, or
  a group carrying an `includeConfig` that is not `null` (a12-dmkits Letter E §4, source-read). The check then
  walks the type definitions by id; otherwise in declared order. -/
  expands : Bool := false
  /-- The document uniqueness criteria, in authored order; an absent member and an empty list are none. -/
  uniquenessCriteria : List ConsistencyUniquenessCriterion := []

/-- A notification class of the consistency check. Every class is an ERROR. -/
inductive ModelConsistencyClass where
  | idNotUnique
  | attachmentMissingField
  | attachmentRequiredRules
  | attachmentContentConfig
  | multiSelectRepeatableGroup
  | multiSelectRequiredField
  | multiSelectRequiredFlag
  | multiSelectIndexField
  | multiSelectFieldType
  | multiSelectOtherElements
  /-- A printed bound holding more digits than a stored Number may
  (`NumericFormalReadError.totalDigitsTooLong`). -/
  | boundTotalDigitsTooLong
  /-- A printed bound that is a negative zero (`NumericFormalReadError.signedZero`). -/
  | boundSignedZero
  | idEmpty
  | errorConditionEmpty
  | errorEntityEmpty
  | computationOperationEmpty
  | typeDefinitionNameEmpty
  /-- An empty element name, absent and `null` included; a blank name that is not empty draws none. -/
  | elementNameEmpty
  /-- A field typed by a type-definition reference whose id is absent or empty. -/
  | typeDefinitionReferenceEmpty
  /-- A computation whose computed-field path is empty. -/
  | computedFieldEmpty
  /-- A group whose index field is written empty, which keeps the group's own name where a field is
  expected. A blank spelling that is not empty draws none. -/
  | indexFieldNameEmpty
  /-- A header declaring no locale (spec/01 §1.1). -/
  | supportedLanguagesMissing
  /-- Two distinct declared locales sharing one JDK language tag (`ParsedLocale.languageTag`). -/
  | supportedLanguagesDuplicate
  /-- A document uniqueness criterion whose name is empty. -/
  | uniquenessCriterionNameMissing
  /-- A criterion naming no field. -/
  | uniquenessCriterionNoField
  /-- A criterion field whose path names no field: nothing, a group or a relative path. -/
  | uniquenessCriterionFieldNotFound
  /-- A criterion field with no requiredness or required relative to its parent. -/
  | uniquenessCriterionFieldNotRequired
  /-- A criterion field inside a repeatable group. -/
  | uniquenessCriterionFieldRepeatable
  /-- A transient criterion field. -/
  | uniquenessCriterionFieldTransient
  /-- A criterion with no error text for a declared locale. -/
  | uniquenessCriterionTextMissing
  /-- A criterion sharing its name with another, drawn once for each of the two. -/
  | uniquenessCriterionNameDuplicate
  /-- An error text parameter naming no field of its own criterion. -/
  | uniquenessCriterionParameterInvalid
  /-- An error text with an unterminated `$`: the keyed class `WRONG_NUMBER_OF_DOLLARS` the rule messages
  share, reached through the shared message-text gate. -/
  | uniquenessCriterionDollars
  deriving Repr, DecidableEq

namespace ModelConsistencyClass

/-- Every class once, in declaration order. -/
def all : List ModelConsistencyClass :=
  [idNotUnique, attachmentMissingField,
    attachmentRequiredRules, attachmentContentConfig, multiSelectRepeatableGroup,
    multiSelectRequiredField, multiSelectRequiredFlag, multiSelectIndexField, multiSelectFieldType,
    multiSelectOtherElements, boundTotalDigitsTooLong, boundSignedZero, idEmpty, errorConditionEmpty,
    errorEntityEmpty, computationOperationEmpty, typeDefinitionNameEmpty, elementNameEmpty,
    typeDefinitionReferenceEmpty, computedFieldEmpty, indexFieldNameEmpty, supportedLanguagesMissing,
    supportedLanguagesDuplicate, uniquenessCriterionNameMissing, uniquenessCriterionNoField,
    uniquenessCriterionFieldNotFound, uniquenessCriterionFieldNotRequired,
    uniquenessCriterionFieldRepeatable, uniquenessCriterionFieldTransient, uniquenessCriterionTextMissing,
    uniquenessCriterionNameDuplicate, uniquenessCriterionParameterInvalid, uniquenessCriterionDollars]

/-- The label the captures give the class. The two supported-language classes carry their Kernel code;
every other class is codeless and named by itself. -/
def observedLabel : ModelConsistencyClass → String
  | idNotUnique => "codeless:id-not-unique"
  | attachmentMissingField => "codeless:attachment-missing-field"
  | attachmentRequiredRules => "codeless:attachment-required-rules"
  | attachmentContentConfig => "codeless:attachment-content-config"
  | multiSelectRepeatableGroup => "codeless:multi-select-repeatable-group"
  | multiSelectRequiredField => "codeless:multi-select-required-field"
  | multiSelectRequiredFlag => "codeless:multi-select-required-flag"
  | multiSelectIndexField => "codeless:multi-select-index-field"
  | multiSelectFieldType => "codeless:multi-select-fieldtype"
  | multiSelectOtherElements => "codeless:multi-select-other-elements"
  | boundTotalDigitsTooLong => "codeless:metamodel-formal:STELLIGKEIT_ZU_LANG"
  | boundSignedZero => "codeless:metamodel-formal:ZAHL_NULL_ENTHAELT_VORZEICHEN"
  | idEmpty => "codeless:id-empty"
  | errorConditionEmpty => "codeless:error-condition-empty"
  | errorEntityEmpty => "codeless:error-entity-not-set"
  | computationOperationEmpty => "codeless:computation-operation-empty"
  | typeDefinitionNameEmpty => "codeless:typedef-name-empty"
  | elementNameEmpty => "codeless:element-name-empty"
  | typeDefinitionReferenceEmpty => "codeless:typedef-reference-empty"
  | computedFieldEmpty => "codeless:computed-field-empty"
  | indexFieldNameEmpty => "codeless:index-field-name-empty"
  | supportedLanguagesMissing => "MVK_SUPP_LANGUAGES_MISSING"
  | supportedLanguagesDuplicate => "MVK_SUPP_LANGUAGES_DUPLICATE"
  | uniquenessCriterionNameMissing => "codeless:uniqueness-criterion-name-missing"
  | uniquenessCriterionNoField => "codeless:uniqueness-criterion-no-field"
  | uniquenessCriterionFieldNotFound => "codeless:uniqueness-criterion-field-not-found"
  | uniquenessCriterionFieldNotRequired => "codeless:uniqueness-criterion-field-not-required"
  | uniquenessCriterionFieldRepeatable => "codeless:uniqueness-criterion-field-repeatable"
  | uniquenessCriterionFieldTransient => "codeless:uniqueness-criterion-field-transient"
  | uniquenessCriterionTextMissing => "codeless:uniqueness-criterion-text-missing"
  | uniquenessCriterionNameDuplicate => "codeless:uniqueness-criterion-name-duplicate"
  | uniquenessCriterionParameterInvalid => "codeless:uniqueness-criterion-parameter-invalid"
  | uniquenessCriterionDollars => KernelStaticDiagnostic.wrongNumberOfDollars.kernelCode

end ModelConsistencyClass

/-- A defect after which the Kernel's check reports no class: the model is not built at all, or, for a
check-only frame shape, built and then unchecked. -/
inductive ModelBuildFailure where
  /-- The validation-model converter builds no model (`convertModel`'s `unbuilt`). -/
  | validationModelUnbuilt
  | enumerationCategoryNameDuplicated
  /-- A field whose Enumeration, resolved through its type definition, declares no value. -/
  | enumerationValuesMissing
  /-- A group's index or sort spelling that leaves no model, the empty sort name apart. -/
  | nomination (failure : NominationFailure)
  | sortFieldNameEmpty
  /-- Two type definitions carry one id, the empty id included. -/
  | typeDefinitionIdRepeated
  /-- A declared locale with an empty language, or two codes naming one locale. -/
  | declaredLocale (failure : DeclaredLocaleFailure)
  /-- A label locale the JDK tags specially (kernel 31.1.1, spec/01 §1.1). -/
  | labelLocaleTagged (key : String)
  | frameCheck (failure : FrameCheckFailure)
  deriving Repr, DecidableEq

structure ModelConsistencyNotification where
  /-- Names from the root group to the element the class concerns. A type definition is named by its id,
  or by its name when the id is empty, as the Kernel's sentence names it (peer KF647's lock compares
  which definition each sentence names). -/
  path : List String
  kind : ModelConsistencyClass
  deriving Repr, DecidableEq

inductive ModelConsistencyOutcome where
  /-- The check reports no class: the model cannot be built, or a check-only frame shape fails its check;
  `path` names the first offending element. -/
  | notBuilt (path : List String) (failure : ModelBuildFailure)
  | checked (notifications : List ModelConsistencyNotification)
  deriving Repr, DecidableEq

/-- The capture labels of the outcome: the Kernel's single unbuilt-model label, or each notification's. -/
def ModelConsistencyOutcome.observedLabels : ModelConsistencyOutcome → List String
  | .notBuilt _ _ => ["codeless:model-not-built"]
  | .checked notifications => notifications.map (·.kind.observedLabel)

namespace ConsistencyElement

def id : ConsistencyElement → String
  | group id .. | rule id .. | computation id .. => id
  | field f => f.id

def name : ConsistencyElement → String
  | group _ name .. | rule _ name .. | computation _ name .. => name
  | field f => f.name

/-- The direct children; only a group has any. -/
def children : ConsistencyElement → List ConsistencyElement
  | group _ _ _ _ _ _ elements => elements
  | _ => []

def asField? : ConsistencyElement → Option ConsistencyField
  | field f => some f
  | _ => none

/-- The declaration defect that stops the Kernel building the model: an Enumeration declaring two categories
of one name, judged on the declared type, so a type definition's own categories are outside it, or no value at
all, judged on the type the field resolves to as the declaration walk judges it. -/
def conversionFailure? : ConsistencyElement → Option ModelBuildFailure
  | .field f =>
      let repeatedCategoryName := match f.declared with
        | .enumeration categoryNames _ => decide (categoryNames.eraseDups.length < categoryNames.length)
        | _ => false
      if repeatedCategoryName then some .enumerationCategoryNameDuplicated
      else match f.effective with
        | some (.enumeration _ false) => some .enumerationValuesMissing
        | _ => none
  | _ => none

/-- Whether the element is a group or a computation, the kinds a multi-select group may not nest. -/
def isGroupOrComputation : ConsistencyElement → Bool
  | group .. | computation .. => true
  | _ => false

mutual
/-- The element with its path, then its descendants depth-first. -/
def walk (parent : List String) : ConsistencyElement → List (List String × ConsistencyElement)
  | element@(group _ name _ _ _ _ children) =>
      (parent ++ [name], element) :: walkAll (parent ++ [name]) children
  | element => [(parent ++ [element.name], element)]

def walkAll (parent : List String) : List ConsistencyElement → List (List String × ConsistencyElement)
  | [] => []
  | element :: rest => walk parent element ++ walkAll parent rest
end

mutual
/-- The fields at and below the element, each with its full path (the names from the root, each after a `/`)
and whether a group on the way declares a repeatability above one. -/
def placedFields (parent : List String) (repeatable : Bool) :
    ConsistencyElement → List (String × ConsistencyField × Bool)
  | group _ name count _ _ _ children => placedFieldsAll (parent ++ [name]) (repeatable || 1 < count) children
  | field f => [(String.join ((parent ++ [f.name]).map ("/" ++ ·)), f, repeatable)]
  | _ => []

def placedFieldsAll (parent : List String) (repeatable : Bool) :
    List ConsistencyElement → List (String × ConsistencyField × Bool)
  | [] => []
  | element :: rest => placedFields parent repeatable element ++ placedFieldsAll parent repeatable rest
end

end ConsistencyElement

namespace ConsistencyModel

/-- Every element with its path in walk order. Type definitions are not elements. -/
def entries (model : ConsistencyModel) : List (List String × ConsistencyElement) :=
  ConsistencyElement.walkAll [] model.rootGroups

/-- The fields among `entries`. -/
def fieldEntries (model : ConsistencyModel) : List (List String × ConsistencyField) :=
  model.entries.filterMap fun (path, element) => element.asField?.map (path, ·)

end ConsistencyModel

namespace ModelConsistency

private def notification (path : List String) (kind : ModelConsistencyClass) :
    ModelConsistencyNotification :=
  { path, kind }

/-- The notification when the condition holds. -/
private def raiseIf (condition : Bool) (path : List String) (kind : ModelConsistencyClass) :
    List ModelConsistencyNotification :=
  if condition then [notification path kind] else []

/-- The defect of one element that stops the Kernel building the model. A group's spellings are read from
its own path against the authored groups, which `isGroup` names. -/
def buildFailure? (isGroup : List String → Bool) (path : List String) : ConsistencyElement →
    Option ModelBuildFailure
  | .group _ _ _ _ indexFieldName sortFieldNames _ =>
      if sortFieldNames.any (·.isEmpty) then some .sortFieldNameEmpty
      else ((indexFieldName.toList ++ sortFieldNames).findSome? (nominationFailure? isGroup path)).map .nomination
  | element@(.field _) | element@(.rule ..) | element@(.computation ..) => element.conversionFailure?

/-- The first id two type definitions share, which every model reader refuses before building. -/
def repeatedTypeDefinitionId? (ids : List String) : Option String :=
  ids.find? fun id => 1 < ids.count id

/-- The path a type definition's notification names. -/
def typeDefinitionPath (definition : ConsistencyTypeDefinition) : List String :=
  [if definition.id.isEmpty then definition.name else definition.id]

/-- The first build failure, with the path of the offending element or type definition: a check-only
frame shape's, then a declared locale's, both with no path, then a repeated type-definition id, which the
Kernel meets while expanding the definitions, then the converter's, with no path, and then each element's
in walk order. Which of two such failures the Kernel names is unmeasured; either leaves the one unbuilt
label. -/
def firstBuildFailure? (model : ConsistencyModel) : Option (List String × ModelBuildFailure) :=
  if let some failure := model.frameCheckFailure? then some ([], .frameCheck failure)
  else if let some failure := declaredLocaleFailure? model.declaredLocales then some ([], .declaredLocale failure)
  else if let some key := model.jdkTaggedLabel? then some ([], .labelLocaleTagged key)
  else match repeatedTypeDefinitionId? (model.typeDefinitions.map (·.id)) with
  | some id => some ([id], .typeDefinitionIdRepeated)
  | none =>
      if model.validationModelUnbuilt then some ([], .validationModelUnbuilt)
      else
        let groupPaths := model.entries.filterMap fun (path, element) =>
          match element with | .group .. => some path | _ => none
        model.entries.findSome? fun (path, element) =>
          (buildFailure? groupPaths.contains path element).map (path, ·)

/-- The type definitions in the order the checks walk them: as declared for a model with nothing to expand,
and otherwise by id, compared by UTF-16 code unit (a local probe of 2026-10-29 and peer KF647's Latin-1 row,
the declared order a12-dmkits `CheckerBasicSentenceOrderAgreementTest` at `1124b523f`, kernel 31.1.1).
Supplementary-plane ids are unmeasured. -/
def orderedTypeDefinitions (model : ConsistencyModel) : List ConsistencyTypeDefinition :=
  if model.expands then
    model.typeDefinitions.mergeSort fun first second => !(utf16Units second.id < utf16Units first.id)
  else model.typeDefinitions

/-- Check 1. Every occurrence of an identifier shared with another element is reported. -/
def idUniquenessNotifications (model : ConsistencyModel) : List ModelConsistencyNotification :=
  let ids := model.entries.map (·.2.id)
  model.entries.flatMap fun (path, element) =>
    raiseIf (1 < ids.count element.id) path .idNotUnique

/-- The field names an attachment group must declare. -/
def attachmentRequiredFieldNames : List String :=
  ["original_filename", "internal_filename", "content", "attachment_id", "size", "mime_type",
    "category", "description"]

/-- The four rule conditions an attachment group must carry, as the condition language writes them,
compared by exact string equality: the captures' spacing and case variants all miss. A language the
captures do not cover has no entry. -/
def attachmentRequiredConditions : String → Option (List String)
  | "en_US" => some [
      "GroupFilled(RuleGroup) and NotExactlyOneFieldFilled(attachment_id, content)",
      "FieldFilled(content) and FieldNotFilled(size)",
      "GroupFilled(RuleGroup) and FieldNotFilled(internal_filename)",
      "GroupFilled(RuleGroup) and FieldNotFilled(mime_type)"]
  | "de_DE" => some [
      "KontextAngegeben(RegelKontext) und NichtGenauEinFeldAngegeben(attachment_id, content)",
      "FeldAngegeben(content) und FeldNichtAngegeben(size)",
      "KontextAngegeben(RegelKontext) und FeldNichtAngegeben(internal_filename)",
      "KontextAngegeben(RegelKontext) und FeldNichtAngegeben(mime_type)"]
  | _ => none

/-- Check 3 for one attachment group: the missing-field class, then the missing-rule class, then the
`content` configuration. The configuration is read from the first direct child named `content`, of any
kind, and from its declared type, so a type definition or a Number `content` draws nothing. -/
def attachmentNotifications (language : String) (path : List String)
    (children : List ConsistencyElement) : Except String (List ModelConsistencyNotification) := do
  let some requiredConditions := attachmentRequiredConditions language
    | throw s!"attachment rule texts of condition language {language} are not measured"
  let fieldNames := children.filterMap fun child => child.asField?.map (·.name)
  let conditions := children.filterMap fun
    | .rule _ _ errorCondition _ => some errorCondition
    | _ => none
  let contentConfigured :=
    match children.find? (·.name == "content") with
    | some (.field { declared := .string noValueValidation lineBreaksPermitted, .. }) =>
        noValueValidation && lineBreaksPermitted
    | _ => true
  pure (raiseIf (attachmentRequiredFieldNames.any (!fieldNames.contains ·)) path .attachmentMissingField ++
    raiseIf (requiredConditions.any (!conditions.contains ·)) path .attachmentRequiredRules ++
    raiseIf (fieldNames.contains "content" && !contentConfigured) path .attachmentContentConfig)

/-- Check 3 over every group whose usage type is `attachment`. The condition language is consulted
only when such a group exists. -/
def attachmentGroupNotifications (model : ConsistencyModel) :
    Except String (List ModelConsistencyNotification) :=
  model.entries.foldlM (init := []) fun notifications (path, element) =>
    match element with
    | .group _ _ _ (some "attachment") _ _ children => do
        pure (notifications ++ (← attachmentNotifications model.conditionLanguage path children))
    | _ => pure notifications

/-- Whether the effective type is an Enumeration or a String, the two a multi-select field may have. An
unresolvable reference is neither. -/
private def isSelectableType : Option ConsistencyFieldType → Bool
  | some (.enumeration ..) | some (.string ..) => true
  | _ => false

/-- Check 4 for one multi-select group. Exactly one direct field child is required; its requiredness,
its use as the group's index field and its type are judged only then. Nested groups and computations
are judged whatever the field count, a combination the captures leave unmeasured. -/
def multiSelectNotifications (path : List String) (repeatability : Nat)
    (indexFieldName : Option String) (children : List ConsistencyElement) :
    List ModelConsistencyNotification :=
  let fields := children.filterMap (·.asField?)
  raiseIf (repeatability ≤ 1) path .multiSelectRepeatableGroup ++
    (match fields with
      | [field] =>
          raiseIf (!field.requirednessDeclared) path .multiSelectRequiredFlag ++
            raiseIf (indexFieldName == some field.name) path .multiSelectIndexField ++
            raiseIf (!isSelectableType field.effective) path .multiSelectFieldType
      | _ => [notification path .multiSelectRequiredField]) ++
    raiseIf (children.any (·.isGroupOrComputation)) path .multiSelectOtherElements

/-- Check 4 over every group whose usage type is `multi-select`. -/
def multiSelectGroupNotifications (model : ConsistencyModel) : List ModelConsistencyNotification :=
  model.entries.flatMap fun (path, element) =>
    match element with
    | .group _ _ repeatability (some "multi-select") indexFieldName _ children =>
        multiSelectNotifications path repeatability indexFieldName children
    | _ => []

/-- The requiredness mode of a field a uniqueness criterion may name. -/
private def criterionRequiredMode : String := "absoluteOrRelativeToNextRepAncestor"

/-- The refusals of one criterion field, named by its path as written: no field of that full path, which
a group, a rule and a relative path all fail, or, for a field, the requiredness, repeatability and
transience refusals, in that order (each measured alone; their order is unmeasured). -/
private def criterionFieldNotifications (placed : List (String × ConsistencyField × Bool))
    (path : List String) (fullName : String) : List ModelConsistencyNotification :=
  match placed.find? (·.1 == fullName) with
  | none => [notification path .uniquenessCriterionFieldNotFound]
  | some (_, field, repeatable) =>
      raiseIf (field.requirednessMode != some criterionRequiredMode) path .uniquenessCriterionFieldNotRequired ++
        raiseIf repeatable path .uniquenessCriterionFieldRepeatable ++
        raiseIf field.transient path .uniquenessCriterionFieldTransient

/-- The refusals of one criterion's error text for one declared locale: no entry for the locale (the first
entry of a locale is read when several are written, unmeasured), an unterminated `$`, which stops the
parameters being read, or a parameter that is neither a field path of the criterion nor that path with a
`.value` suffix. A text the shared message-text gates refuse for a line break, a control character or no
characters at all is outside the measured profile, since no row measures it for a criterion; an empty
parameter pair is read as a parameter naming no field, unmeasured. -/
private def criterionTextNotifications (path : List String) (criterion : ConsistencyUniquenessCriterion)
    (locale : ParsedLocale) : Except String (List ModelConsistencyNotification) :=
  match criterion.errorTexts.find? (·.1 == locale.key) with
  | none => pure [notification path .uniquenessCriterionTextMissing]
  | some (_, text) =>
      match validateMessageTemplateSource text with
      | .error .oddDollarCount => pure [notification path .uniquenessCriterionDollars]
      | .error _ => throw s!"error text of uniqueness criterion {criterion.name} fails a gate unmeasured for criteria"
      | .ok segments =>
          let named (parameter : String) :=
            criterion.fieldPaths.any fun fullName => parameter == fullName || parameter == fullName ++ ".value"
          pure (raiseIf ((messageParameterPieces segments).any (!named ·)) path .uniquenessCriterionParameterInvalid)

/-- The notifications of one criterion: an empty name, a name another criterion carries, no field, each
field's refusals in the written order, then each declared locale's text. The path is the criterion's name,
derived, as is the order among these. -/
private def criterionNotifications (model : ConsistencyModel) (criterion : ConsistencyUniquenessCriterion) :
    Except String (List ModelConsistencyNotification) := do
  let path := [criterion.name]
  let placed := ConsistencyElement.placedFieldsAll [] false model.rootGroups
  let sharesName := 1 < (model.uniquenessCriteria.filter (·.name == criterion.name)).length
  let texts ← model.declaredLocales.flatMapM (criterionTextNotifications path criterion)
  pure (raiseIf criterion.name.isEmpty path .uniquenessCriterionNameMissing ++
    raiseIf sharesName path .uniquenessCriterionNameDuplicate ++
    raiseIf criterion.fieldPaths.isEmpty path .uniquenessCriterionNoField ++
    criterion.fieldPaths.flatMap (criterionFieldNotifications placed path) ++ texts)

/-- The document uniqueness criteria check (spec/01 §1.5), each criterion in authored order. The empty name
is judged for duplicates like any other, unmeasured. -/
def uniquenessCriterionNotifications (model : ConsistencyModel) :
    Except String (List ModelConsistencyNotification) :=
  model.uniquenessCriteria.flatMapM (criterionNotifications model)

/-- The formal-check class of a printed bound: more digits than a stored Number may hold, otherwise a
negative zero. The digit count leaves out the sign and the decimal point. -/
def boundFormalClass? (printed : String) : Option ModelConsistencyClass :=
  let digits := printed.toList.filter fun character => character != '-' && character != '.'
  if numericStoredDigitLimit < digits.length then some .boundTotalDigitsTooLong
  else if printed.startsWith "-" && digits.all (· == '0') then some .boundSignedZero
  else none

/-- The class of one declared bound, absent when the bound is absent or passes. A bound outside the
normal double range has no printed form in the represented profile and is an error, not a class. -/
private def boundClass? (bound : Option Rat) (minFractionalDigits maxFractionalDigits : Int) :
    Except String (Option ModelConsistencyClass) :=
  match bound with
  | none => pure none
  | some authored =>
      match NumberBound.printed? authored minFractionalDigits maxFractionalDigits with
      | none => throw "bound outside the normal double range"
      | some printed => pure (boundFormalClass? printed)

/-- Check 5: the maximum's class, then the minimum's, the second dropped when it equals the first at the
same field. -/
def boundFormalNotifications (model : ConsistencyModel) :
    Except String (List ModelConsistencyNotification) :=
  model.fieldEntries.foldlM (init := []) fun notifications (path, field) =>
    match field.effective with
    | some (.number minFractionalDigits maxFractionalDigits minValue maxValue) => do
        let classes := [← boundClass? maxValue minFractionalDigits maxFractionalDigits,
          ← boundClass? minValue minFractionalDigits maxFractionalDigits].filterMap id
        pure (notifications ++ classes.eraseDups.map (notification path))
    | _ => pure notifications

/-- Check 6: type definitions first, in the walk's order, then each element's empty identifier and empty name followed
by the class its kind adds. A rule's missing error code and an Enumeration's duplicated values belong to
other owners. Emptiness is `isEmpty`, so a one-space name draws nothing, while the converter states its own
sentence for every blank name; a group's index field is judged alike, a blank spelling that is not empty
drawing no class here (peer KF653). The order of one element's classes is unmeasured. -/
def emptinessNotifications (model : ConsistencyModel) : List ModelConsistencyNotification :=
  (orderedTypeDefinitions model).flatMap (fun definition =>
    raiseIf definition.id.isEmpty (typeDefinitionPath definition) .idEmpty ++
      raiseIf definition.name.isEmpty (typeDefinitionPath definition) .typeDefinitionNameEmpty) ++
    model.entries.flatMap fun (path, element) =>
      raiseIf element.id.isEmpty path .idEmpty ++ raiseIf element.name.isEmpty path .elementNameEmpty ++
        match element with
        | .field { declared := .typeDefinition "", .. } => [notification path .typeDefinitionReferenceEmpty]
        | .group _ _ _ _ indexFieldName .. => raiseIf (indexFieldName == some "") path .indexFieldNameEmpty
        | .rule _ _ errorCondition errorEntityRelPath =>
            raiseIf errorCondition.isEmpty path .errorConditionEmpty ++
              raiseIf errorEntityRelPath.isEmpty path .errorEntityEmpty
        | .computation _ _ computedFieldRelPath operations =>
            raiseIf computedFieldRelPath.isEmpty path .computedFieldEmpty ++
              raiseIf (operations.any (·.isEmpty)) path .computationOperationEmpty
        | _ => []

/-- The header's model-level classes: `MVK_SUPP_LANGUAGES_MISSING` for no declared locale, and one
`MVK_SUPP_LANGUAGES_DUPLICATE` for each language tag two distinct declared locales share, in the order the
tags first occur. They stand ahead of the content's notifications; no capture orders them against another
class ([header locale codes](../../docs/sources/model-structure-and-declaration-probes.md#src-header-locale-codes)). -/
def supportedLanguageNotifications (model : ConsistencyModel) : List ModelConsistencyNotification :=
  if model.declaredLocales.isEmpty then [{ path := [], kind := .supportedLanguagesMissing }] else
  let tags := model.declaredLocales.map (·.languageTag)
  (tags.eraseDups.filter fun tag => tags.count tag > 1).map fun _ =>
    { path := [], kind := .supportedLanguagesDuplicate }

/-- The Kernel's consistency check of a read model. An error means the model reaches a case the
captures do not measure: attachment rule texts under another condition language, a bound outside
the normal double range, or a criterion's error text that fails a message-text gate other than the dollar
count. -/
def check (model : ConsistencyModel) : Except String ModelConsistencyOutcome :=
  match firstBuildFailure? model with
  | some (path, failure) => pure (.notBuilt path failure)
  | none => do
      let attachment ← attachmentGroupNotifications model
      let uniqueness ← uniquenessCriterionNotifications model
      let boundFormal ← boundFormalNotifications model
      pure (.checked (supportedLanguageNotifications model ++ idUniquenessNotifications model ++
        attachment ++ multiSelectGroupNotifications model ++ uniqueness ++ boundFormal ++
        emptinessNotifications model))

end ModelConsistency

end A12Kernel
