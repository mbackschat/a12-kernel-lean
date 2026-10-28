import A12Kernel.Elaboration.DeclarationAdmission
import A12Kernel.Semantics.NumberBound

/-! # A12Kernel.Elaboration.ModelConsistency — the notifications a model's consistency check raises

The Kernel checks a whole model by collecting notifications, not by stopping at the first refusal, so
the multiplicity, the class and the order of each notification are observable. This module is the
collection over an already-read model, measured against kernel 30.8.1 over two retained captures
(`evidence/kernel-30.8.1/captures/model-consistency-2026-10-13/` and
`evidence/kernel-30.8.1/captures/model-consistency-bound-order-2026-10-13/`). The captures record
class labels only, so a notification's path is the model's own element path and is not an observed
quantity.

A model that cannot be built yields no notification at all: the first element, in walk order, with one
of the `ModelBuildFailure` defects stops the check. Three of those defects (an empty or absent
type-definition reference, an empty computed-field path, an Enumeration with two categories of one
name) do not stop the build when the variant filter deletes the field or computation carrying them:
the model builds and the defect is one codeless notification of check 6 instead. A deleted field's,
rule's or computation's empty name is likewise check 6's sentence and its one-space name nothing. Otherwise six checks run in this registration
order and their notifications concatenate in it, so a class is never interleaved with another check's:

1. Element identifier uniqueness, over every group, field, rule and computation; a type definition is
   outside it. The empty identifier is an ordinary identifier here.
2. Number value limits: a declared maximum or minimum whose nearest binary64 exceeds the limit the
   declared fraction digits allow (`NumberBound.exceedsLimit`), maximum first.
3. Attachment groups: the required fields, the required rules and the `content` field's String
   configuration.
4. Multi-select groups: repeatability, the single Enumeration or String field and its requiredness, and
   the absence of nested groups and computations.
5. The formal check of each printed bound (`NumberBound.printed?`), maximum first, over fields that
   survive the variant filter only.
6. Emptiness of identifiers, element names, rule conditions, rule error entities, computation operations and type
   definition names, and the lifted conversion defects of deleted declarations.

Every check except the fifth walks the authored model, fields removed by the variant filter included.
The walk visits type definitions first, then elements depth-first, a group before its children. Within
one check the notifications follow the walk.

The captures fix identifier uniqueness before emptiness and value limits before the bound check; the
remaining registration order, the raw (possibly `-1`) maximum fraction digits as the limit input, a
`content` field missing either String flag, the nested-element test regardless of the field count, and
the first child named `content` of any kind are read from the Kernel's consistency rule sources at
kernel 30.8.1, not separately measured ([checkpoint](../../docs/sources/model-structure-and-declaration-probes.md#src-model-consistency-k17)).
Two build failures in one model and the order across distinct duplicated identifiers are unmeasured;
a label-only capture cannot separate the latter. The lifted conversion defects rest on a peer
measurement of a12-dmkits `fecf8552` (`CheckerBasicSentenceAgreementTest`, `docs/sources/inbound-handbacks.md#src-inbound-2026-10-27`),
which compares sets of classes: their order against another class of the same element is unmeasured.

Not claimed: type definitions' own bodies, a bound outside the normal double range (an error, not a
class), attachment condition texts under a language the captures do not cover, the combination of
an invalid multi-select field count with nested groups, the resolution of a computed field's path, and
the admission of an empty element name for a declaration the filter deletes.
-/

namespace A12Kernel

/-- The type of a field as the consistency check reads it. -/
inductive ConsistencyFieldType where
  | number (minFractionalDigits maxFractionalDigits : Int) (minValue maxValue : Option Rat)
  | string (noValueValidation lineBreaksPermitted : Bool)
  | enumeration (categoryNames : List String)
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
  /-- Whether the field survives the variant filter. -/
  inVariant : Bool
  deriving Repr, DecidableEq

/-- One authored element. A group lists its children in authored order. -/
inductive ConsistencyElement where
  | group (id name : String) (repeatability : Nat) (usageType : Option String)
      (indexFieldName : Option String) (sortFieldNames : List String)
      (elements : List ConsistencyElement)
  | field (field : ConsistencyField)
  /-- `inVariant` is whether the rule or computation survives the variant filter, as for a field. -/
  | rule (id name errorCondition errorEntityRelPath : String) (inVariant : Bool)
  | computation (id name computedFieldRelPath : String) (operations : List String) (inVariant : Bool)

structure ConsistencyTypeDefinition where
  id : String
  name : String
  deriving Repr, DecidableEq

structure ConsistencyModel where
  typeDefinitions : List ConsistencyTypeDefinition
  rootGroups : List ConsistencyElement
  /-- The model's condition language code, which selects the attachment rules' required texts. -/
  conditionLanguage : String

/-- A notification class of the consistency check. Every class is an ERROR. -/
inductive ModelConsistencyClass where
  | idNotUnique
  | numberMaxValueExceeded
  | numberMinValueExceeded
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
  /-- An empty field, rule or computation name, the type definition's sentence on an element. Only a
  declaration the variant filter deletes reaches the check with it; a kept one leaves the model unbuilt. -/
  | elementNameEmpty
  /-- A deleted declaration's lifted build failure: a type-definition reference with an empty or absent
  id (`ModelBuildFailure.typeDefinitionReferenceEmpty`). -/
  | typeDefinitionReferenceEmpty
  /-- A deleted computation's lifted empty computed-field path
  (`ModelBuildFailure.computedFieldPathEmpty`). -/
  | computedFieldEmpty
  /-- A deleted field's lifted Enumeration with two categories of one name
  (`ModelBuildFailure.enumerationCategoryNameDuplicated`). -/
  | enumerationCategoryDuplicate
  deriving Repr, DecidableEq

namespace ModelConsistencyClass

/-- Every class once, in declaration order. -/
def all : List ModelConsistencyClass :=
  [idNotUnique, numberMaxValueExceeded, numberMinValueExceeded, attachmentMissingField,
    attachmentRequiredRules, attachmentContentConfig, multiSelectRepeatableGroup,
    multiSelectRequiredField, multiSelectRequiredFlag, multiSelectIndexField, multiSelectFieldType,
    multiSelectOtherElements, boundTotalDigitsTooLong, boundSignedZero, idEmpty, errorConditionEmpty,
    errorEntityEmpty, computationOperationEmpty, typeDefinitionNameEmpty, elementNameEmpty, typeDefinitionReferenceEmpty,
    computedFieldEmpty, enumerationCategoryDuplicate]

/-- The label the captures give the class, or for the three lifted classes the label the locks give it. None
of these classes carries a Kernel code, so each is named by its own class. -/
def observedLabel : ModelConsistencyClass → String
  | idNotUnique => "codeless:id-not-unique"
  | numberMaxValueExceeded => "codeless:number-max-value-exceeded"
  | numberMinValueExceeded => "codeless:number-min-value-exceeded"
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
  | enumerationCategoryDuplicate => "codeless:enum-category-duplicate"

end ModelConsistencyClass

/-- A defect that stops the Kernel from building the model at all. -/
inductive ModelBuildFailure where
  | elementNameEmpty
  | computedFieldPathEmpty
  | enumerationCategoryNameDuplicated
  | indexFieldNameEmpty
  | sortFieldNameEmpty
  | typeDefinitionReferenceEmpty
  deriving Repr, DecidableEq

namespace ModelBuildFailure

/-- The notification class that replaces a build failure for a declaration the variant filter deletes,
for the three failures a deleting filter is measured to lift. -/
def liftedClass? : ModelBuildFailure → Option ModelConsistencyClass
  | .typeDefinitionReferenceEmpty => some .typeDefinitionReferenceEmpty
  | .computedFieldPathEmpty => some .computedFieldEmpty
  | .enumerationCategoryNameDuplicated => some .enumerationCategoryDuplicate
  | .elementNameEmpty | .indexFieldNameEmpty | .sortFieldNameEmpty => none

end ModelBuildFailure

structure ModelConsistencyNotification where
  /-- Names from the root group to the element the class concerns; a type definition is its own name. -/
  path : List String
  kind : ModelConsistencyClass
  deriving Repr, DecidableEq

inductive ModelConsistencyOutcome where
  /-- The model cannot be built and no check ran; `path` names the first offending element. -/
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

/-- Whether the variant filter deletes the declaration; a group is never deleted. -/
def deletedByFilter : ConsistencyElement → Bool
  | field f => !f.inVariant
  | rule _ _ _ _ inVariant | computation _ _ _ _ inVariant => !inVariant
  | group .. => false

/-- The three declaration defects a deleting variant filter lifts from a build failure to a
notification, judged whether or not the declaration survives the filter. The Enumeration duplicate is judged on the declared type, so a type definition's own
categories are outside it. -/
def conversionFailure? : ConsistencyElement → Option ModelBuildFailure
  | .field f =>
      match f.declared with
      | .enumeration categoryNames =>
          if categoryNames.eraseDups.length < categoryNames.length then
            some .enumerationCategoryNameDuplicated
          else none
      | .typeDefinition "" => some .typeDefinitionReferenceEmpty
      | _ => none
  | .computation _ _ computedFieldRelPath _ _ =>
      if computedFieldRelPath.isEmpty then some .computedFieldPathEmpty else none
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

/-- The defect of one element that stops the Kernel building the model, an empty name first. A
declaration the variant filter deletes fails nothing: its empty name and the failures of
`conversionFailure?` are reported by `emptinessNotifications` instead, and its blank name by nothing.
A kept declaration's blank name fails like an empty one, measured for one space (KF626). -/
def buildFailure? : ConsistencyElement → Option ModelBuildFailure
  | element@(.group _ _ _ _ indexFieldName sortFieldNames _) =>
      if element.name.isEmpty then some .elementNameEmpty
      else if indexFieldName == some "" then some .indexFieldNameEmpty
      else if sortFieldNames.any (·.isEmpty) then some .sortFieldNameEmpty
      else none
  | element@(.field _) | element@(.rule ..) | element@(.computation ..) =>
      if element.deletedByFilter then none
      else if ExecutableDeclaration.blank element.name then some .elementNameEmpty
      else element.conversionFailure?

/-- The first build failure in walk order, with the path of the offending element. -/
def firstBuildFailure? (model : ConsistencyModel) : Option (List String × ModelBuildFailure) :=
  model.entries.findSome? fun (path, element) => (buildFailure? element).map (path, ·)

/-- Check 1. Every occurrence of an identifier shared with another element is reported. -/
def idUniquenessNotifications (model : ConsistencyModel) : List ModelConsistencyNotification :=
  let ids := model.entries.map (·.2.id)
  model.entries.flatMap fun (path, element) =>
    raiseIf (1 < ids.count element.id) path .idNotUnique

/-- Whether the declared bound, if any, exceeds the limit its declared maximum fraction digits allow.
The maximum fraction digits are the raw declared value, which may be negative. -/
private def exceeds (bound : Option Rat) (maxFractionalDigits : Int) (minimum : Bool) : Bool :=
  bound.any fun authored => NumberBound.exceedsLimit authored maxFractionalDigits minimum

/-- Check 2. A type definition's own bounds are not checked, only the fields that resolve to them. -/
def numberLimitNotifications (model : ConsistencyModel) : List ModelConsistencyNotification :=
  model.fieldEntries.flatMap fun (path, field) =>
    match field.effective with
    | some (.number _ maxFractionalDigits minValue maxValue) =>
        raiseIf (exceeds maxValue maxFractionalDigits false) path .numberMaxValueExceeded ++
          raiseIf (exceeds minValue maxFractionalDigits true) path .numberMinValueExceeded
    | _ => []

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
    | .rule _ _ errorCondition _ _ => some errorCondition
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
  | some (.enumeration _) | some (.string ..) => true
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

/-- Check 5 over the fields that survive the variant filter: the maximum's class, then the minimum's,
the second dropped when it equals the first at the same field. -/
def boundFormalNotifications (model : ConsistencyModel) :
    Except String (List ModelConsistencyNotification) :=
  model.fieldEntries.foldlM (init := []) fun notifications (path, field) =>
    match field.effective with
    | some (.number minFractionalDigits maxFractionalDigits minValue maxValue) =>
        if !field.inVariant then pure notifications else do
          let classes := [← boundClass? maxValue minFractionalDigits maxFractionalDigits,
            ← boundClass? minValue minFractionalDigits maxFractionalDigits].filterMap id
          pure (notifications ++ classes.eraseDups.map (notification path))
    | _ => pure notifications

/-- The lifted build failure of a deleted declaration, as its class. A kept declaration draws none: its
failure leaves no model before any notification is collected. -/
def liftedNotifications (path : List String) (element : ConsistencyElement) :
    List ModelConsistencyNotification :=
  match element.conversionFailure?.bind (·.liftedClass?) with
  | some kind => raiseIf element.deletedByFilter path kind
  | none => []

/-- Check 6: type definitions first, then each element's empty identifier and empty name followed by
the class its kind adds. A rule's missing error code and an Enumeration's duplicated values belong to
other owners. Emptiness is `isEmpty`, so a one-space name draws nothing (KF626). A deleted
declaration's lifted build failure follows the name; the order of one element's classes is not measured. -/
def emptinessNotifications (model : ConsistencyModel) : List ModelConsistencyNotification :=
  model.typeDefinitions.flatMap (fun definition =>
    raiseIf definition.id.isEmpty [definition.name] .idEmpty ++
      raiseIf definition.name.isEmpty [definition.name] .typeDefinitionNameEmpty) ++
    model.entries.flatMap fun (path, element) =>
      raiseIf element.id.isEmpty path .idEmpty ++ raiseIf element.name.isEmpty path .elementNameEmpty ++
        liftedNotifications path element ++
        match element with
        | .rule _ _ errorCondition errorEntityRelPath _ =>
            raiseIf errorCondition.isEmpty path .errorConditionEmpty ++
              raiseIf errorEntityRelPath.isEmpty path .errorEntityEmpty
        | .computation _ _ _ operations _ =>
            raiseIf (operations.any (·.isEmpty)) path .computationOperationEmpty
        | _ => []

/-- The Kernel's consistency check of a read model. An error means the model reaches a case the
captures do not measure: attachment rule texts under another condition language, or a bound outside
the normal double range. -/
def check (model : ConsistencyModel) : Except String ModelConsistencyOutcome :=
  match firstBuildFailure? model with
  | some (path, failure) => pure (.notBuilt path failure)
  | none => do
      let attachment ← attachmentGroupNotifications model
      let boundFormal ← boundFormalNotifications model
      pure (.checked (idUniquenessNotifications model ++ numberLimitNotifications model ++
        attachment ++ multiSelectGroupNotifications model ++ boundFormal ++
        emptinessNotifications model))

end ModelConsistency

end A12Kernel
