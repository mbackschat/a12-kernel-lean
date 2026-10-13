import Lean.Data.Json
import A12Kernel.Elaboration.Flat.Types
import A12Kernel.Elaboration.Enumeration
import A12Kernel.Elaboration.EnumerationDeclarationNotification
import A12Kernel.Elaboration.DeclarationAdmission
import A12Kernel.Elaboration.LegalCharset
import A12Kernel.Elaboration.IndexAndSortDeclaration
import A12Kernel.Semantics.NumberBound

/-! # Reading a DM-JSON document model

A DM-JSON model is the Kernel's own model file: a tree of groups whose elements are fields, rules and
computations. This reader expands it into the `FlatModel` the elaborators take, keeping each rule's
condition and each computation's alternatives as authored text for the DSL reader.

It is an input adapter, differentially tested by the replay rather than proved. Every declaration it
cannot map, a bound it cannot read and an index naming no field included, is kept with its reason in
`DmModel.refusals` and its field left out of the model, and the replay refuses such a model whole
rather than evaluating any rule against a guess. Field ids
follow depth-first declaration order, which is the order `FlatModel.fields` requires, and repeatable
levels are numbered in the order their groups are reached.
-/

namespace A12Kernel.Dm

/-- The notification as the declaration-report captures label it: its Kernel code, or the class
name of one of the two codeless classes. -/
def _root_.A12Kernel.EnumerationDeclarationNotification.observedLabel : EnumerationDeclarationNotification → String
  | .supplementaryCharacter => "codeless:supplementary-character"
  | .repeatedValue _ => "codeless:repeated-value"
  | notification => notification.kernelCode?.getD "codeless:unclassified"


open Lean

/-- One validation rule, its condition and error entity kept as authored. -/
structure DmRule where
  /-- The group declaring the rule. -/
  group : GroupPath
  name : String
  errorEntityRelPath : String
  errorCode : String
  condition : String
  severity : String
  /-- The authored message template per locale, in declaration order. -/
  messages : List (String × String) := []
  deriving Repr, Inhabited

/-- One computation alternative: an optional precondition and the operation. -/
structure DmAlternative where
  precondition : Option String
  operation : String
  toleranceRangeOp : Option String := none
  deriving Repr, Inhabited

/-- One computation, its target and alternatives kept as authored. -/
structure DmComputation where
  group : GroupPath
  name : String
  targetRelPath : String
  commonPrecondition : Option String
  alternatives : List DmAlternative
  errorCodesToSuppress : List String
  roundingMode : String := "Exact"
  deriving Repr, Inhabited

structure DmModel where
  flat : FlatModel
  rules : List DmRule
  computations : List DmComputation
  /-- The model's condition language code, such as en_US or de_DE. -/
  conditionLanguage : String
  /-- Each declaration this reader could not map, by its path, with the reason. -/
  refusals : List (List String × String)
  /-- The notifications each refused ordinary Enumeration declaration raised under the model's supported characters, by field path in field order. A declaration raising none has no entry. -/
  enumerationNotifications : List (List String × List EnumerationDeclarationNotification) := []
  deriving Repr

def DmRule.declaration (rule : DmRule) : ExecutableDeclaration :=
  { group := rule.group, name := rule.name, kind := .rule (.text rule.errorCode) }

def DmComputation.declaration (computation : DmComputation) : ExecutableDeclaration :=
  { group := computation.group, name := computation.name, kind := .computation }

def DmModel.declarations (model : DmModel) : List ExecutableDeclaration :=
  model.rules.map (·.declaration) ++ model.computations.map (·.declaration)

private def str? (json : Json) (key : String) : Option String :=
  (json.getObjValAs? String key).toOption

private def nat? (json : Json) (key : String) : Option Nat :=
  (json.getObjValAs? Nat key).toOption

private def bool? (json : Json) (key : String) : Option Bool :=
  (json.getObjValAs? Bool key).toOption

/-- A plain decimal string: an optional minus, digits, and optionally a point with digits. Anything else,
an exponent, a plus sign or a digit separator included, is no decimal here. -/
private def plainDecimal? (text : String) : Option Rat :=
  let (negative, unsigned) := if text.startsWith "-" then (true, (text.drop 1).toString) else (false, text)
  let digits (part : String) : Bool := !part.isEmpty && part.all Char.isDigit
  let magnitude? : Option Rat := match unsigned.splitOn "." with
    | [whole] => if digits whole then some (whole.toNat! : Rat) else none
    | [whole, fraction] =>
        if digits whole && digits fraction then
          some (((whole ++ fraction).toNat! : Rat) / (10 ^ fraction.length : Nat))
        else none
    | _ => none
  magnitude?.map fun magnitude => if negative then -magnitude else magnitude

/-- A DM decimal bound, written as a JSON number or as a plain decimal string (the Kernel admitted
string-written Number bounds, capture row `mv-double`); absent is `none`, and any other value refuses
the declaration rather than dropping the bound. -/
def decimalMember? (json : Json) (key : String) : Except String (Option Rat) :=
  match json.getObjVal? key with
  | .ok (.num number) => pure (some (Rat.ofScientific number.mantissa.natAbs true number.exponent *
      (if number.mantissa < 0 then -1 else 1)))
  | .ok (.str text) => match plainDecimal? text with
    | some value => pure (some value)
    | none => throw s!"{key} {text}"
  | .ok .null | .error _ => pure none
  | .ok other => throw s!"{key} {other.compress}"

/-- A DM flag the Kernel coerces: `true`, `false`, `null` or absent, a JSON number (non-zero is true)
and the strings `"true"` and `"false"`. Any other value is unreadable. Measured on
`noValueValidation` and `lineBreaksPermitted` only (rows `nv-coerce`, `nv-coerce-zero`); every other
flag keeps its own reading. -/
def flagMember? (json : Json) (key : String) : Except String Bool :=
  match json.getObjVal? key with
  | .error _ | .ok .null => pure false
  | .ok (.bool value) => pure value
  | .ok (.num number) => pure (number.mantissa != 0)
  | .ok (.str "true") => pure true
  | .ok (.str "false") => pure false
  | .ok other => throw s!"{key} {other.compress}"

/-- The partial precision a `datePrecision` member declares; an absent member is the full date. -/
def partialMode? : Option String → Except String TemporalPartialMode
  | none | some "FULL" => pure .full
  | some "DAY_OPTIONAL" => pure .dayOptional
  | some "MONTH_OPTIONAL" => pure .monthOptional
  | some "YEAR_OPTIONAL" => pure .yearOptional
  | some other => throw s!"datePrecision {other}"

/-- The ordinary Enumeration declaration of a DM `EnumerationType` body. The one parse behind both the field's declaration and its notification pass, so the two cannot read different declarations. -/
private def readEnumerationDeclaration (body : Json) : Except String EnumerationDeclaration := do
  let defaultStoredToken ← match (body.getObjVal? "sValue").toOption with
    | none | some .null => pure none
    | some (.str value) => pure (if value.isEmpty then none else some value)
    | some _ => throw "EnumerationType sValue must be a string"
  let entries := (← body.getObjValAs? (Array Json) "values").toList
  let values ← entries.mapM (·.getObjValAs? String "value")
  -- Copy admission compares effective display mappings (spec/09 §1); discarding labels
  -- here would turn a remapped Enumeration into an unlabelled one before that check.
  let displayFacts ← entries.mapM fun entry => do
    let stored ← entry.getObjValAs? String "value"
    let labels ← match (entry.getObjVal? "label").toOption with
      | none => pure #[]
      | some labels => labels.getArr?
    labels.toList.mapM fun label => do
      let locale ← label.getObjValAs? String "locale"
      let display ← label.getObjValAs? String "text"
      pure ({ stored, locale, display } : EnumerationDisplayFact)
  let categories ← ((body.getObjValAs? (Array Json) "categories").toOption.getD #[]).toList.mapM
    fun category => do
      let name ← category.getObjValAs? String "name"
      let tokens ← category.getObjValAs? (Array String) "values"
      pure ({ name, tokens := tokens.toList } : EnumerationCategoryDeclaration)
  pure { storedTokens := values, displayFacts := displayFacts.flatten, categories, defaultStoredToken }

/-- The notifications the Kernel raises for a field's ordinary Enumeration declaration, empty for any other field type and for a body this reader cannot parse (`readFieldType` reports that failure). -/
private def fieldEnumerationNotifications (charset : LegalCharset) (fieldJson : Json) :
    List EnumerationDeclarationNotification :=
  match fieldJson.getObjVal? "fieldType" with
  | .error _ => []
  | .ok fieldType =>
      match fieldType.getObjValAs? String "type" with
      | .ok "EnumerationType" =>
          let body := (fieldType.getObjVal? "EnumerationType").toOption.getD (Json.mkObj [])
          match readEnumerationDeclaration body with
          | .ok declaration => declaration.notifications charset
          | .error _ => []
      | _ => []

/-- The declaration of one field from its DM field type. -/
def readFieldType (id : FieldId) (groupPath : GroupPath) (name : String)
    (scope : List RepeatableLevel) (fieldJson : Json) : Except String FlatFieldDecl := do
  let fieldType ← fieldJson.getObjVal? "fieldType"
  let typeName ← fieldType.getObjValAs? String "type"
  let body := (fieldType.getObjVal? typeName).toOption.getD (Json.mkObj [])
  let base : FlatFieldDecl := { id, groupPath, name, policy := { kind := .string }, repeatableScope := scope
                                isGlobal := (bool? fieldJson "global").getD false }
  let requiredness ← match (fieldJson.getObjVal? "requirednessConfig").toOption.bind (str? · "mode") with
    | none => pure none
    | some "relativeToParent" => pure (some RequirednessMode.relativeToParent)
    | some "absoluteOrRelativeToNextRepAncestor" => pure (some .absoluteOrNearestRepeatableAncestor)
    | some other => throw s!"requiredness mode {other}"
  let base := { base with requiredness }
  match typeName with
  | "StringType" =>
      let lineBreaksPermitted ← flagMember? body "lineBreaksPermitted"
      let noValueValidation ← flagMember? body "noValueValidation"
      pure { base with
        stringPolicy := { lineBreaksPermitted
                          minLength := nat? body "minLength", maxLength := nat? body "maxLength" }
        stringPatternSource := str? body "pattern"
        stringValueMode := if noValueValidation then .raw else .evaluated }
  | "NumberType" =>
      -- An absent fractional member reads as `0` and `-1` is the no-bound sentinel (spec/04 §4): the
      -- declared pair becomes an ordinary one, except that `-1` beside a zero maximum leaves stored
      -- text's separator and fractional count unchecked. Both written `-1` is a declaration refusal.
      let fractional (key : String) : Except String Int := match body.getObjValAs? Int key with
        | .ok value => if value < -1 then throw s!"NumberType {key} {value}" else pure value
        | .error _ => pure 0
      let minimumDigits ← fractional "minFractionalDigits"
      let maximumDigits ← fractional "maxFractionalDigits"
      if minimumDigits = -1 && maximumDigits = -1 then throw "MVK_FRACT_DIGITS_MISSING"
      let minFractionalDigits := minimumDigits.toNat
      let scale := if maximumDigits = -1 then minFractionalDigits else maximumDigits.toNat
      -- The amount trait caps integer digits at `15 - scale` behind an explicit `maxIntegerDigits`,
      -- reported as the same cause (spec §4 digit table, §9 fit order), and on stored input turns a
      -- signed zero into the zero class on an unsigned, zero-forbidding field (peer kf276).
      let traitCap ← match str? body "trait" with
        | none => pure none
        | some "amount" => pure (some (15 - scale))
        | some other => throw s!"NumberType trait {other}"
      -- The runtime bound is the text generated code receives, printed from the authored bound's
      -- nearest double, not the authored decimal (spec/04 §4).
      let printedBound (key : String) : Except String (Option Rat) := do
        match ← decimalMember? body key with
        | none => pure none
        | some authored => match NumberBound.printedValue? authored minimumDigits maximumDigits with
          | some value => pure (some value)
          | none => throw s!"NumberType {key} lies outside the normal double range"
      pure { base with
        policy := { kind := .number { scale, signed := !(bool? body "positivesOnly").getD false } }
        numericTargetConstraints := {
          minFractionalDigits
          maxIntegerDigits := (nat? body "maxIntegerDigits").orElse fun _ => traitCap
          zeroAllowed := !(bool? body "zeroNotAllowed").getD false
          leadingZerosAllowed := (bool? body "leadingZerosAllowed").getD false
          amount := traitCap.isSome
          minStoredLength := nat? body "minLength", maxStoredLength := nat? body "maxLength"
          minimum := ← printedBound "minValue", maximum := ← printedBound "maxValue"
          fractionalDigitsChecked := !(minimumDigits = -1 && maximumDigits = 0) } }
  | "BooleanType" => pure { base with policy := { kind := .boolean } }
  | "ConfirmType" => pure { base with policy := { kind := .confirm } }
  | "EnumerationType" =>
      let enumeration ← readEnumerationDeclaration body
      let _ ← enumeration.validate.mapError (fun error => s!"EnumerationType {repr error}")
      pure { base with
        policy := { kind := .enumeration }
        enumeration := some enumeration }
  | "DateType" | "TimeType" | "DateTimeType" | "DateFragmentType" =>
      let body ← fieldType.getObjVal? typeName
      let _ ← body.getObj?
      let format ← if typeName == "DateFragmentType" then
          body.getObjValAs? String "formatOfFragment"
        else match body.getObjVal? "format" with
          | .ok value => value.getStr?
          | .error _ => pure (match typeName with
            | "TimeType" => "HH:mm:ss"
            | "DateTimeType" => "yyyy-MM-dd'T'HH:mm:ss"
            | _ => "yyyy-MM-dd")
      let kind : TemporalKind := match typeName with
        | "TimeType" => .time
        | "DateTimeType" => .dateTime
        | _ => .date
      pure { base with
        policy := { kind := .temporal kind (TemporalComponents.ofFormat format) }
        temporalTargetPolicy := some {
          format, partialMode := ← partialMode? (str? body "datePrecision")
          youngerThan1900Check := (bool? body "youngerThan1900Check").getD false } }
  | "DateRangeType" =>
      let interpretationOfYear ← match str? body "interpretationOfYear" with
        | none => pure none
        | some "FROM" => pure (some DateRangeYearInterpretation.anchorStart)
        | some "TO" => pure (some .anchorFinish)
        | some other => throw s!"interpretationOfYear {other}"
      let format ← body.getObjValAs? String "format"
      let separator ← body.getObjValAs? String "rangeSeparator"
      pure { base with
        policy := { kind := .dateRange }
        dateRangePolicy := some {
          format := format
          separator := separator
          interpretationOfYear := interpretationOfYear
          youngerThan1900Check := (bool? body "youngerThan1900Check").getD false } }
  | "CustomFieldType" =>
      let customName ← body.getObjValAs? String "name"
      pure { base with customType := some {
        name := customName, minLength := nat? body "minLength", maxLength := nat? body "maxLength" } }
  | other => throw s!"field type {other}"

private structure ReadState where
  fields : Array FlatFieldDecl := #[]
  groups : Array RepeatableGroupDecl := #[]
  rules : Array DmRule := #[]
  computations : Array DmComputation := #[]
  refusals : Array (List String × String) := #[]
  declarations : Array ExecutableDeclaration := #[]
  /-- Index-field names to resolve once every field id is known, by repeatable level. -/
  indexFields : Array (RepeatableLevel × GroupPath × String) := #[]
  /-- A non-repeatable group's index-field name, resolved the same way. -/
  nonrepeatableIndexFields : Array (GroupPath × String) := #[]
  /-- The model's supported characters, read before the walk because an Enumeration declaration's notifications depend on them. -/
  legalCharset : LegalCharset := .defaultBmp
  enumerationNotifications : Array (List String × List EnumerationDeclarationNotification) := #[]
  /-- The model's inline type definitions, by id. -/
  typeDefinitions : List (String × Json) := []
  /-- The variant the model is read for; `none` is the default variant. -/
  variant : Option String := none
  /-- Each field the variant filter removes, by group, name and repeatable scope. -/
  filteredFields : Array (GroupPath × String × List RepeatableLevel) := #[]
  /-- Each group's sort nominations as written. -/
  sortNominations : Array (GroupPath × List String) := #[]

/-- KF297's optional computation members default only on absence/null; scalar coercion must
still reach closed-set admission, while containers are reader errors. -/
private def computationString? (json : Json) (key : String) : Except String (Option String) :=
  match (json.getObjVal? key).toOption with
  | none | some .null => pure none
  | some (.str value) => pure (some value)
  | some (.num value) => pure (some value.toString)
  | some (.bool value) => pure (some (if value then "true" else "false"))
  | some _ => throw s!"expected scalar computation member: {key}"

private def readAlternative (json : Json) : Except String DmAlternative := do
  pure {
    precondition := str? json "precondition"
    operation := ← json.getObjValAs? String "operation"
    toleranceRangeOp := ← computationString? json "toleranceRangeOp" }

private def ruleCode (body : Json) : DeclarationStringValue :=
  match (body.getObjVal? "errorCode").toOption with
  | none => .text ""
  | some (.str value) => .text value
  | some (.num value) => .text value.toString
  | some (.bool value) => .text (if value then "true" else "false")
  | some .null | some (.arr _) | some (.obj _) => .unreadable

/-- Whether a field, rule or computation survives the variant the model is read for. An absent or
`null` filter keeps it; `ONLY` keeps it when the variant is named and `ALL_EXCEPT` when it is not, so
at the default variant, which names nothing, the filter type alone decides. Any other filter shape
fails the whole model, as the Kernel's build does (spec/01 §3). A `variants` member that is neither
absent, `null` nor a list of names is refused too, which no measurement covers. -/
def acceptedByVariant (variant : Option String) (body : Json) : Except String Bool := do
  match body.getObjVal? "variantFilter" with
  | .error _ | .ok .null => pure true
  | .ok filter@(.obj _) =>
      let names ← match filter.getObjVal? "variants" with
        | .error _ | .ok .null => pure []
        | .ok (.arr values) => values.toList.mapM fun
            | .str name => pure name
            | other => throw s!"variantFilter variant {other.compress}"
        | .ok other => throw s!"variantFilter variants {other.compress}"
      let named := variant.any names.contains
      match filter.getObjVal? "filterType" with
      | .ok (.str "ONLY") => pure named
      | .ok (.str "ALL_EXCEPT") => pure !named
      | _ => throw s!"variantFilter {filter.compress}"
  | .ok other => throw s!"variantFilter {other.compress}"

/-- A field's body with a `TypeDefType` replaced by the inline definition it names, so every check
reads the base kind, as the Kernel's effective type does (typedef base-kind checkpoint). A definition
imported from another model is not in this one and is refused with an unknown id. -/
def resolveTypeDefinition (definitions : List (String × Json)) (fieldJson : Json) :
    Except String Json := do
  let fieldType ← fieldJson.getObjVal? "fieldType"
  if (fieldType.getObjValAs? String "type").toOption != some "TypeDefType" then return fieldJson
  let reference := (fieldType.getObjVal? "TypeDefType").toOption.getD (Json.mkObj [])
  let some id := str? reference "typeDefinitionId"
    | throw "TypeDefType without a typeDefinitionId"
  let some definition := definitions.lookup id
    | throw s!"typeDefinitionId {id} names no type definition of this model"
  let base ← definition.getObjVal? "fieldType"
  if (base.getObjValAs? String "type").toOption == some "TypeDefType" then
    throw s!"type definition {id} is itself a TypeDefType"
  pure (fieldJson.setObjVal! "fieldType" base)

/-- The field types the Kernel's model reader knows. -/
private def knownFieldTypes : List String :=
  ["StringType", "NumberType", "BooleanType", "ConfirmType", "EnumerationType", "DateType",
    "TimeType", "DateTimeType", "DateFragmentType", "DateRangeType", "CustomFieldType",
    "TypeDefType", "UnspecifiedType"]

/-- The refusal a variant-filtered field keeps, which is the Kernel's authored-model stage: an
unknown, absent or `null` field type, a temporal type without its body, a duplicated Enumeration
value and a type definition reference without its id (spec/01 §3). Every check the default variant
makes is lost with the field. -/
private def filteredFieldRefusal? (definitions : List (String × Json)) (fieldJson : Json) :
    Option String :=
  match resolveTypeDefinition definitions fieldJson with
  | .error reason => some reason
  | .ok resolved =>
      match resolved.getObjVal? "fieldType" >>= (·.getObjValAs? String "type") with
      | .error _ => some "field type absent"
      | .ok typeName =>
          let body? := (resolved.getObjVal? "fieldType").toOption.bind fun fieldType =>
            (fieldType.getObjVal? typeName).toOption
          if !knownFieldTypes.contains typeName then some s!"field type {typeName}"
          else if ["DateType", "TimeType", "DateTimeType", "DateFragmentType"].contains typeName &&
              !(body?.any fun body => (body.getObj?).isOk) then
            some s!"{typeName} without its body"
          else if typeName == "EnumerationType" then
            match readEnumerationDeclaration (body?.getD (Json.mkObj [])) with
            | .error reason => some reason
            | .ok declaration =>
                if declaration.storedTokens.Nodup then none
                else some "EnumerationType duplicated value"
          else none

/-- Walk one group element and its descendants depth-first. -/
private partial def readElement (path : GroupPath) (scope : List RepeatableLevel) (element : Json) :
    StateT ReadState (Except String) Unit := do
  let kind ← element.getObjValAs? String "type"
  let name ← element.getObjValAs? String "name"
  let body ← element.getObjVal? kind
  match kind with
  | "Group" =>
      let repeatability := (nat? body "repeatability").getD 1
      let groupPath := path ++ [name]
      let scope ← if repeatability > 1 then do
          let level := (← get).groups.size + 1
          modify fun state => { state with
            groups := state.groups.push { level, path := groupPath, repeatability := some repeatability } }
          if let some index := str? body "indexFieldName" then
            modify fun state => { state with indexFields := state.indexFields.push (level, groupPath, index) }
          pure (scope ++ [level])
        else do
          if let some index := str? body "indexFieldName" then
            modify fun state => { state with
              nonrepeatableIndexFields := state.nonrepeatableIndexFields.push (groupPath, index) }
          pure scope
      if let .ok (sorts : Array Json) := body.getObjValAs? (Array Json) "sortFields" then
        let names ← StateT.lift (sorts.toList.mapM (·.getObjValAs? String "name"))
        modify fun state => { state with sortNominations := state.sortNominations.push (groupPath, names) }
      for child in (← body.getObjValAs? (Array Json) "elements") do
        readElement groupPath scope child
  | "Field" =>
      let state ← get
      if !(← StateT.lift (acceptedByVariant state.variant body)) then
        match filteredFieldRefusal? state.typeDefinitions body with
        | some reason => modify fun state => { state with refusals := state.refusals.push (path ++ [name], reason) }
        | none => modify fun state => { state with
            filteredFields := state.filteredFields.push (path, name, scope) }
        return
      let body ← match resolveTypeDefinition state.typeDefinitions body with
        | .ok resolved => pure resolved
        | .error reason => do
            modify fun state => { state with refusals := state.refusals.push (path ++ [name], reason) }
            return
      let id := state.fields.size
      let notifications := fieldEnumerationNotifications state.legalCharset body
      if notifications.isEmpty then
        match readFieldType id path name scope body with
        | .ok declaration => modify fun state => { state with fields := state.fields.push declaration }
        | .error reason => modify fun state => { state with refusals := state.refusals.push (path ++ [name], reason) }
      else
        let codes := (notifications.map (·.observedLabel)).eraseDups
        modify fun state => { state with
          refusals := state.refusals.push
            (path ++ [name], s!"EnumerationType notifications {String.intercalate ", " codes}")
          enumerationNotifications := state.enumerationNotifications.push (path ++ [name], notifications) }
  | "Rule" =>
      if !(← StateT.lift (acceptedByVariant (← get).variant body)) then return
      let code := ruleCode body
      modify fun state => { state with
        declarations := state.declarations.push { group := path, name, kind := .rule code }
        rules := state.rules.push {
        group := path, name
        errorEntityRelPath := (str? body "errorEntityRelPath").getD ""
        errorCode := match code with | .text value => value | .unreadable => ""
        condition := (str? body "errorCondition").getD ""
        severity := (str? body "severity").getD "ERROR"
        messages := ((body.getObjValAs? (Array Json) "errorMessage").toOption.getD #[]).toList.filterMap
          fun entry => do pure (← str? entry "locale", ← str? entry "text") } }
  | "Computation" =>
      if !(← StateT.lift (acceptedByVariant (← get).variant body)) then return
      let roundingMode ← StateT.lift (computationString? body "roundingMode")
      let alternatives ← StateT.lift do
        (← body.getObjValAs? (Array Json) "computationAlternatives").toList.mapM readAlternative
      modify fun state => { state with
        declarations := state.declarations.push { group := path, name, kind := .computation }
        computations := state.computations.push {
        group := path, name, alternatives
        targetRelPath := (str? body "computedFieldRelPath").getD ""
        commonPrecondition := str? body "commonPrecondition"
        roundingMode := roundingMode.getD "Exact"
        errorCodesToSuppress := ((body.getObjValAs? (Array String) "errorCodesToSuppress").toOption.getD #[]).toList } }
  | other => modify fun state => { state with refusals := state.refusals.push (path ++ [name], s!"element {other}") }

private def readSupportedCharacters (config : Json)
    (graphemeClusters? : Option (String → List String)) : Except String LegalCharset := do
  let entries ← match config.getObjVal? "supportedCharacters" with
    | .error _ | .ok .null => pure []
    | .ok (.arr entries) => entries.toList.mapM Json.getStr?
    | .ok _ => throw "supportedCharacters is not an array"
  let clustersOf ← match graphemeClusters? with
    | some clustersOf => pure clustersOf
    | none =>
        let requiresPreparation := entries.any fun entry =>
          if !(entry.toList.all isBmpScalar) then false
          else match entry.toList with
            | [_, _] => true
            | [_, middle, _] => middle != '-'
            | _ => false
        if requiresPreparation then
          throw "supportedCharacters requires Java-compatible grapheme preparation"
        -- Spec/06 §A.2 singles, ranges, and bounded failures never consult clustering.
        -- The shape guard above ensures this callback is never invoked.
        pure (fun _ => [])
  (admitSupportedCharacters clustersOf entries).mapError
    (fun error => s!"supportedCharacters definition: {repr error}")

/-- A written index or sort nomination as a path: leading `../` steps count parents, a leading `/`
makes it absolute, and the last segment names the field. -/
private def nominationPath (nomination : String) : SurfaceFieldPath :=
  let absolute := nomination.startsWith "/"
  let segments := (nomination.splitOn "/").filter (!·.isEmpty)
  let parents := (segments.takeWhile (· == "..")).length
  let named := segments.drop parents
  { base := if absolute then .absolute else .relative parents
    groups := named.dropLast, field := named.getLast?.getD "" }

/-- The row-key refusals of every nominating group, each labelled by its Kernel code or, for the
codeless list-capacity notice, its observed label. A nomination is bound against the model as authored,
so a field the variant filter removed is bound through a stub and then judged absent, while a name
binding nowhere fails the build without a class (spec/03 §B4). -/
private def nominationRefusals (flat : FlatModel) (state : ReadState) : List (List String × String) :=
  let stubs := state.filteredFields.toList.filter (fun (group, name, _) =>
      !flat.fields.any fun field => field.groupPath == group && field.name == name) |>.zipIdx flat.fields.length
    |>.map fun ((group, name, scope), id) =>
      ({ id, groupPath := group, name, policy := { kind := .string }, repeatableScope := scope } : FlatFieldDecl)
  let binding : FlatModel := { flat with fields := flat.fields ++ stubs }
  let dropped := stubs.map (·.id)
  let indexOf (path : GroupPath) : Option String :=
    match state.groups.toList.find? (·.path == path) with
    | some group => (state.indexFields.find? (·.1 == group.level)).map (·.2.2)
    | none => (state.nonrepeatableIndexFields.find? (·.1 == path)).map (·.2)
  let paths := ((state.indexFields.toList.filterMap fun (level, _, _) =>
      (state.groups.toList.find? (·.level == level)).map (·.path)) ++
    state.nonrepeatableIndexFields.toList.map (·.1) ++ state.sortNominations.toList.map (·.1)).eraseDups
  paths.flatMap fun path =>
    let judged (written : String) : Except String NominatedTarget :=
      match binding.nominatedTarget dropped path (nominationPath written) with
      | .ok target => .ok target
      | .error (.unbound _) => .error s!"nomination {written} names no field"
      | .error (.invalidModel _) => .error s!"nomination {written} is not judged on an invalid model"
    let sorts := ((state.sortNominations.find? (·.1 == path)).map (·.2)).getD []
    let failures := ((indexOf path).toList ++ sorts).filterMap fun written =>
      match judged written with | .error reason => some (path, reason) | .ok _ => none
    if !failures.isEmpty then failures else
    let declarations : RowFieldDeclarations := {
      index := (indexOf path).bind fun written => (judged written).toOption
      sort := sorts.filterMap fun written => ((judged written).toOption.map (written, ·)) }
    (rowFieldDeclarationRefusals declarations).map fun refusal =>
      (path, refusal.kernelCode?.getD "codeless:sort-list-capacity")

/-- Read a DM-JSON model. A structural fault in the file fails the whole read; an unmappable
declaration is refused alone. -/
private def readModelCore (json : Json)
    (graphemeClusters? : Option (String → List String)) (variant : Option String) :
    Except String (DmModel × List ExecutableDeclaration) := do
  let content ← json.getObjVal? "content"
  let config := (content.getObjVal? "modelConfig").toOption.getD (Json.mkObj [])
  let info := (content.getObjVal? "modelInfo").toOption.getD (Json.mkObj [])
  let roots ← (← content.getObjVal? "modelRoot").getObjValAs? (Array Json) "rootGroups"
  let legalCharset ← readSupportedCharacters config graphemeClusters?
  let typeDefinitions ← ((content.getObjValAs? (Array Json) "typeDefinitions").toOption.getD #[]).toList.mapM
    fun definition => do pure (← definition.getObjValAs? String "id", definition)
  let ((), state) ← (roots.toList.forM (readElement [] [])).run { legalCharset, typeDefinitions, variant }
  let fieldId (group : GroupPath) (name : String) : Option FieldId :=
    (state.fields.find? fun field => field.groupPath == group && field.name == name).map (·.id)
  -- The file writes the Base Year as a string; an unreadable one fails the read rather than leave
  -- the model without the year its partial dates are supplemented by.
  let baseYear ← match info.getObjVal? "baseYear" with
    | .error _ | .ok .null => pure none
    | .ok (.str text) => match text.toInt? with
        | some year => pure (some year)
        | none => throw s!"baseYear {text} is no integer"
    | .ok other => match other.getInt? with
        | .ok year => pure (some year)
        | .error _ => throw "baseYear is no integer"
  let mut refusals := state.refusals.toList
  let groups := state.groups.toList.map fun group =>
    let index := (state.indexFields.find? (·.1 == group.level)).bind fun (_, path, nomination) =>
      fieldId path (nominationPath nomination).field
    { group with indexField := index }
  let nonrepeatableIndexFields := state.nonrepeatableIndexFields.toList.filterMap fun (path, nomination) =>
    (fieldId path (nominationPath nomination).field).map (path, ·)
  let flat : FlatModel := {
    fields := state.fields.toList
    repeatableGroups := groups
    nonrepeatableIndexFields
    legalCharset
    fieldRefByShortNameAllowed := (bool? config "fieldRefByShortNameAllowed").getD false
    baseYear
    timeZoneId := (str? config "timeZone").getD "UTC" }
  refusals := refusals ++ nominationRefusals flat state
  pure ({
    flat
    rules := state.rules.toList
    computations := state.computations.toList
    conditionLanguage := ((config.getObjVal? "conditionLanguage").toOption.bind (str? · "code")).getD "en_US"
    refusals
    enumerationNotifications := state.enumerationNotifications.toList }, state.declarations.toList)

/-- An adapter limitation is not evidence of a Kernel reader failure. Only the established
declaration checks attach the semantic phase or actual notification classes. -/
inductive ModelReadFailure where
  | input (reason : String)
  | declaration (failure : DeclarationAdmissionFailure)
  deriving Repr, BEq, DecidableEq

/-- Read a model with structured declaration admission. Other model checks remain the
responsibility of their checked carriers; success is not a complete consistency certificate.
Combined supported-character entries require a caller-supplied Java-compatible grapheme classifier;
its absence is a host-preparation failure rather than a malformed-definition verdict. -/
def readModelWithAdmission (json : Json)
    (graphemeClusters? : Option (String → List String) := none) (variant : Option String := none) :
    Except ModelReadFailure DmModel := do
  let (model, declarations) ← (readModelCore json graphemeClusters? variant).mapError .input
  (ExecutableDeclaration.admitAll declarations).mapError .declaration
  pure model

/-- Compatibility projection for replay callers. Consumers explaining a refusal use
`readModelWithAdmission` to retain its phase and codeless notifications. -/
def readModel (json : Json) (graphemeClusters? : Option (String → List String) := none)
    (variant : Option String := none) : Except String DmModel :=
  (readModelWithAdmission json graphemeClusters? variant).mapError fun
    | .input reason => reason
    | .declaration failure => s!"declaration admission: {repr failure}"

end A12Kernel.Dm
