import Lean.Data.Json
import A12Kernel.Elaboration.Flat.Types
import A12Kernel.Elaboration.Enumeration

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
  deriving Repr, Inhabited

/-- One computation alternative: an optional precondition and the operation. -/
structure DmAlternative where
  precondition : Option String
  operation : String
  deriving Repr, Inhabited

/-- One computation, its target and alternatives kept as authored. -/
structure DmComputation where
  group : GroupPath
  name : String
  targetRelPath : String
  commonPrecondition : Option String
  alternatives : List DmAlternative
  errorCodesToSuppress : List String
  deriving Repr, Inhabited

structure DmModel where
  flat : FlatModel
  rules : List DmRule
  computations : List DmComputation
  /-- The model's condition language code, such as en_US or de_DE. -/
  conditionLanguage : String
  /-- Each declaration this reader could not map, by its path, with the reason. -/
  refusals : List (List String × String)
  deriving Repr

private def str? (json : Json) (key : String) : Option String :=
  (json.getObjValAs? String key).toOption

private def nat? (json : Json) (key : String) : Option Nat :=
  (json.getObjValAs? Nat key).toOption

private def bool? (json : Json) (key : String) : Option Bool :=
  (json.getObjValAs? Bool key).toOption

/-- A DM decimal bound, written as a JSON number or an integer string; absent is `none`, and any
other value refuses the declaration rather than dropping the bound. -/
private def rat? (json : Json) (key : String) : Except String (Option Rat) :=
  match json.getObjVal? key with
  | .ok (.num number) => pure (some (Rat.ofScientific number.mantissa.natAbs true number.exponent *
      (if number.mantissa < 0 then -1 else 1)))
  | .ok (.str text) => match text.toInt? with
    | some value => pure (some value)
    | none => throw s!"{key} {text}"
  | .ok .null | .error _ => pure none
  | .ok other => throw s!"{key} {other.compress}"

private def partialMode? : Option String → Except String TemporalPartialMode
  | none | some "FULL" => pure .full
  | some "DAY_OPTIONAL" => pure .dayOptional
  | some "MONTH_OPTIONAL" => pure .monthOptional
  | some "YEAR_OPTIONAL" => pure .yearOptional
  | some other => throw s!"datePrecision {other}"

/-- The declaration of one field from its DM field type. -/
def readFieldType (id : FieldId) (groupPath : GroupPath) (name : String)
    (scope : List RepeatableLevel) (fieldJson : Json) : Except String FlatFieldDecl := do
  let fieldType ← fieldJson.getObjVal? "fieldType"
  let typeName ← fieldType.getObjValAs? String "type"
  let body := (fieldType.getObjVal? typeName).toOption.getD (Json.mkObj [])
  let base : FlatFieldDecl := { id, groupPath, name, policy := { kind := .string }, repeatableScope := scope }
  let requiredness ← match (fieldJson.getObjVal? "requirednessConfig").toOption.bind (str? · "mode") with
    | none => pure none
    | some "relativeToParent" => pure (some RequirednessMode.relativeToParent)
    | some "absoluteOrRelativeToNextRepAncestor" => pure (some .absoluteOrNearestRepeatableAncestor)
    | some other => throw s!"requiredness mode {other}"
  let base := { base with requiredness }
  match typeName with
  | "StringType" =>
      pure { base with
        stringPolicy := { lineBreaksPermitted := (bool? body "lineBreaksPermitted").getD false
                          minLength := nat? body "minLength", maxLength := nat? body "maxLength" }
        stringPatternSource := str? body "pattern"
        stringValueMode := if (bool? body "noValueValidation").getD false then .raw else .evaluated }
  | "NumberType" =>
      let scale := (nat? body "maxFractionalDigits").getD 0
      -- The amount trait's only formal effect is an integer-digit cap of `15 - scale` behind an
      -- explicit `maxIntegerDigits`, reported as the same cause (spec §4 digit table, §9 fit order).
      let traitCap ← match str? body "trait" with
        | none => pure none
        | some "amount" => pure (some (15 - scale))
        | some other => throw s!"NumberType trait {other}"
      pure { base with
        policy := { kind := .number { scale, signed := !(bool? body "positivesOnly").getD false } }
        numericTargetConstraints := {
          minFractionalDigits := (nat? body "minFractionalDigits").getD 0
          maxIntegerDigits := (nat? body "maxIntegerDigits").orElse fun _ => traitCap
          zeroAllowed := !(bool? body "zeroNotAllowed").getD false
          leadingZerosAllowed := (bool? body "leadingZerosAllowed").getD false
          minStoredLength := nat? body "minLength", maxStoredLength := nat? body "maxLength"
          minimum := ← rat? body "minValue", maximum := ← rat? body "maxValue" } }
  | "BooleanType" => pure { base with policy := { kind := .boolean } }
  | "ConfirmType" => pure { base with policy := { kind := .confirm } }
  | "EnumerationType" =>
      if (body.getObjVal? "sValue").isOk then throw "EnumerationType sValue"
      let values ← (← body.getObjValAs? (Array Json) "values").toList.mapM (·.getObjValAs? String "value")
      let categories ← ((body.getObjValAs? (Array Json) "categories").toOption.getD #[]).toList.mapM
        fun category => do
          let name ← category.getObjValAs? String "name"
          let tokens ← category.getObjValAs? (Array String) "values"
          pure ({ name, tokens := tokens.toList } : EnumerationCategoryDeclaration)
      pure { base with
        policy := { kind := .enumeration }
        enumeration := some { storedTokens := values, categories } }
  | "DateType" | "TimeType" | "DateTimeType" | "DateFragmentType" =>
      let format ← body.getObjValAs? String (if typeName == "DateFragmentType" then "formatOfFragment" else "format")
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
        dateRangePolicy := some { format, separator, interpretationOfYear } }
  | "CustomFieldType" =>
      let customName ← body.getObjValAs? String "name"
      pure { base with customType := some { name := customName } }
  | other => throw s!"field type {other}"

private structure ReadState where
  fields : Array FlatFieldDecl := #[]
  groups : Array RepeatableGroupDecl := #[]
  rules : Array DmRule := #[]
  computations : Array DmComputation := #[]
  refusals : Array (List String × String) := #[]
  /-- Index-field names to resolve once every field id is known, by repeatable level. -/
  indexFields : Array (RepeatableLevel × GroupPath × String) := #[]

private def readAlternative (json : Json) : Except String DmAlternative := do
  pure { precondition := str? json "precondition", operation := ← json.getObjValAs? String "operation" }

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
        else pure scope
      for child in (← body.getObjValAs? (Array Json) "elements") do
        readElement groupPath scope child
  | "Field" =>
      let id := (← get).fields.size
      match readFieldType id path name scope body with
      | .ok declaration => modify fun state => { state with fields := state.fields.push declaration }
      | .error reason => modify fun state => { state with refusals := state.refusals.push (path ++ [name], reason) }
  | "Rule" =>
      modify fun state => { state with rules := state.rules.push {
        group := path, name
        errorEntityRelPath := (str? body "errorEntityRelPath").getD ""
        errorCode := (str? body "errorCode").getD ""
        condition := (str? body "errorCondition").getD ""
        severity := (str? body "severity").getD "ERROR" } }
  | "Computation" =>
      let alternatives ← StateT.lift do
        (← body.getObjValAs? (Array Json) "computationAlternatives").toList.mapM readAlternative
      modify fun state => { state with computations := state.computations.push {
        group := path, name, alternatives
        targetRelPath := (str? body "computedFieldRelPath").getD ""
        commonPrecondition := str? body "commonPrecondition"
        errorCodesToSuppress := ((body.getObjValAs? (Array String) "errorCodesToSuppress").toOption.getD #[]).toList } }
  | other => modify fun state => { state with refusals := state.refusals.push (path ++ [name], s!"element {other}") }

/-- Read a DM-JSON model. A structural fault in the file fails the whole read; an unmappable
declaration is refused alone. -/
def readModel (json : Json) : Except String DmModel := do
  let content ← json.getObjVal? "content"
  let config := (content.getObjVal? "modelConfig").toOption.getD (Json.mkObj [])
  let info := (content.getObjVal? "modelInfo").toOption.getD (Json.mkObj [])
  let roots ← (← content.getObjVal? "modelRoot").getObjValAs? (Array Json) "rootGroups"
  let ((), state) ← (roots.toList.forM (readElement [] [])).run {}
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
  let mut groups := []
  for group in state.groups.toList do
    match state.indexFields.find? (·.1 == group.level) with
    | some (_, groupPath, index) =>
        -- An index naming no field of its group refuses the group's index, not the whole read.
        if (fieldId groupPath index).isNone then
          refusals := refusals ++ [(groupPath, s!"indexFieldName {index} names no field")]
        groups := groups ++ [{ group with indexField := fieldId groupPath index }]
    | none => groups := groups ++ [group]
  pure {
    flat := {
      fields := state.fields.toList
      repeatableGroups := groups
      fieldRefByShortNameAllowed := (bool? config "fieldRefByShortNameAllowed").getD false
      baseYear
      timeZoneId := (str? config "timeZone").getD "UTC" }
    rules := state.rules.toList
    computations := state.computations.toList
    conditionLanguage := ((config.getObjVal? "conditionLanguage").toOption.bind (str? · "code")).getD "en_US"
    refusals }

end A12Kernel.Dm
