import Lean.Data.Json
import A12Kernel.Elaboration.ElementNameNotification
import A12Kernel.Elaboration.FieldTypeDeclarationNotification
import A12Kernel.Elaboration.StringContext
import A12Kernel.Reference.Dm.Model

/-! # Reading a DM-JSON model for the declaration notifications

The Kernel's consistency check judges every element the variant filter keeps, so this reader walks every
root group and nested group in document order and judges each element: a field's name and its type body
after its type definition is resolved per referencing field (a definition no field references draws
nothing, and one that two fields reference draws its notifications at both), a group's name,
repeatability, sort fields and row-key nominations, a rule's or computation's name and error code, and
the supplementary scalars of an element's annotations. It reads only the members those laws consume, keeps
integer members raw so a refused one stays visible, and binds every boolean member as the Kernel
does (`booleanMember?`).

The names above an element decide what it may report: a path class on a group or field name hands the
group-path codeless notification to everything below it and withholds the path class, the `xml` group
class and the field messages there, and a field carrying a path class of its own reports no type body.
The result is a list of `(label, element path)` pairs. A model the Kernel cannot build, by an empty
element name, a blank rule or computation name, a repeated hint-list locale, an Enumeration declaring
no values or a row-key nomination that binds to no field, yields the one unbuilt-model label and no path. The report is a multiset, so the walk order is not an observation.

It is an input adapter, differentially tested by the field-declaration capture rather than proved. A
condition language other than the two whose tokens are measured, a member of the wrong shape, an
unresolvable type definition, a repeatability past a signed 32-bit count (which the Kernel does not
read) and a row-key nomination in a model the flat validation refuses are read errors, never an empty
report. A row-key nomination that binds to no declared field is not an error: the Kernel builds no
model, so it yields the unbuilt-model label.
-/

namespace A12Kernel.Dm

open Lean A12Kernel

private def optionalInt (json : Json) (key : String) : Except String (Option Int) :=
  match json.getObjVal? key with
  | .error _ | .ok .null => pure none
  | .ok value => some <$> fromJson? value

private def optionalString (json : Json) (key : String) : Except String (Option String) :=
  match json.getObjVal? key with
  | .error _ | .ok .null => pure none
  | .ok (.str value) => pure (some value)
  | .ok other => throw s!"{key} {other.compress}"

/-- The members of an array-valued key; an absent or `null` key is empty. -/
private def arrayMembers (json : Json) (key : String) : Except String (List Json) :=
  match json.getObjVal? key with
  | .error _ | .ok .null => pure []
  | .ok value => (value.getArr?).map Array.toList

/-- Locale-keyed entries, `[{locale, text}]`, as a field's messages and an Enumeration value's labels
write them. -/
def localizedTexts (json : Json) (key : String) : Except String (List (String × String)) := do
  (← arrayMembers json key).mapM fun entry => do
    pure (← entry.getObjValAs? String "locale", ← entry.getObjValAs? String "text")

private def readMessages (json : Json) : Except String (List FieldMessageEntry) := do
  pure ((← localizedTexts json "errorMessage").map fun (locale, text) => { locale, text })

private def readString (body : Json) : Except String StringTypeDeclaration := do
  pure {
    minLength := ← optionalInt body "minLength"
    maxLength := ← optionalInt body "maxLength"
    noValueValidation := ← booleanMember? body "noValueValidation"
    lineBreaksPermitted := ← booleanMember? body "lineBreaksPermitted"
    pattern := ← optionalString body "pattern"
    hintList := ← (← arrayMembers body "hintList").mapM fun entry => do
      pure { locale := ← entry.getObjValAs? String "locale"
             values := ← (← arrayMembers entry "values").mapM Json.getStr? }
    messages := ← readMessages body }

private def readNumber (body : Json) : Except String NumberTypeDeclaration := do
  let amount ← match ← optionalString body "trait" with
    | none => pure false
    | some "amount" => pure true
    | some other => throw s!"NumberType trait {other}"
  pure {
    minLength := ← optionalInt body "minLength"
    maxLength := ← optionalInt body "maxLength"
    maxIntegerDigits := ← optionalInt body "maxIntegerDigits"
    minFractionalDigits := ← optionalInt body "minFractionalDigits"
    maxFractionalDigits := ← optionalInt body "maxFractionalDigits"
    positivesOnly := ← booleanMember? body "positivesOnly"
    amount
    minValue := ← decimalMember? body "minValue"
    maxValue := ← decimalMember? body "maxValue" }

private def readEnumeration (body : Json) : Except String EnumerationTypeDeclaration := do
  -- The runtime declaration's parse decides whether the body is readable, so the two readers cannot
  -- admit different bodies; a body without `values` is the unbuilt model, which the laws report.
  if (body.getObjVal? "values").toOption.isSome then discard <| readEnumerationDeclaration body
  let sValue ← match body.getObjVal? "sValue" with
    | .error _ | .ok .null => pure none
    | .ok (.str value) => pure (some value)
    | .ok _ => throw "EnumerationType sValue must be a string"
  pure {
    values := ← (← arrayMembers body "values").mapM fun entry => do
      pure { token := ← entry.getObjValAs? String "value"
             labels := (← localizedTexts entry "label").map fun (locale, text) => { locale, text } }
    categories := ← (← arrayMembers body "categories").mapM fun category => do
      pure { name := ← category.getObjValAs? String "name"
             tokens := ((category.getObjValAs? (Array String) "values").toOption.getD #[]).toList }
    sValue
    messages := ← readMessages body }

/-- The declaration of a field whose type definition is already resolved. A type none of the laws
concerns, or no type at all, is `other`: its refusal belongs to another reader. -/
private def readDeclaration (fieldJson : Json) : Except String FieldTypeDeclaration := do
  let some fieldType := (fieldJson.getObjVal? "fieldType").toOption | pure .other
  let some typeName := (fieldType.getObjValAs? String "type").toOption | pure .other
  let body := (fieldType.getObjVal? typeName).toOption.getD (Json.mkObj [])
  -- A temporal kind without its body object is unreadable (rows `tb-time-nobody`, `tb-dt-nobody`,
  -- `tb-frag-nobody`; spec/01 §3 for Date), while a String or a Boolean without one is read.
  if ["DateType", "TimeType", "DateTimeType", "DateFragmentType"].contains typeName then
    discard <| (fieldType.getObjVal? typeName).bind Json.getObj?
  match typeName with
  | "StringType" => .string <$> readString body
  | "NumberType" => .number <$> readNumber body
  | "CustomFieldType" =>
      pure (.custom { name := ← optionalString body "name"
                      minLength := ← optionalInt body "minLength"
                      maxLength := ← optionalInt body "maxLength" })
  | "DateType" =>
      pure (.date { format := ← optionalString body "format"
                    partialMode := ← partialMode? (← optionalString body "datePrecision")
                    youngerThan1900Check := ← booleanMember? body "youngerThan1900Check" })
  | "TimeType" | "DateTimeType" => pure (.temporal { format := ← optionalString body "format" })
  | "DateFragmentType" =>
      pure (.dateFragment { format := ← optionalString body "formatOfFragment"
                            youngerThan1900Check := ← booleanMember? body "youngerThan1900Check" })
  | "DateRangeType" =>
      pure (.dateRange { format := ← optionalString body "format"
                         separator := ← optionalString body "rangeSeparator" })
  | "EnumerationType" => .enumeration <$> readEnumeration body
  | "UnspecifiedType" => pure .unspecified
  | _ => pure .other

/-- What the model's condition language fixes: the two tokens a field's own message may name and the
word a dotted field name may not end in. Only the two measured languages have them. -/
private def languageProfile : String → Except String (StringPatternMessageTokens × String)
  | "en_US" => pure ({ field := "field", fieldValue := "field.value" }, "value")
  | "de_DE" => pure ({ field := "Feld", fieldValue := "Feld.Wert" }, "Wert")
  | other => throw s!"condition language {other} is not measured"

private structure WalkEnvironment where
  variant : Option String
  definitions : List (String × Json)
  compilePattern : StringPatternCompiler
  context : FieldTypeContext
  valueWord : String
  /-- The model's root groups, which a row-key nomination binds against. -/
  roots : List Json
  shortNamesAllowed : Bool

/-- One element's reported labels, the fact that the element stops the model from being built, or the
reason this reader cannot judge the model, which is never an empty report. -/
private structure ElementReport where
  path : List String
  labels : List String := []
  unbuilt : Bool := false
  refusal : Option String := none

/-- The element's one repertoire notification stands for all its texts, so the labels collapse to one. -/
private def collapseRepertoire (labels : List String) : List String :=
  let repertoire := ElementNameKind.supplementaryCharacter.label
  labels.filter (· != repertoire) ++ (if labels.contains repertoire then [repertoire] else [])

private def hasSupplementaryText (json : Json) (keys : List String) : Bool :=
  keys.any fun key => hasSupplementaryScalar ((json.getObjValAs? String key).toOption.getD "")

/-- Whether an element-level annotation, `[{name, value}]` beside the element's body, holds a
supplementary scalar in its name or value. -/
private def annotationsRepertoire (element : Json) : Except String Bool := do
  pure ((← arrayMembers element "annotations").any (hasSupplementaryText · ["name", "value"]))

private def repertoireIf (condition : Bool) : List String :=
  if condition then [ElementNameKind.supplementaryCharacter.label] else []

/-- The state a nomination binder is collected in: every field in depth-first order, the repeatable
groups numbered in the order reached, and the fields the variant filter removes. -/
private structure BindingState where
  fields : Array FlatFieldDecl := #[]
  groups : Array RepeatableGroupDecl := #[]
  dropped : Array FieldId := #[]

/-- Collect one element of the model as authored into the binder: a group keeps its repeatability, a
field becomes a String stub carrying only what the binder reads, its path, its repeatable scope and
whether it skips value validation (with the line-break permission that mode requires, so the stub is a
legal declaration whatever the field's own defects are). A field the variant filter removes stays, as
the Kernel binds a nomination against the model as authored. -/
private partial def collectBinding (environment : WalkEnvironment) (scope : List RepeatableLevel)
    (path : GroupPath) (element : Json) : StateT BindingState (Except String) Unit := do
  let kind ← StateT.lift (element.getObjValAs? String "type")
  let name := (element.getObjValAs? String "name").toOption.getD ""
  let body := (element.getObjVal? kind).toOption.getD (Json.mkObj [])
  match kind with
  | "Group" =>
      let groupPath := path ++ [name]
      let repeatability ← StateT.lift (optionalInt body "repeatability")
      let scope ← match repeatability with
        | some declared =>
            if 1 < declared then do
              let level := (← get).groups.size + 1
              modify fun state => { state with
                groups := state.groups.push { level, path := groupPath, repeatability := some declared.toNat } }
              pure (scope ++ [level])
            else pure scope
        | none => pure scope
      for child in ← StateT.lift (arrayMembers body "elements") do
        collectBinding environment scope groupPath child
  | "Field" =>
      let kept ← StateT.lift (acceptedByVariant environment.variant body)
      let skipsValidation ← StateT.lift (if !kept then pure false else do
        match ← readDeclaration (← resolveTypeDefinition environment.definitions body) with
        | .string declaration => pure declaration.noValueValidation
        | _ => pure false)
      let id := (← get).fields.size
      modify fun state => { state with
        fields := state.fields.push {
          id, groupPath := path, name, policy := { kind := .string }, repeatableScope := scope
          stringValueMode := if skipsValidation then .raw else .evaluated
          stringPolicy := { lineBreaksPermitted := true } }
        dropped := if kept then state.dropped else state.dropped.push id }
  | _ => pure ()

/-- The model as the nomination binder reads it, with the ids of the fields the variant filter removes. -/
private def bindingModel (environment : WalkEnvironment) : Except String (FlatModel × List FieldId) := do
  let ((), state) ← (environment.roots.forM (collectBinding environment [] [])).run {}
  pure ({ fields := state.fields.toList, repeatableGroups := state.groups.toList
          fieldRefByShortNameAllowed := environment.shortNamesAllowed }, state.dropped.toList)

/-- A group's row-key refusals as reports. Each nomination is judged by the declaration owner,
`FlatModel.nominatedTarget`: written as a name or a path, it must bind to a declared field, else the
Kernel builds no model and reports no class, and it is then judged on the group's own direct child of
its last segment's name. A disqualified field carries its refusal itself, the list-level classes and the
unresolved ones the group; the owner's list-level classes are asked of the same names made neutral. A
nomination in a model the flat validation refuses is not judged, as in the model reader, and refuses
the report. -/
private def rowKeyReports (environment : WalkEnvironment) (path : List String) (body : Json) :
    Except String (List ElementReport) := do
  let index := (body.getObjValAs? String "indexFieldName").toOption
  let sorts ← (← arrayMembers body "sortFields").mapM fun entry => entry.getObjValAs? String "name"
  let nominations := (index.toList.map (RowFieldRole.indexField, ·)) ++ sorts.map (RowFieldRole.sortField, ·)
  if nominations.isEmpty then return []
  let (model, dropped) ← bindingModel environment
  let mut judged : List (RowFieldRole × String × NominatedTarget) := []
  for (role, nomination) in nominations do
    match model.nominatedTarget dropped path (nominationPath nomination) with
    | .ok target => judged := judged ++ [(role, nomination, target)]
    | .error (.unbound _) => return [{ path, unbuilt := true }]
    | .error (.invalidModel cause) =>
        let reason := s!"nomination {nomination} is not judged on a model the flat validation refuses: {repr cause}"
        return [{ path, refusal := some reason }]
  let distinct := judged.foldl (init := ([] : List (RowFieldRole × String × NominatedTarget)))
    fun kept entry => if kept.any (fun k => k.1 == entry.1 && k.2.1 == entry.2.1) then kept
      else kept ++ [entry]
  let perName := distinct.filterMap fun (role, nomination, target) =>
    (rowFieldRefusal role target).map fun refusal =>
      match refusal with
      | .valueValidationOff _ => (path ++ [(nominationPath nomination).field], refusal.label)
      | _ => (path, refusal.label)
  let neutral : RowFieldDeclarations :=
    { sort := sorts.map fun name => (name, NominatedTarget.field false false) }
  pure ((perName ++ (rowFieldDeclarationRefusals neutral).map fun refusal => (path, refusal.label)).map
    fun (at_, label) => { path := at_, labels := [label] })

/-- Judge each element in document order below the groups above it. A field the variant filter removes
draws nothing, its name and annotations included. -/
private partial def judgeElement (environment : WalkEnvironment) (above : PathAbove)
    (parent : List String) (element : Json) : Except String (List ElementReport) := do
  let kind ← element.getObjValAs? String "type"
  let name := (element.getObjValAs? String "name").toOption.getD ""
  let body := (element.getObjVal? kind).toOption.getD (Json.mkObj [])
  let path := parent ++ [name]
  let annotated ← annotationsRepertoire element
  match kind with
  | "Group" =>
      if name.isEmpty then return [{ path, unbuilt := true }]
      let isRoot := parent.isEmpty
      let judgement := groupName isRoot name
      let repeatability ← intMember? body "repeatability"
      if repeatability.any (2147483647 < ·) then
        throw s!"group {name} declares a repeatability the Kernel does not read"
      let children ← arrayMembers body "elements"
      let sorts ← arrayMembers body "sortFields"
      let own := (judgement.reported above ++ groupDeclarationKinds isRoot repeatability sorts.length).map
        (·.label)
      let rowKeys ← rowKeyReports environment path body
      let below ← children.mapM (judgeElement environment (judgement.below above) path)
      pure ({ path, labels := collapseRepertoire (own ++ repertoireIf annotated) } :: rowKeys ++
        below.flatten)
  | "Field" =>
      if name.isEmpty then return [{ path, unbuilt := true }]
      if !(← acceptedByVariant environment.variant body) then return []
      let judgement := fieldName environment.valueWord name
      let named := (judgement.reported above).map (·.label)
      let reachable := !(judgement.pathClass || above.pathClass)
      let ownPathReported := judgement.pathClass && !above.pathClass
      if ownPathReported then
        return [{ path, labels := collapseRepertoire (named ++ repertoireIf annotated) }]
      let declaration ← readDeclaration (← resolveTypeDefinition environment.definitions body)
      match declaration.judge environment.compilePattern
          { environment.context with messagesReached := reachable } with
      | .modelNotBuilt => pure [{ path, unbuilt := true }]
      | .notifications raised =>
          let labels := named ++ raised.map (·.label) ++ repertoireIf annotated
          pure [{ path, labels := collapseRepertoire labels }]
  | "Rule" | "Computation" =>
      if ExecutableDeclaration.blank name then return [{ path, unbuilt := true }]
      if !(← acceptedByVariant environment.variant body) then return []
      let declaration : ExecutableDeclaration :=
        { group := parent, name, kind := if kind == "Rule" then .rule (ruleCode body) else .computation }
      if let .rule .unreadable := declaration.kind then throw s!"rule {name} has an unreadable errorCode"
      let labels := declaration.notifications.filterMap (·.kind.label?) ++
        above.forRule.map (·.label) ++ repertoireIf annotated
      pure [{ path, labels := collapseRepertoire labels }]
  | _ => pure []

/-- The notifications every kept element's declaration raises, each as its capture label and the
element path, or the one unbuilt-model label with an empty path: field types and bodies, element and
group names, group declarations, rule and computation names, and the repertoire of element annotations
and field messages. The Java pattern compilation is the host's and has no default: the closed ASCII
profiles of `builtinStringPatternCompiler` refuse Java-valid sources they cannot execute, which this
check would report as invalid patterns. -/
def fieldTypeDeclarationNotifications (json : Json) (compilePattern : StringPatternCompiler)
    (variant : Option String := none)
    (charset : LegalCharset := .defaultBmp) : Except String (List (String × String)) := do
  let header := (json.getObjVal? "header").toOption.getD (Json.mkObj [])
  let content ← json.getObjVal? "content"
  let language := ((content.getObjVal? "modelConfig").toOption.bind fun config =>
    (config.getObjVal? "conditionLanguage").toOption.bind fun language =>
      (language.getObjValAs? String "code").toOption).getD "en_US"
  let (messageTokens, valueWord) ← languageProfile language
  let roots ← match content.getObjVal? "modelRoot" with
    | .error _ | .ok .null => pure []
    | .ok root => arrayMembers root "rootGroups"
  let environment : WalkEnvironment := {
    variant
    definitions := (← arrayMembers content "typeDefinitions").map fun definition =>
      ((definition.getObjValAs? String "id").toOption.getD "", definition)
    compilePattern
    context := {
      declaredLocales := (← arrayMembers header "locales").filterMap fun locale =>
        (locale.getObjValAs? String "code").toOption
      messageTokens
      charset }
    valueWord
    roots
    shortNamesAllowed := ← booleanMember? ((content.getObjVal? "modelConfig").toOption.getD (Json.mkObj []))
      "fieldRefByShortNameAllowed" }
  let reports := (← roots.mapM (judgeElement environment {} [])).flatten
  if reports.any (·.unbuilt) then
    pure [(modelNotBuiltLabel, "")]
  else if let some reason := reports.findSome? (·.refusal) then
    throw reason
  else
    pure (reports.flatMap fun report =>
      report.labels.map fun label => (label, "/" ++ "/".intercalate report.path))

/-! ## Locks on the member coercions this reader depends on -/

private def member (value : Json) : Json := Json.mkObj [("k", value)]

/- A bound written as text reads as a decimal with an optional sign, point and exponent, surrounding
   spaces trimmed (`sb-str-plus`, `sb-str-exp`, `sb-str-space`); a bare or trailing point is this
   account's reading of that grammar, unmeasured. Text with no digits, a digit separator, a second point,
   a letter or an exponent past this reader's range stays refused (`sb-str-abc`). -/
example :
    (decimalMember? (member (.str "1.5")) "k").toOption = some (some (3 / 2)) ∧
    (decimalMember? (member (.str "-2")) "k").toOption = some (some (-2)) ∧
    (decimalMember? (member (.str "007.50")) "k").toOption = some (some (15 / 2)) ∧
    (decimalMember? (member (.str "+5")) "k").toOption = some (some 5) ∧
    (decimalMember? (member (.str "1e3")) "k").toOption = some (some 1000) ∧
    (decimalMember? (member (.str "25E-1")) "k").toOption = some (some (5 / 2)) ∧
    (decimalMember? (member (.str " 5")) "k").toOption = some (some 5) ∧
    (decimalMember? (member (.str ".5")) "k").toOption = some (some (1 / 2)) ∧
    ["", "-", "1_0", "1.2.3", "abc", "1e", "e3", "1e401"].all
      (fun text => (decimalMember? (member (.str text)) "k").toOption.isNone) = true := by
  native_decide

/- A boolean member binds: a JSON number written without a fraction is true unless zero, `null` and
   absence are false, and a fraction, another text or another shape is unreadable (`fc-*`). The text
   law is locked in [the binding locks](MemberBindingLocks.lean). -/
example :
    (booleanMember? (member (.bool true)) "k").toOption = some true ∧
    (booleanMember? (member (.num 1)) "k").toOption = some true ∧
    (booleanMember? (member (.num 0)) "k").toOption = some false ∧
    (booleanMember? (member (.str "true")) "k").toOption = some true ∧
    (booleanMember? (member (.str "false")) "k").toOption = some false ∧
    (booleanMember? (member .null) "k").toOption = some false ∧
    (booleanMember? (Json.mkObj []) "k").toOption = some false ∧
    (booleanMember? (member (.num (-1))) "k").toOption = some true ∧
    (booleanMember? (member (.str "TRUE")) "k").toOption = some true ∧
    (booleanMember? (member (.num { mantissa := 5, exponent := 1 })) "k").toOption = none ∧
    (booleanMember? (member (.str "yes")) "k").toOption = none ∧
    (booleanMember? (member (.arr #[])) "k").toOption = none := by
  native_decide

/-! ## Locks on the row-key nominations -/

/-- A String field declaration; `skipsValidation` is the no-value-validation flag with the line-break
permission it requires, so the field draws no type class of its own. -/
private def fieldElement (name : String) (skipsValidation : Bool := false) : String :=
  "{\"type\":\"Field\",\"id\":\"" ++ name ++ "\",\"name\":\"" ++ name ++
    "\",\"Field\":{\"fieldType\":{\"type\":\"StringType\"" ++
    (if skipsValidation then ",\"StringType\":{\"noValueValidation\":true,\"lineBreaksPermitted\":true}"
      else "") ++ "}}}"

/-- A group declaration with its sort-field nominations, as the file writes them. -/
private def groupElement (name : String) (repeatability : Nat) (sorts : List String)
    (elements : List String) : String :=
  "{\"type\":\"Group\",\"id\":\"" ++ name ++ "\",\"name\":\"" ++ name ++ "\",\"Group\":{\"repeatability\":" ++
    toString repeatability ++ ",\"sortFields\":[" ++
    ",".intercalate (sorts.map fun sort => "{\"name\":\"" ++ sort ++ "\"}") ++ "],\"elements\":[" ++
    ",".intercalate elements ++ "]}}"

/-- A model with one root group `Form`, the short-name reference flag as given. -/
private def nominationModel (shortNames : Bool) (elements : List String) : Json :=
  (Json.parse ("{\"header\":{\"locales\":[{\"code\":\"en_US\"}]},\"content\":{\"modelConfig\":" ++
    "{\"fieldRefByShortNameAllowed\":" ++ (if shortNames then "true" else "false") ++
    "},\"modelRoot\":{\"rootGroups\":[" ++ groupElement "Form" 1 [] elements ++ "]}}}")).toOption.getD .null

private def reported (model : Json) : Option (List (String × String)) :=
  (fieldTypeDeclarationNotifications model fun _ => .compiled fun _ => true).toOption

/- A nomination written as a path binds against the model as authored but is judged on the group's own
   direct child of the last segment's name: `../Key` binds to the parent's field while the local `Key`
   decides, and a local namesake that does not skip value validation leaves it admitted whatever the
   parent's does ([inbound](../../../docs/sources/inbound-handbacks.md#inbound-2026-09-27a-index-and-sort-lookup)). -/
example :
    reported (nominationModel false [fieldElement "Key",
      groupElement "Rows" 3 ["../Key"] [fieldElement "Key" (skipsValidation := true)]]) =
      some [("MVK_SORT_FIELD_NO_VALUE_VALIDATION", "/Form/Rows/Key")] ∧
    reported (nominationModel false [fieldElement "Key" (skipsValidation := true),
      groupElement "Rows" 3 ["../Key"] [fieldElement "Key"]]) = some [] := by
  native_decide

/- A path that binds to a field the group does not itself declare leaves the nomination unresolved, and
   when the group's own child of the last segment's name is a group the class is the same at the group:
   the group arm is reached through a path binding elsewhere. A plain name equal to a group the declaring
   group declares binds to no field at all, which is the next lock's case. -/
example :
    reported (nominationModel false [fieldElement "Key",
      groupElement "Rows" 3 ["../Key"] [fieldElement "Other"]]) =
      some [("MVK_INVALID_SORT_FIELD", "/Form/Rows")] ∧
    reported (nominationModel false [fieldElement "Sub",
      groupElement "Rows" 3 ["../Sub"] [groupElement "Sub" 1 [] [fieldElement "X"]]]) =
      some [("MVK_INVALID_SORT_FIELD", "/Form/Rows")] := by
  native_decide

/- A nomination that binds to no field builds no model, so the whole model reports the one unbuilt
   label and no class, whether it is an undeclared plain name or path, or a plain name that is a group
   of the declaring group even though the short-name flag could bind a field of that name elsewhere. -/
example :
    reported (nominationModel false [groupElement "Rows" 3 ["Nope"] [fieldElement "Key"]]) =
      some [("codeless:model-not-built", "")] ∧
    reported (nominationModel false [groupElement "Rows" 3 ["../Nope"] [fieldElement "Key"]]) =
      some [("codeless:model-not-built", "")] ∧
    reported (nominationModel true [fieldElement "Sub",
      groupElement "Rows" 3 ["Sub"] [groupElement "Sub" 1 [] [fieldElement "X"]]]) =
      some [("codeless:model-not-built", "")] := by
  native_decide

/-! ## Locks on the DateRange separator default -/

private def dateRangeField (body : String) : Json :=
  (Json.parse ("{\"fieldType\":{\"type\":\"DateRangeType\",\"DateRangeType\":" ++ body ++ "}}")).toOption.getD .null

private def dateRangeSeparator (body : String) : Option String :=
  ((readFieldType 0 ["Form"] "R" [] (dateRangeField body)).toOption.bind (·.dateRangePolicy)).map (·.separator)

/- An absent range separator reads as `/`, as an explicit one does, so `yyyy-MM-dd` without one is on
   the allowlist while `dd.MM.yyyy` without one is read and left to the pair allowlist; an absent format
   is still refused (tb-range-fmtonly, tb-range-fmtonly-de, tb-range-sepnly). -/
example :
    dateRangeSeparator "{\"format\":\"yyyy-MM-dd\"}" = some "/" ∧
    dateRangeSeparator "{\"format\":\"yyyy-MM-dd\",\"rangeSeparator\":null}" = some "/" ∧
    dateRangeSeparator "{\"format\":\"dd.MM.yyyy\"}" = some "/" ∧
    dateRangeSeparator "{\"format\":\"MM\",\"rangeSeparator\":\"\"}" = some "" ∧
    dateRangeSeparator "{\"rangeSeparator\":\"/\"}" = none ∧
    dateRangeSeparator "{\"format\":\"yyyy-MM-dd\",\"rangeSeparator\":1}" = none := by
  native_decide

end A12Kernel.Dm
