import Lean.Data.Json
import A12Kernel.Elaboration.ElementNameNotification
import A12Kernel.Elaboration.FieldTypeDeclarationNotification
import A12Kernel.Elaboration.StringContext
import A12Kernel.Reference.Dm.Model
import A12Kernel.Reference.Dm.ModelConversion

/-! # Reading a DM-JSON model for the declaration notifications

The Kernel's consistency check judges every element, so this reader walks every root group and nested
group of the converted model (`convertModel`) in document order and judges each element: a field's name and its type body
after its type definition is resolved per referencing field (a definition no field references draws
nothing, and one that two fields reference draws its notifications at both), a group's name,
repeatability, sort fields and row-key nominations, a rule's or computation's name and error code, a rule's possible-cause slots, and
the supplementary scalars of an element's annotations. It reads only the members those laws consume, keeps
integer members raw so a refused one stays visible, and binds every integer and boolean member as the
Kernel does (`intMember?`, `primitiveIntMember?`, `booleanMember?`), after the one pass that binds every
element and type body for all three DM readers (`bindModelMembers`).

The names above an element decide what it may report: a path class on a group or field name hands the
group-path codeless notification to everything below it and withholds the path class, the `xml` group
class and the field messages there, and a field carrying a path class of its own reports no type body.
The result is a list of `(label, element path)` pairs, headed by the converter's sentences, which the
Kernel states for each declaration it drops and which make that declaration's own defects, and the rules
beneath a dropped group, draw nothing. A model the Kernel cannot build, by a conversion that builds no
validation model, a repeated hint-list locale, an Enumeration declaring no values or an empty token with an empty label text, a repeated
type-definition id, a declared locale with no language or declared twice, a row-key nomination whose spelling
leaves no model (`NominationFailure`, a sort name written empty included), or a frame shape that costs only the check (`FrameCheckFailure`), yields the one unbuilt-model
label and no path. The report is a multiset, so the walk order is not an observation.

It is an input adapter, differentially tested by the field-declaration capture rather than proved. A
member of the wrong shape, a
localized-text member that does not bind (`bindLocalizedTextMembers`), a header locale code the parser
refuses (`headerLocales`), a
type definition that is itself a type reference, a repeatability past a signed 32-bit count (which the Kernel does not
read) and a row-key nomination in a model the flat validation refuses are read errors, never an empty
report. A row-key nomination whose spelling leaves no model is not an error: the Kernel builds no
model, so it yields the unbuilt-model label.
-/

namespace A12Kernel.Dm

open Lean A12Kernel

private def optionalString (json : Json) (key : String) : Except String (Option String) :=
  match json.getObjVal? key with
  | .error _ | .ok .null => pure none
  | .ok (.str value) => pure (some value)
  | .ok other => throw s!"{key} {other.compress}"

private def readMessages (json : Json) : Except String (List FieldMessageEntry) := do
  pure ((← localizedTextMember json "errorMessage").map fun (locale, text) => { locale, text })

private def readString (body : Json) : Except String StringTypeDeclaration := do
  pure {
    minLength := ← intMember? body "minLength"
    maxLength := ← intMember? body "maxLength"
    noValueValidation := ← booleanMember? body "noValueValidation"
    lineBreaksPermitted := ← booleanMember? body "lineBreaksPermitted"
    pattern := ← optionalString body "pattern"
    hintList := ← (← frameMembers body "hintList").mapM fun entry => do
      pure { locale := ← localeKey (← entry.getObjValAs? String "locale")
             values := ← (← frameMembers entry "values").mapM Json.getStr? }
    messages := ← readMessages body }

private def readNumber (body : Json) : Except String NumberTypeDeclaration := do
  let amount ← match ← optionalString body "trait" with
    | none => pure false
    | some "amount" => pure true
    | some other => throw s!"NumberType trait {other}"
  pure {
    minLength := ← intMember? body "minLength"
    maxLength := ← intMember? body "maxLength"
    maxIntegerDigits := ← intMember? body "maxIntegerDigits"
    minFractionalDigits := ← primitiveIntMember? body "minFractionalDigits"
    maxFractionalDigits := ← primitiveIntMember? body "maxFractionalDigits"
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
    values := ← enumerationValueEntries body
    categories := ← boundCategories body
    sValue
    messages := ← readMessages body }

/-- The declaration of a field whose type definition is already resolved. A type none of the laws
concerns, or no type at all, is `other`: its refusal belongs to another reader. -/
private def readDeclaration (fieldJson : Json) : Except String FieldTypeDeclaration := do
  let some fieldType := (fieldJson.getObjVal? "fieldType").toOption | pure .other
  let some typeName := (fieldType.getObjValAs? String "type").toOption | pure .other
  let body := (fieldType.getObjVal? typeName).toOption.getD (Json.mkObj [])
  -- A body that is missing is the empty body on every type, the four temporal kinds included (kernel
  -- 31.1.1, peer KF654; 30.8.1 refused them, rows `tb-time-nobody`, `tb-dt-nobody`, `tb-frag-nobody`). A
  -- temporal body that is present and no object stays unreadable.
  if ["DateType", "TimeType", "DateTimeType", "DateFragmentType"].contains typeName &&
      (fieldType.getObjVal? typeName).isOk then
    discard body.getObj?
  match typeName with
  | "StringType" => .string <$> readString body
  | "NumberType" => .number <$> readNumber body
  | "CustomFieldType" =>
      pure (.custom { name := ← optionalString body "name"
                      minLength := ← intMember? body "minLength"
                      maxLength := ← intMember? body "maxLength" })
  | "DateType" =>
      let format ← optionalString body "format"
      let partialMode ← partialMode? (← optionalString body "datePrecision")
      bindInertYearCheck body
      pure (.date { format, partialMode })
  | "TimeType" | "DateTimeType" => pure (.temporal { format := ← optionalString body "format" })
  | "DateFragmentType" =>
      let format ← optionalString body "formatOfFragment"
      bindInertYearCheck body
      pure (.dateFragment { format })
  | "DateRangeType" =>
      pure (.dateRange { format := ← optionalString body "format"
                         separator := ← optionalString body "rangeSeparator" })
  | "EnumerationType" => .enumeration <$> readEnumeration body
  | _ => pure .other

/-- What the model's condition language fixes: the two tokens a field's own message may name and the
word a dotted field name may not end in. Only the two measured languages have them. -/
private def languageProfile : String → Except String (StringPatternMessageTokens × String)
  | "en_US" => pure ({ field := "field", fieldValue := "field.value" }, "value")
  | "de_DE" => pure ({ field := "Feld", fieldValue := "Feld.Wert" }, "Wert")
  | other => throw s!"condition language {other} is not measured"

private structure WalkEnvironment where
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
  /-- The report holds only index and sort checks that wait on the entity walk. -/
  orderingGate : Bool := false
  /-- A field's error text failed a check the entity walk itself runs. -/
  walkRefused : Bool := false
  /-- A rule's or computation's message leaves the model unbuilt, once nothing else was reported
  (`undeclaredLocaleBuildFailure`). -/
  buildFailure : Bool := false

/-- The classes the Kernel's entity walk draws at a field's error text beside its path and count
classes: the encoding, line-break, control-character, dollar and parameter checks
(`NoMetaModelChecks.checkEntity`, source-read; the
[October 21 letter](../../../docs/sources/inbound-handbacks.md#src-inbound-2026-10-21), §2.16,
measured only a refused path and a count below one). The walk's restricted-alphabet check of
Enumeration values is drawn by `readModel`, outside this reader, so it withholds no gate here. -/
private def walkTextLabels : List String :=
  [KernelStaticDiagnostic.wrongEncoding, .invalidMessageLinebreak, .invalidMessageCharacters,
    .wrongNumberOfDollars, .invalidMessageParameter].map (·.kernelCode)

/-- The element's one repertoire notification stands for all its texts, so the labels collapse to one. -/
private def collapseRepertoire (labels : List String) : List String :=
  let repertoire := ElementNameKind.supplementaryCharacter.label
  labels.filter (· != repertoire) ++ (if labels.contains repertoire then [repertoire] else [])

private def hasSupplementaryText (json : Json) (keys : List String) : Bool :=
  keys.any fun key => hasSupplementaryScalar ((json.getObjValAs? String key).toOption.getD "")

/-- Whether an element-level annotation, `[{name, value}]` beside the element's body, holds a
supplementary scalar in its name or value. -/
private def annotationsRepertoire (element : Json) : Except String Bool := do
  pure ((← frameMembers element "annotations").any (hasSupplementaryText · ["name", "value"]))

private def repertoireIf (condition : Bool) : List String :=
  if condition then [ElementNameKind.supplementaryCharacter.label] else []

/-- The state a nomination binder is collected in: every field in depth-first order, the repeatable
groups numbered in the order reached, and the nonrepeatable groups holding no field, which a spelling may
land on as on any group. -/
private structure BindingState where
  fields : Array FlatFieldDecl := #[]
  groups : Array RepeatableGroupDecl := #[]
  emptyNonrepeatableGroups : Array GroupPath := #[]

/-- Collect one element of the model as authored into the binder: a group keeps its repeatability, a
field becomes a String stub carrying only what the binder reads, its path, its repeatable scope and
whether it skips value validation (with the line-break permission that mode requires, so the stub is a
legal declaration whatever the field's own defects are). -/
private partial def collectBinding (environment : WalkEnvironment) (scope : List RepeatableLevel)
    (path : GroupPath) (element : Json) : StateT BindingState (Except String) Unit := do
  let kind ← StateT.lift (element.getObjValAs? String "type")
  let name := elementName element
  let body ← StateT.lift (elementBody element kind)
  match kind with
  | "Group" =>
      let groupPath := path ++ [name]
      let repeatability ← StateT.lift (primitiveIntMember? body "repeatability")
      let scope ← match repeatability with
        | some declared =>
            if 1 < declared then do
              let level := (← get).groups.size + 1
              modify fun state => { state with
                groups := state.groups.push { level, path := groupPath, repeatability := some declared.toNat } }
              pure (scope ++ [level])
            else pure scope
        | none => pure scope
      let fieldsBefore := (← get).fields.size
      for child in ← StateT.lift (groupElements body) do
        collectBinding environment scope groupPath child
      if !(repeatability.any (1 < ·)) && (← get).fields.size == fieldsBefore then
        modify fun state => { state with
          emptyNonrepeatableGroups := state.emptyNonrepeatableGroups.push groupPath }
  | "Field" =>
      let skipsValidation ← StateT.lift (do
        match ← readDeclaration (← resolveTypeDefinition environment.definitions body) with
        | .string declaration => pure declaration.noValueValidation
        | _ => pure false)
      let id := (← get).fields.size
      modify fun state => { state with
        fields := state.fields.push {
          id, groupPath := path, name, policy := { kind := .string }, repeatableScope := scope
          stringValueMode := if skipsValidation then .raw else .evaluated
          stringPolicy := { lineBreaksPermitted := true } } }
  | _ => pure ()

/-- The model as the nomination binder reads it. -/
private def bindingModel (environment : WalkEnvironment) : Except String FlatModel := do
  let ((), state) ← (environment.roots.forM (collectBinding environment [] [])).run {}
  pure { fields := state.fields.toList, repeatableGroups := state.groups.toList
         emptyNonrepeatableGroups := state.emptyNonrepeatableGroups.toList
         fieldRefByShortNameAllowed := environment.shortNamesAllowed }

/-- A group's row-key refusals as reports. Each nomination is judged by the declaration owner,
`FlatModel.nominatedTarget`: its spelling is read against the group's own path, a spelling that leaves no
model reporting no class, and the group's own direct child of the short name it keeps is then judged. A
disqualified field carries its refusal itself, the list-level classes and the unresolved ones the group; the
owner's list-level classes are asked of the same names made neutral. A nomination in a model the flat
validation refuses is not judged, as in the model reader, and refuses the report. -/
private def rowKeyReports (environment : WalkEnvironment) (path : List String) (body : Json) :
    Except String (List ElementReport) := do
  let index ← frameText body "indexFieldName"
  let sorts ← (← frameMembers body "sortFields").mapM fun entry => do pure ((← frameText entry "name").getD "")
  let nominations := (index.toList.map (RowFieldRole.indexField, ·)) ++ sorts.map (RowFieldRole.sortField, ·)
  if nominations.isEmpty then return []
  let model ← bindingModel environment
  let mut judged : List (RowFieldRole × String × NominatedTarget) := []
  for (role, nomination) in nominations do
    match model.nominatedTarget role path nomination with
    | .ok target => judged := judged ++ [(role, nomination, target)]
    | .error (.invalidModel cause) =>
        let reason := s!"nomination {nomination} is not judged on a model the flat validation refuses: {repr cause}"
        return [{ path, refusal := some reason }]
    | .error _ => return [{ path, unbuilt := true }]
  let distinct := judged.foldl (init := ([] : List (RowFieldRole × String × NominatedTarget)))
    fun kept entry => if kept.any (fun k => k.1 == entry.1 && k.2.1 == entry.2.1) then kept
      else kept ++ [entry]
  let shortName := nominationShortName path
  let perName := distinct.filterMap fun (role, nomination, target) =>
    (rowFieldRefusal role target).map fun refusal =>
      match refusal with
      | .valueValidationOff _ => (path ++ [shortName nomination], refusal)
      | _ => (path, refusal)
  -- The Kernel judges the short name trimmed, and a blank one is an unfilled entry of its metamodel that no
  -- name law judges (a12-dmkits `CheckerOrderingNameSentenceAgreementTest` at `1124b523f`).
  let sentenceRefused := fun nomination =>
    !ExecutableDeclaration.blank (shortName nomination) && fieldNameShapeRefused (javaTrim (shortName nomination))
  -- The metamodel holds the index and the first three sort entries, and only their kept short names
  -- draw the member sentence, once per group (2026-10-21 §2.16).
  let shapes := (index.toList ++ sorts.take 3).filter sentenceRefused
  let memberSentence : List String :=
    if shapes.isEmpty then []
    else [(if shapes.any (hasSupplementaryScalar ∘ shortName) then ElementNameKind.supplementaryCharacter
      else .fieldNameShape).label]
  let neutral : RowFieldDeclarations :=
    { sort := sorts.map fun name => (name, NominatedTarget.field false false)
      refusedNames := sorts.filter sentenceRefused }
  pure ((perName ++ (rowFieldDeclarationRefusals neutral).map (path, ·)).map
      (fun (at_, refusal) => { path := at_, labels := [refusal.label], orderingGate := refusal.isOrderingGate }) ++
    if memberSentence.isEmpty then [] else [{ path, labels := memberSentence }])

/-- Judge each element in document order below the groups above it. -/
private partial def judgeElement (environment : WalkEnvironment) (above : PathAbove)
    (parent : List String) (element : Json) : Except String (List ElementReport) := do
  let kind ← element.getObjValAs? String "type"
  let name := elementName element
  let body ← elementBody element kind
  let path := parent ++ [name]
  let annotated ← annotationsRepertoire element
  match kind with
  | "Group" =>
      let isRoot := parent.isEmpty
      let judgement := groupName isRoot name
      let repeatability ← primitiveIntMember? body "repeatability"
      if repeatability.any (2147483647 < ·) then
        throw s!"group {name} declares a repeatability the Kernel does not read"
      let children ← groupElements body
      let sorts ← frameMembers body "sortFields"
      let counted := groupCountKinds repeatability
      let own := ((judgement.reported above ++ groupDeclarationKinds isRoot repeatability sorts.length ++
          (if above.countInvalid then [ElementNameKind.maxValuesInvalid] else []) ++ counted).eraseDups).map (·.label)
      let rowKeys ← rowKeyReports environment path body
      let below ← children.mapM (judgeElement environment
        { judgement.below above with countInvalid := above.countInvalid || !counted.isEmpty } path)
      pure ({ path, labels := collapseRepertoire (own ++ repertoireIf annotated) } :: rowKeys ++
        below.flatten)
  | "Field" =>
      let judgement := fieldName environment.valueWord name
      let named := (judgement.reported above ++
        if above.countInvalid then [ElementNameKind.maxValuesInvalid] else []).map (·.label)
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
          let walkRefused := raised.any fun notification => walkTextLabels.contains notification.label
          pure [{ path, labels := collapseRepertoire labels, walkRefused }]
  | "Rule" | "Computation" =>
      let declaration : ExecutableDeclaration :=
        { group := parent, name, kind := ← (if kind == "Rule" then pure (.rule (ruleCode body))
          else .computation <$> computationString? body "errorCode") }
      if let .rule .unreadable := declaration.kind then throw s!"rule {name} has an unreadable errorCode"
      -- The metamodel judges a rule's possible-cause slots whatever its condition and the model checks
      -- report (a12-dmkits KF682); a computation carries no filter.
      let slotLabels := ((← readPossibleCauseFilter parent.length body).map
        customErrorEntityListRefusals).getD [] |>.map (·.label)
      let labels := declaration.notifications.filterMap (·.kind.label?) ++
        above.forRule.map (·.label) ++ slotLabels ++ repertoireIf annotated
      let messages := (localizedTextMember body "errorMessage").toOption.getD []
      let buildFailure := undeclaredLocaleBuildFailure environment.context.declaredLocales messages
      pure [{ path, labels := collapseRepertoire labels, buildFailure }]
  | _ => pure []

/-- The notifications every element's declaration raises, each as its capture label and the
element path, or the one unbuilt-model label with an empty path: the converter's sentences, field types and
bodies, element and group names, group declarations, rule and computation names, and the repertoire of
element annotations and field messages. The Java pattern compilation is the host's and has no default: the closed ASCII
profiles of `builtinStringPatternCompiler` refuse Java-valid sources they cannot execute, which this
check would report as invalid patterns. -/
def fieldTypeDeclarationNotifications (json : Json) (compilePattern : StringPatternCompiler)
    (charset : LegalCharset := .defaultBmp) : Except String (List (String × String)) := do
  let frame ← bindModelFrame json
  let content := frame.content
  bindLocalizedTextMembers content
  bindModelMembers frame
  let locales ← headerLocales json
  let (messageTokens, valueWord) ← languageProfile (frame.conditionLanguage.getD "en_US")
  let converted := convertModel frame
  let roots := converted.roots.toList
  let environment : WalkEnvironment := {
    definitions := frame.typeDefinitions.toList.map fun definition =>
      ((definition.getObjValAs? String "id").toOption.getD "", definition)
    compilePattern
    context := {
      declaredLocales := locales.map (·.key)
      messageTokens
      charset }
    valueWord
    roots
    shortNamesAllowed := ← booleanMember? frame.config "fieldRefByShortNameAllowed" }
  let walked := (← roots.mapM (judgeElement environment {} [])).flatten
  -- A check-only frame shape, a failing declared locale or a repeated type-definition id leaves no
  -- class, after the walk's read errors, since the Kernel reads a model before it builds or checks one
  -- (spec/01 §1.2; header locale codes checkpoint, peers KF647 and KF650).
  if frame.checkFailure?.isSome || (declaredLocaleFailure? locales).isSome ||
      (jdkTaggedLabel? frame.content).isSome || converted.unbuilt ||
      (ModelConsistency.repeatedTypeDefinitionId? (environment.definitions.map (·.1))).isSome then
    return [(modelNotBuiltLabel, "")]
  -- The index and sort checks run only after an entity walk that refused nothing (2026-10-21 §2.16).
  let walkRefused := walked.any fun report => report.walkRefused || report.labels.any fun label =>
    [ElementNameKind.pathInvalid, .pathsInconsistent, .maxValuesInvalid].any (·.label == label)
  let reports := if walkRefused then walked.filter (!·.orderingGate) else walked
  if reports.any (·.unbuilt) then
    pure [(modelNotBuiltLabel, "")]
  else if let some reason := reports.findSome? (·.refusal) then
    throw reason
  else
    let reported := converted.sentences.map (fun (sentence, path) => (sentence.label, "/" ++ "/".intercalate path)) ++
      reports.flatMap fun report => report.labels.map fun label => (label, "/" ++ "/".intercalate report.path)
    -- Code generation runs only on a model the check passed, so a message it refuses leaves the model unbuilt
    -- only beside no reported class (a12-dmkits `ErrorTextLocaleScopeLawsTest` at `1124b523f`, KF659).
    pure (if reported.isEmpty && reports.any (·.buildFailure) then [(modelNotBuiltLabel, "")] else reported)

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

/- A boolean member binds: a JSON number written without a fraction is true unless zero, absence is
   false, and `null`, a fraction, another text or another shape is unreadable (`fc-*`; kernel 31.1.1's
   Jackson 3 refuses a `null` for a primitive, where 30.8.1 read it as false, a12-dmkits
   `BooleanMemberBindingDiffTest` at `1124b523f`). The text law is locked in
   [the binding locks](MemberBindingLocks.lean). -/
example :
    (booleanMember? (member (.bool true)) "k").toOption = some true ∧
    (booleanMember? (member (.num 1)) "k").toOption = some true ∧
    (booleanMember? (member (.num 0)) "k").toOption = some false ∧
    (booleanMember? (member (.str "true")) "k").toOption = some true ∧
    (booleanMember? (member (.str "false")) "k").toOption = some false ∧
    (booleanMember? (member .null) "k").toOption = none ∧
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
    ",".intercalate (sorts.map fun sort => "{\"name\":\"" ++ sort ++ "\",\"order\":\"ASC\"}") ++ "],\"elements\":[" ++
    ",".intercalate elements ++ "]}}"

/-- A model with one root group `Form`, the short-name reference flag as given. -/
private def nominationModel (shortNames : Bool) (elements : List String) : Json :=
  (Json.parse ("{\"header\":{\"id\":\"Nominations\",\"modelVersion\":\"28.4.0\",\"locales\":[{\"code\":\"en_US\"}]}," ++
    "\"content\":{\"modelInfo\":{\"name\":\"Form\"},\"modelConfig\":" ++
    "{\"fieldRefByShortNameAllowed\":" ++ (if shortNames then "true" else "false") ++
    "},\"modelRoot\":{\"rootGroups\":[" ++ groupElement "Form" 1 [] elements ++ "]}}}")).toOption.getD .null

private def reported (model : Json) : Option (List (String × String)) :=
  (fieldTypeDeclarationNotifications model fun _ => .compiled fun _ => true).toOption

/- A nomination written as a path is judged on the group's own direct child of its last segment's name:
   `../Key` lands on the parent's field while the local `Key` decides, and a local namesake that does not skip
   value validation leaves it admitted whatever the parent's does
   ([inbound](../../../docs/sources/inbound-handbacks.md#inbound-2026-09-27a-index-and-sort-lookup)). -/
example :
    reported (nominationModel false [fieldElement "Key",
      groupElement "Rows" 3 ["../Key"] [fieldElement "Key" (skipsValidation := true)]]) =
      some [("MVK_SORT_FIELD_NO_VALUE_VALIDATION", "/Form/Rows/Key")] ∧
    reported (nominationModel false [fieldElement "Key" (skipsValidation := true),
      groupElement "Rows" 3 ["../Key"] [fieldElement "Key"]]) = some [] := by
  native_decide

/- A path whose short name is a field the group does not itself declare leaves the nomination unresolved, and
   when the group's own child of that name is a group the class is the same at the group: the group arm is
   reached through a spelling that lands elsewhere. A plain name equal to a group the declaring group
   declares lands on that group, which is the next lock's case. -/
example :
    reported (nominationModel false [fieldElement "Key",
      groupElement "Rows" 3 ["../Key"] [fieldElement "Other"]]) =
      some [("MVK_INVALID_SORT_FIELD", "/Form/Rows")] ∧
    reported (nominationModel false [fieldElement "Sub",
      groupElement "Rows" 3 ["../Sub"] [groupElement "Sub" 1 [] [fieldElement "X"]]]) =
      some [("MVK_INVALID_SORT_FIELD", "/Form/Rows")] := by
  native_decide

/- A spelling landing on nothing is only a name: the group has no direct child of it, so the model builds and
   the nomination draws the role's unresolved class, whether the spelling is a plain name or a path
   (Locked: a12-dmkits GroupIndexAndSortReferenceLawsTest at 1124b523f, kernel 31.1.1, where 30.8.1 built no
   model). A spelling landing on a group, here a plain name that is a group of the declaring group even though
   the short-name flag could bind a field of that name elsewhere, draws the same class on kernel 31.3.1, where
   31.1.1 built no model (KF680). -/
example :
    reported (nominationModel false [groupElement "Rows" 3 ["Nope"] [fieldElement "Key"]]) =
      some [("MVK_INVALID_SORT_FIELD", "/Form/Rows")] ∧
    reported (nominationModel false [groupElement "Rows" 3 ["../Nope"] [fieldElement "Key"]]) =
      some [("MVK_INVALID_SORT_FIELD", "/Form/Rows")] ∧
    reported (nominationModel true [fieldElement "Sub",
      groupElement "Rows" 3 ["Sub"] [groupElement "Sub" 1 [] [fieldElement "X"]]]) =
      some [("MVK_INVALID_SORT_FIELD", "/Form/Rows")] := by
  native_decide

/-! ## Locks on the DateRange separator default -/

private def dateRangeField (body : String) : Json :=
  (Json.parse ("{\"fieldType\":{\"type\":\"DateRangeType\",\"DateRangeType\":" ++ body ++ "}}")).toOption.getD .null

private def dateRangeSeparator (body : String) : Option String :=
  ((readFieldType 0 ["Form"] "R" [] (dateRangeField body)).toOption.bind (·.dateRangePolicy)).map (·.separator)

/- An absent or empty range separator reads as `/`, as an explicit one does (spec/05 §8.1, which states
   the empty case for kernel 31.1.1, where 30.8.1 kept it), so `yyyy-MM-dd` without one is on the
   allowlist while `dd.MM.yyyy` without one is read and left to the pair allowlist; an absent format is
   still refused (tb-range-fmtonly, tb-range-fmtonly-de, tb-range-sepnly). -/
example :
    dateRangeSeparator "{\"format\":\"yyyy-MM-dd\"}" = some "/" ∧
    dateRangeSeparator "{\"format\":\"yyyy-MM-dd\",\"rangeSeparator\":null}" = some "/" ∧
    dateRangeSeparator "{\"format\":\"dd.MM.yyyy\"}" = some "/" ∧
    dateRangeSeparator "{\"format\":\"MM\",\"rangeSeparator\":\"\"}" = some "/" ∧
    dateRangeSeparator "{\"rangeSeparator\":\"/\"}" = none ∧
    dateRangeSeparator "{\"format\":\"yyyy-MM-dd\",\"rangeSeparator\":1}" = none := by
  native_decide

end A12Kernel.Dm
