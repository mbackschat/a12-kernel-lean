import A12Kernel.Reference.Dm.Validate
import A12Kernel.Elaboration.ValidationMessageDiagnostic
import A12Kernel.Elaboration.ValidationMessageRendering

namespace A12Kernel.Dm.IndexMessageLocks

private def model : FlatModel := {
  fields := [
    { id := 1, name := "Key", groupPath := ["Form", "Rows"], repeatableScope := [10],
      policy := { kind := .string } },
    { id := 2, name := "Amount", groupPath := ["Form", "Rows"], repeatableScope := [10],
      policy := { kind := .number { scale := 0, signed := true } } }]
  repeatableGroups := [
    { level := 10, path := ["Form", "Rows"], repeatability := some 2, indexField := some 1 }] }

private def dm : DmModel := {
  flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }

private def checkedRule (condition : String) : Option (CheckedResolvedValidationRule model) :=
  (checkRule dm .english {
    group := ["Form"], name := "Message", errorCode := "INDEX", severity := "ERROR"
    errorEntityRelPath := "../Rows/Amount", condition }).toOption

private def metadata (condition : String) : Option (Bool × Bool) := do
  let checked ← checkedRule condition
  let context := ValidationMessageCondition.rule checked
  pure (← context.indexReferenced? ["Form", "Rows"],
    ← context.indexNonIterating? ["Form", "Rows"] 10)

example : model.validate.isOk = true := by native_decide

example : metadata "[/Form/Rows/Amount] > 0" = some (true, false) ∧
    metadata "Sum(Rows*/Amount) > 0" = some (true, true) ∧
    metadata "[/Form/Rows/Amount] > 0 And Sum(Rows*/Amount) > 0" = some (true, true) := by native_decide

private def indexCheck (condition : String) : Option (Option IndexMessageAuthoringError) := do
  let checked ← checkedRule condition
  pure (match checkMessageIndex (.rule checked) "Key" .value with
    | .ok _ => none
    | .error error => some error)

example : indexCheck "[/Form/Rows/Amount] > 0" = some none ∧
    indexCheck "Sum(Rows*/Amount) > 0" = some (some (.diagnostic .indexFieldNotIterating)) ∧
    indexCheck "[/Form/Rows/Amount] > 0 And Sum(Rows*/Amount) > 0" =
      some (some (.diagnostic .indexFieldNotIterating)) := by native_decide

private def profile : ValidationMessageKeywordProfile := .english

private def authored (source : String) : Option Bool := do
  let checked ← checkedRule "[/Form/Rows/Amount] > 0"
  pure (elaborateValidationMessageTemplate model profile (.rule checked) source).isOk

example : authored "$index(Key).value$" = some true := by native_decide

private def keyedCondition := "[/Form/Rows/Amount] > 0 And [Rows/Amount For \"a\"] > 0"

example : metadata keyedCondition = some (true, true) ∧
    indexCheck keyedCondition = some (some (.diagnostic .indexFieldNotIterating)) := by native_decide

private def selectedGroup (key : String) : Option Bool := do
  let checked ← checkedRule keyedCondition
  (ValidationMessageCondition.rule checked).selectedGroupReferenced? ["Form", "Rows"]
    (some (.literal (.text key) none))

example : selectedGroup "a" = some true ∧ selectedGroup "b" = some false := by native_decide

private def groupAuthoring (condition parameter : String) : Option (Option KernelStaticDiagnostic) := do
  let checked ← checkedRule condition
  match elaborateValidationMessageTemplate model profile (.rule checked) ("$" ++ parameter ++ "$") with
  | .ok _ => pure none
  | .error error => some <$> error.namedRuleDiagnostic?

private def keyedPresence := "FieldFilled(Rows/Amount For \"a\")"

example : groupAuthoring keyedPresence "#Rows For \"a\"" = some none := by native_decide

example : groupAuthoring keyedPresence "#Rows For \"b\"" = some (some .invalidGroupInParameter) ∧
    groupAuthoring keyedPresence "#Rows" = some (some .invalidGroupInParameter) ∧
    groupAuthoring "Sum(Rows*/Amount) > 0" "#Rows" = some (some .iterParamWithStarReference) := by
  native_decide

example : groupAuthoring keyedCondition "#Rows For \"a\"" = some (some .invalidUseOfSemanticIndex) ∧
    groupAuthoring (keyedPresence ++ " And Sum(Rows*/Amount) > 0") "#Rows For \"a\"" = some none ∧
    groupAuthoring (keyedPresence ++ " Or Sum(Rows*/Amount) > 0") "#Rows For \"a\"" =
      some (some .invalidUseOfSemanticIndex) := by native_decide

example : ["GroupFilled(/Form)", "GroupNotFilled(/Form)"].all (fun parentRead =>
      decide (indexCheck ("[/Form/Rows/Amount] > 0 And " ++ parentRead) = some none) &&
      decide (groupAuthoring (keyedPresence ++ " And " ++ parentRead) "#Rows" =
        some (some .invalidGroupInParameter)) &&
      decide (groupAuthoring (keyedPresence ++ " And " ++ parentRead) "#Rows For \"a\"" =
        some none)) = true := by native_decide

private def selectedOperands (secondKey : String) : String :=
  "Rows/Key For \"a\", Rows/Amount For \"" ++ secondKey ++ "\""

private def listGuard (operator secondKey : String) : Option (Option KernelStaticDiagnostic) :=
  groupAuthoring (operator ++ "(" ++ selectedOperands secondKey ++ ")") "#Rows For \"a\""

example : listGuard "AllFieldsFilled" "b" = some none ∧
    listGuard "AllGroupsFilled" "b" = some none ∧
    groupAuthoring "AllFieldsFilled(Rows/Amount For \"b\", Rows/Key For \"a\")"
      "#Rows For \"a\"" = some none ∧
    groupAuthoring "AllGroupsFilled(Rows/Amount For \"b\", Rows/Key For \"a\")"
      "#Rows For \"a\"" = some none ∧
    listGuard "AtLeastOneFieldFilled" "a" = some none ∧
    listGuard "MoreThanOneFieldFilled" "a" = some none ∧
    listGuard "AtLeastOneGroupFilled" "a" = some none ∧
    listGuard "AtLeastOneFieldFilled" "b" = some (some .invalidUseOfSemanticIndex) ∧
    listGuard "MoreThanOneFieldFilled" "b" = some (some .invalidUseOfSemanticIndex) ∧
    listGuard "AtLeastOneGroupFilled" "b" = some (some .invalidUseOfSemanticIndex) := by
  native_decide

example : groupAuthoring "GroupFilled(Rows For \"a\")" "#Rows For \"a\"" = some none ∧
    ["FieldNotFilled(Rows/Amount For \"a\")", "GroupNotFilled(Rows For \"a\")"].all
      (fun condition => decide (groupAuthoring condition "#Rows For \"a\"" =
          some (some .invalidUseOfSemanticIndex)) &&
        decide (groupAuthoring (keyedPresence ++ " And " ++ condition) "#Rows For \"a\"" =
          some none)) = true := by native_decide

example : ["NoFieldFilled", "NotAllFieldsFilled", "NotExactlyOneFieldFilled",
    "FieldsNotCollectivelyFilled", "NoGroupFilled", "NotAllGroupsFilled",
    "GroupsNotCollectivelyFilled"].all (fun operator =>
      decide (listGuard operator "a" = some (some .invalidUseOfSemanticIndex)) &&
      decide (groupAuthoring (keyedPresence ++ " And " ++ operator ++
        "(" ++ selectedOperands "a" ++ ")") "#Rows For \"a\"" = some none)) = true := by
  native_decide

private def groupTemplateError (condition parameter : String) :
    Option (Option ValidationMessageTemplateError) := do
  let checked ← checkedRule condition
  pure (match elaborateValidationMessageTemplate model profile (.rule checked)
      ("$" ++ parameter ++ "$") with
    | .ok _ => none
    | .error error => some error)

example : groupTemplateError keyedPresence "#Rows For \"a\" extra" =
    some (some (.parameterSyntax "#Rows For \"a\" extra" .unexpected)) := by native_decide

private def inputs : ValidationMessageInputs := {
  fieldName := fun _ => { providerResult := none, modelLabel := none, debugDisplay := "unused" }
  fieldValue := fun _ => { displayValue := some "wrong", defaultDisplay := "wrong-default" }
  fieldStoredToken := fun _ => some "wrong"
  formPointer := fun _ _ => "unused" }

private def rendered (row : Nat) (token : Option String)
    (parallel : Option String := none) : Option String := do
  let checked ← checkedRule "[/Form/Rows/Amount] > 0"
  let template ← (elaborateValidationMessageTemplate model profile (.rule checked)
    "$index(Key).value$/$#Rows$").toOption
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption
  let document : Document := {
    instantiatedRows := [{ group := 10, path := [1] }, { group := 10, path := [2] }]
    rawCells := fun address => if address.field == 1 && address.path == [row] then token else none }
  let plan ← (template.toRenderPlanAt {
    environment := [(10, row)], document, prepared, locale := "en_US"
    parallelIndexToken := parallel } inputs).toOption
  pure plan.render.text

example : rendered 1 (some "first") = some "first/1" ∧
    rendered 2 (some "second") = some "second/2" ∧
    rendered 2 none = some "/2" ∧
    rendered 2 (some "") = some "/2" ∧
    rendered 2 (some "stored") (some "joined") = some "joined/2" := by native_decide

private def keyedRendered (insertions : List MessageIndexInsertion) : Option String := do
  let checked ← checkedRule keyedPresence
  let template ← (elaborateValidationMessageTemplate model profile (.rule checked)
    "$#Rows For \"a\"$").toOption
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption
  let plan ← (template.toRenderPlanAt {
    environment := [(10, 2)], document := { instantiatedRows := [], rawCells := fun _ => none }
    prepared, locale := "en_US"
    references := some { cache := .known { insertions }, keyAt := fun _ => none } } inputs).toOption
  pure plan.render.text

example : keyedRendered [{ group := 10, parentPath := [], key := .text "a", row := 1 }] = some "1" ∧
    keyedRendered [] = some "?" := by native_decide

example : keyedRendered [
      { group := 10, parentPath := [], key := .text "a", row := 2 },
      { group := 10, parentPath := [], key := .text "a", row := 1 }] = some "1" ∧
    keyedRendered [
      { group := 10, parentPath := [], key := .text "a", row := 1 },
      { group := 10, parentPath := [], key := .text "a", row := 2 }] = some "2" := by native_decide

private inductive IndexKind where
  | string
  | constrainedString
  | enumeration
  deriving DecidableEq

private def nestedModel (kind : IndexKind) : FlatModel :=
  let key : FlatFieldDecl := {
    id := 1, name := "Key", groupPath := ["Form", "Parents", "Rows"]
    repeatableScope := [5, 10], policy := { kind := .string } }
  let key := match kind with
    | .string => key
    | .constrainedString => { key with stringPolicy := { minLength := some 3 } }
    | .enumeration => { key with
        policy := { kind := .enumeration }
        enumeration := some {
          storedTokens := ["open", "closed"], defaultStoredToken := some "open"
          categories := [{ name := "Category", tokens := ["active", "done"] }]
          displayFacts := [
            { locale := "en_US", stored := "open", display := "Open" },
            { locale := "en_US", stored := "closed", display := "Closed" },
            { locale := "de_DE", stored := "open", display := "Offen" },
            { locale := "de_DE", stored := "closed", display := "Geschlossen" }] } }
  { fields := [key,
      { id := 2, name := "Amount", groupPath := ["Form", "Parents", "Rows"]
        repeatableScope := [5, 10]
        policy := { kind := .number { scale := 0, signed := true } } },
      { id := 3, name := "ForeignKey", groupPath := ["Form", "OtherRows"]
        repeatableScope := [30], policy := { kind := .string } },
      { id := 4, name := "LookupKey", groupPath := ["Form", "Parents"]
        repeatableScope := [5], policy := { kind := .string } }]
    repeatableGroups := [
      { level := 5, path := ["Form", "Parents"], repeatability := some 2 },
      { level := 10, path := ["Form", "Parents", "Rows"],
        repeatability := some 2, indexField := some 1 },
      { level := 30, path := ["Form", "OtherRows"], repeatability := some 2, indexField := some 3 }] }

private def locale : Language → String
  | .english => "en_US"
  | .german => "de_DE"

private def languageProfile : Language → ValidationMessageKeywordProfile :=
  Language.messageKeywordProfile

private def nestedRule (kind : IndexKind) (language : Language) :
    Option (CheckedResolvedValidationRule (nestedModel kind)) :=
  (checkRule {
    flat := nestedModel kind, rules := [], computations := []
    conditionLanguage := locale language, refusals := [] } language {
      group := ["Form"], name := "Message", errorCode := "INDEX", severity := "ERROR"
      errorEntityRelPath := "../Parents/Rows/Amount"
      condition := "[/Form/Parents/Rows/Amount] > 0" }).toOption

private def nestedAuthoring (kind : IndexKind) (language : Language) (source : String) :
    Option (Option ValidationMessageTemplateError) := do
  let checked ← nestedRule kind language
  pure (match elaborateValidationMessageTemplate (nestedModel kind) (languageProfile language)
      (.rule checked) source with
    | .ok _ => none
    | .error error => some error)

example : (nestedModel .string).validate.isOk = true ∧
    (nestedModel .constrainedString).validate.isOk = true ∧
    (nestedModel .enumeration).validate.isOk = true := by native_decide

example : nestedAuthoring .string .english "$index(Key).value$" = some none ∧
    nestedAuthoring .string .german "$index(Key).Wert$" = some none ∧
    nestedAuthoring .enumeration .english "$index(Key).value$/$index(Key)->Category$" = some none ∧
    nestedAuthoring .enumeration .german "$index(Key).Wert$/$index(Key)->Category$" = some none := by
  native_decide

example : nestedAuthoring .string .english "$index(Key)->Category$" =
      some (some (.indexParameter "index(Key)->Category" (.diagnostic .indexFieldNoEnumeration))) ∧
    nestedAuthoring .enumeration .english "$index(Key)->Category$" = some none ∧
    nestedAuthoring .enumeration .english "$index(Key)->Missing$" =
      some (some (.indexParameter "index(Key)->Missing" (.diagnostic .indexFieldCategoryUnknown))) := by
  native_decide

example : nestedAuthoring .string .english "$index(ForeignKey)$" =
      some (some (.indexParameter "index(ForeignKey)" (.diagnostic .indexFieldUnresolved))) ∧
    nestedAuthoring .string .english "$index(ForeignKey).value$" =
      some (some (.indexParameter "index(ForeignKey).value" (.diagnostic .indexFieldUnresolved))) ∧
    nestedAuthoring .string .english "$index(Key)$" =
      some (some (.indexParameter "index(Key)" (.diagnostic .indexFieldSuffixMissing))) := by
  native_decide

private def nestedDocument (first second : Option String) : Document := {
  instantiatedRows := [
    { group := 5, path := [1] }, { group := 5, path := [2] },
    { group := 10, path := [1, 1] }, { group := 10, path := [1, 2] },
    { group := 10, path := [2, 1] }, { group := 10, path := [2, 2] }]
  rawCells := fun address =>
    if address.field != 1 then none
    else if address.path == [1, 2] then first
    else if address.path == [2, 2] then second
    else some "wrong-address" }

private def nestedRendered (kind : IndexKind) (language : Language) (source : String)
    (environment : Env) (first second : Option String)
    (display : Bool := true) (parallel : Option String := none) :
    Option (Sum ValidationMessageRenderingError String) := do
  let checked ← nestedRule kind language
  let template ← (elaborateValidationMessageTemplate (nestedModel kind) (languageProfile language)
    (.rule checked) source).toOption
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler (nestedModel kind)).toOption
  pure (match template.toRenderPlanAt {
    environment, document := nestedDocument first second, prepared
    locale := locale language, displayEnumerations := display
    parallelIndexToken := parallel } inputs with
    | .ok plan => .inr plan.render.text
    | .error error => .inl error)

private def englishValue := "$index(Key).value$/$#Parents/Rows$"
private def germanValue := "$index(Key).Wert$/$#Parents/Rows$"
private def englishEnum := "$index(Key).value$/$index(Key)->Category$/$#Parents/Rows$"
private def germanEnum := "$index(Key).Wert$/$index(Key)->Category$/$#Parents/Rows$"

-- Both parents have child row 2; deeper bindings and wrong-path cells distinguish scope projection.
example : nestedRendered .string .english englishValue [(10, 2), (20, 9), (5, 1)]
      (some "first") (some "second") = some (.inr "first/2") ∧
    nestedRendered .string .english englishValue [(10, 2), (20, 9), (5, 2)]
      (some "first") (some "second") = some (.inr "second/2") ∧
    nestedRendered .string .german germanValue [(5, 2), (10, 2)]
      (some "first") (some "second") = some (.inr "second/2") := by native_decide

example : nestedRendered .enumeration .english englishEnum [(5, 1), (10, 2)]
      (some "open") (some "closed") = some (.inr "Open/active/2") ∧
    nestedRendered .enumeration .english englishEnum [(5, 2), (10, 2)]
      (some "open") (some "closed") = some (.inr "Closed/done/2") ∧
    nestedRendered .enumeration .german germanEnum [(5, 1), (10, 2)]
      (some "open") (some "closed") = some (.inr "Offen/active/2") ∧
    nestedRendered .enumeration .german germanEnum [(5, 2), (10, 2)]
      (some "open") (some "closed") = some (.inr "Geschlossen/done/2") := by native_decide

example : nestedRendered .enumeration .english englishEnum [(5, 2), (10, 2)]
      (some "open") (some "closed") false = some (.inr "closed/done/2") ∧
    nestedRendered .enumeration .german germanEnum [(5, 2), (10, 2)]
      (some "open") (some "closed") false = some (.inr "closed/done/2") ∧
    nestedRendered .enumeration .english englishEnum [(5, 2), (10, 2)]
      (some "open") none = some (.inr "//2") ∧
    nestedRendered .enumeration .english englishEnum [(5, 2), (10, 2)]
      (some "open") (some "") = some (.inr "//2") ∧
    nestedRendered .enumeration .english englishEnum [(5, 2), (10, 2)]
      (some "open") (some "invalid") = some (.inr "//2") := by native_decide

example : nestedRendered .string .english englishValue [(10, 2)]
      (some "first") (some "second") = some (.inl (.environment (.missingBinding 5))) ∧
    nestedRendered .string .english englishValue [(5, 2)]
      (some "first") (some "second") = some (.inl (.environment (.missingBinding 10))) := by
  native_decide

example : nestedRendered .string .english englishValue [(5, 2), (10, 2)]
      (some "first") (some "stored") true (some "joined") = some (.inr "joined/2") ∧
    nestedRendered .enumeration .german germanEnum [(5, 2), (10, 2)]
      (some "open") (some "invalid") true (some "closed") =
      some (.inr "Geschlossen/done/2") ∧
    nestedRendered .enumeration .english englishEnum [(5, 2), (10, 2)]
      (some "open") (some "closed") true (some "") = some (.inr "//2") := by native_decide

example : nestedRendered .constrainedString .english englishValue [(5, 2), (10, 2)]
      (some "first") (some "ab") = some (.inr "/2") ∧
    nestedRendered .constrainedString .english englishValue [(5, 2), (10, 2)]
      (some "first") (some "abc") = some (.inr "abc/2") := by native_decide

private def nestedPresence (language : Language) (dynamic : Bool) : String :=
  let key := if dynamic then "LookupKey" else "\"a\""
  match language with
  | .english => "FieldFilled(LookupKey) And FieldFilled(Rows/Amount For " ++ key ++ ")"
  | .german => "FeldAngegeben(LookupKey) Und FeldAngegeben(Rows/Amount Fuer " ++ key ++ ")"

private def nestedGroupRule (language : Language) (dynamic : Bool) :
    Option (CheckedResolvedValidationRule (nestedModel .string)) :=
  (checkRule {
    flat := nestedModel .string, rules := [], computations := []
    conditionLanguage := locale language, refusals := [] } language {
      group := ["Form", "Parents"], name := "Message", errorCode := "INDEX", severity := "ERROR"
      errorEntityRelPath := "../Rows/Amount"
      condition := nestedPresence language dynamic }).toOption

private def nestedGroupParameter (language : Language) (dynamic : Bool) : String :=
  let key := if dynamic then "LookupKey" else "\"a\""
  match language with
  | .english => "#Rows For " ++ key
  | .german => "#Rows Fuer " ++ key

private def nestedGroupAuthoring (language : Language) (dynamic : Bool) :
    Option (Option ValidationMessageTemplateError) := do
  let checked ← nestedGroupRule language dynamic
  pure (match elaborateValidationMessageTemplate (nestedModel .string) (languageProfile language)
      (.rule checked) ("$" ++ nestedGroupParameter language dynamic ++ "$") with
    | .ok _ => none
    | .error error => some error)

example : nestedGroupAuthoring .english false = some none ∧
    nestedGroupAuthoring .german false = some none ∧
    nestedGroupAuthoring .english true = some none ∧
    nestedGroupAuthoring .german true = some none := by native_decide

private def nestedCache : List MessageIndexInsertion := [
  { group := 10, parentPath := [1], key := .text "a", row := 1 },
  { group := 10, parentPath := [2], key := .text "a", row := 2 },
  { group := 10, parentPath := [2], key := .text "b", row := 1 }]

private def nestedReferences (readKey : Bool := true) : MessageReferenceInputs := {
  cache := .known { insertions := nestedCache }
  keyAt := fun address =>
    if !readKey then none
    else if address.field == 4 && address.path == [1] then some (.text "a")
    else if address.field == 4 && address.path == [2] then some (.text "b")
    else some (.text "wrong-key-address") }

private def nestedGroupRendered (language : Language) (dynamic : Bool)
    (environment : Env) (references : Option MessageReferenceInputs := some nestedReferences) :
    Option (Sum ValidationMessageRenderingError String) := do
  let checked ← nestedGroupRule language dynamic
  let template ← (elaborateValidationMessageTemplate (nestedModel .string) (languageProfile language)
    (.rule checked) ("$" ++ nestedGroupParameter language dynamic ++ "$")).toOption
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler (nestedModel .string)).toOption
  pure (match template.toRenderPlanAt {
    environment, document := nestedDocument (some "b") (some "a"), prepared
    locale := locale language, references } inputs with
    | .ok plan => .inr plan.render.text
    | .error error => .inl error)

example : nestedGroupRendered .english false [(10, 2), (20, 9), (5, 1)] = some (.inr "1") ∧
    nestedGroupRendered .english false [(10, 1), (20, 9), (5, 2)] = some (.inr "2") ∧
    nestedGroupRendered .german false [(5, 2)] = some (.inr "2") ∧
    nestedGroupRendered .english true [(10, 2), (20, 9), (5, 1)] = some (.inr "1") ∧
    nestedGroupRendered .english true [(10, 2), (20, 9), (5, 2)] = some (.inr "1") ∧
    nestedGroupRendered .german true [(5, 2)] = some (.inr "1") := by native_decide

example : nestedGroupRendered .english false [(5, 2), (10, 2)] none =
      some (.inl (.reference .missingIndexContext)) ∧
    nestedGroupRendered .english false [(10, 2)] =
      some (.inl (.reference (.binding (.missingBinding 5)))) ∧
    nestedGroupRendered .english true [(5, 2), (10, 2)] (some (nestedReferences false)) =
      some (.inr "?") := by native_decide

end A12Kernel.Dm.IndexMessageLocks
