import A12Kernel.Elaboration.ValidationMessageDiagnostic
import A12Kernel.Conformance.MessageGroupArgument

/-! # Checked validation-message authoring conformance locks

The rule-message template's name-position, keyed, form-pointer, Base Year, category, character and
render cases, over one shared model and keyword profile. The group position's template cases use the
same fixture and are locked in `Conformance/MessageGroupPosition.lean`, which is why the model, the
profile and the condition-built template helpers are public here. -/

namespace A12Kernel.Conformance.ValidationMessageAuthoring

open A12Kernel

private def amount : FlatFieldDecl :=
  { id := 0, groupPath := ["Order"], name := "Amount",
    policy := { kind := .number { scale := 0, signed := true } } }

def other : FlatFieldDecl :=
  { id := 1, groupPath := ["Order"], name := "Other",
    policy := { kind := .string } }

/-- A **second** `Amount`, one nonrepeatable group down. Its name collides with the root one, which is
exactly the case the path forms exist for: the bare name is ambiguous and a path disambiguates. -/
private def headAmount : FlatFieldDecl :=
  { id := 2, groupPath := ["Order", "Head"], name := "Amount",
    policy := { kind := .string } }

/-- A field whose name collides with a terminal that **must** be quoted in a parameter. -/
private def forField : FlatFieldDecl :=
  { id := 3, groupPath := ["Order"], name := "For",
    policy := { kind := .string } }

/-- A field whose name collides with a terminal this producer accepts **unquoted**. -/
private def indexField : FlatFieldDecl :=
  { id := 4, groupPath := ["Order"], name := "index",
    policy := { kind := .string } }

/-- One Enumeration field with a declared category, so the category suffix has both an admitted and a
refused name to separate. -/
private def status : FlatFieldDecl :=
  { id := 5, groupPath := ["Order"], name := "Status",
    policy := { kind := .enumeration }
    enumeration := some {
      storedTokens := ["open", "closed"]
      categories := [{ name := "Group", tokens := ["A", "B"] }]
    } }

/-- A field one level **below** the rule group used by the group-position cases, so a refused
descendant is a group the model really declares rather than an unknown path wearing a longer name. -/
private def deepField : FlatFieldDecl :=
  { id := 6, groupPath := ["Order", "Head", "Deeper"], name := "Deep",
    policy := { kind := .string } }

/-- A field in a **sibling** of that rule group, so a refused sibling is likewise declared. -/
private def asideField : FlatFieldDecl :=
  { id := 7, groupPath := ["Order", "Side"], name := "Aside",
    policy := { kind := .string } }

/-- A field three levels below the root, so a parent walk of three steps can reach the root exactly. -/
private def baseField : FlatFieldDecl :=
  { id := 9, groupPath := ["Order", "Head", "Deeper", "Base"], name := "Bottom",
    policy := { kind := .string } }

/-- A field under a **second root group**. The Kernel admits a model with more than one root, which is
what makes the root shorthand's meaning measurable rather than a distinction without a difference. -/
private def branchLabel : FlatFieldDecl :=
  { id := 8, groupPath := ["Vendor", "Branch"], name := "Label",
    policy := { kind := .string } }

def model : FlatModel :=
  { fields := [amount, other, headAmount, forField, indexField, status,
      deepField, asideField, branchLabel, baseField] }

def bare (field : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field }

/-- The exact en_US parameter terminal set, read off the Kernel's own English terminal bundle, together
with the seven this producer historically accepts unquoted inside an entity name. Only `For`,
`RuleGroup`, and `BaseYear` therefore need the quote escape here. -/
def keywordProfile : ValidationMessageKeywordProfile := {
  path := { reserved := MessageGroupArgument.englishReservedTerminals }
  unquotedTerminals := MessageGroupArgument.englishUnquotedTerminals
  baseYearTerminal := "BaseYear"
  forTerminal := "For"
  valueSuffixTerminal := "value"
  rootGroupTerminal := "RootGroup"
  ruleGroupTerminal := "RuleGroup"
  formLineTerminal := "Vordruckzeile"
  formNameTerminal := "Vordruckname"
  retiredGroupTerminals := ["Zeile", "Usb"]
  offsetGroupTerminals := ["Zeile"]
}

private def condition? : Option (CheckedFlatCondition model) :=
  (elaborate model ["Order"] (.fieldFilled (bare "Amount"))).toOption

def pathAt (base : PathBase) (groups : List String) (field : String) :
    SurfaceFieldPath :=
  { base, groups, field }

/-- A condition in `group` whose one operand is `reference`, so the membership gate is satisfied for
exactly that field however the message spells it. -/
private def conditionOn? (group : GroupPath) (reference : SurfaceFieldPath) :
    Option (CheckedFlatCondition model) :=
  (elaborate model group (.fieldFilled reference)).toOption

def pathTemplateOk? (group : GroupPath) (reference : SurfaceFieldPath)
    (template : String) : Option Bool := do
  let condition ← conditionOn? group reference
  pure (elaborateValidationMessageTemplate model keywordProfile condition
    template).toOption.isSome

def pathTemplateError? (group : GroupPath) (reference : SurfaceFieldPath)
    (template : String) : Option ValidationMessageTemplateError := do
  let condition ← conditionOn? group reference
  match elaborateValidationMessageTemplate model keywordProfile condition
      template with
  | .ok _ => none
  | .error error => some error

/- The parameter's entity spec is the shared path grammar, so one field with an ambiguous bare name is
reachable three ways from a root-group rule and by a parent walk from the group below it: qualified by
its group, absolutely, and with an explicit turning point. -/
example :
    pathTemplateOk? ["Order"] (pathAt (.relative 0) ["Head"] "Amount")
        "See $Head/Amount$" = some true ∧
      pathTemplateOk? ["Order"] (pathAt (.relative 0) ["Head"] "Amount")
        "See $/Order/Head/Amount$" = some true ∧
      pathTemplateOk? ["Order", "Head"] (pathAt (.relative 1) [] "Amount")
        "See $../Amount$" = some true ∧
      pathTemplateOk? ["Order", "Head"] (pathAt (.relative 1) [] "Amount")
        "See $..Order/Amount$" = some true := by
  native_decide

/- The path form is **necessary** rather than decorative: with two fields named `Amount`, the bare
name reaches the declaring group's own declaration and only the qualified path reaches the other. The
older bare-name cases above therefore still pin the root field, not this one. -/
example :
    (model.resolveNonrepeatableFieldUnchecked ["Order"]
        (pathAt (.relative 0) [] "Amount")).toOption.map (·.path) =
      some ["Order", "Amount"] ∧
    (model.resolveNonrepeatableFieldUnchecked ["Order"]
        (pathAt (.relative 0) ["Head"] "Amount")).toOption.map (·.path) =
      some ["Order", "Head", "Amount"] := by
  native_decide

/- The value suffix is taken at the end of the whole spec, so it composes with every path form. -/
example :
    pathTemplateOk? ["Order"] (pathAt (.relative 0) ["Head"] "Amount")
        "See $Head/Amount.value$" = some true := by
  native_decide

/- A turning point validates the group it names without changing how many levels are crossed, so a
wrong name is a resolution failure carrying the decoded path rather than a parse failure. -/
example :
    pathTemplateError? ["Order", "Head"] (pathAt (.relative 1) [] "Amount")
        "See $..Nope/Amount$" =
      some (.reference "..Nope/Amount"
        (.invalidEntity
          { base := .relative 1, turningPoint := some "Nope", groups := []
            field := "Amount" })) := by
  native_decide

/- Malformed specs are the Kernel's single parse class, not a family of shape classes: an empty
segment and a bare parent walk with no field. A lone absolute segment is not malformed; it resolves
like any other entity spec. -/
example :
    pathTemplateError? ["Order"] (pathAt (.relative 0) ["Head"] "Amount")
        "See $Head//Amount$" = some (.invalidParameter "Head//Amount") ∧
      pathTemplateError? ["Order"] (pathAt (.relative 0) ["Head"] "Amount")
        "See $..$" = some (.invalidParameter "..") := by
  native_decide

/- A terminal collision is refused at **any** path level, not only as the final name, and the refusal
names the colliding segment rather than the whole spec. -/
example :
    pathTemplateError? ["Order"] (pathAt (.relative 0) ["Head"] "Amount")
        "See $For/Amount$" = some (.unquotedTerminalName "For") := by
  native_decide

/- The grammar's single-quote escape makes a colliding name authorable, and the quotes are erased
before lookup, so the same field is reached and the refusal is about the missing escape rather than
about the name. -/
example :
    pathTemplateOk? ["Order"] (pathAt (.relative 0) [] "For")
        "See $'For'$" = some true ∧
      pathTemplateError? ["Order"] (pathAt (.relative 0) [] "For")
        "See $For$" = some (.unquotedTerminalName "For") := by
  native_decide

/- This producer's quoting rule is **narrower** than the condition language's: a terminal it
historically accepts unquoted needs no escape, and quoting it anyway stays transparent. Without that
exemption the first of these two would be refused. -/
example :
    pathTemplateOk? ["Order"] (pathAt (.relative 0) [] "index")
        "See $index$" = some true ∧
      pathTemplateOk? ["Order"] (pathAt (.relative 0) [] "index")
        "See $'index'$" = some true := by
  native_decide

/-- The same model with a declared Base Year, so the parameter's one gate has both sides. -/
private def configured : FlatModel := { model with baseYear := some 2020 }

private def baseYearRender? (template : String) : Option ResolvedMessageText := do
  let condition ←
    (elaborate configured ["Order"]
      (.fieldFilled (pathAt (.relative 0) [] "Amount"))).toOption
  let checked ←
    (elaborateValidationMessageTemplate configured keywordProfile condition
      template).toOption
  pure (checked.toRenderPlan {
    fieldName := fun _ =>
      { providerResult := none, modelLabel := none, debugDisplay := "A" }
    fieldValue := fun _ => { displayValue := none, defaultDisplay := "0" }
    fieldStoredToken := fun _ => none
    formPointer := fun _ _ => ""
  }).render

/- The Base Year parameter applies its authored offset at authoring, because nothing about it depends
on the document. An absent offset is the same parameter with no calculation. These three rendered
values are Kernel-measured on both codegen strategies against a Base Year of 2020. -/
example :
    baseYearRender? "Year $BaseYear$" = some { text := "Year 2020" } ∧
      baseYearRender? "Year $BaseYear+3$" = some { text := "Year 2023" } ∧
      baseYearRender? "Year $BaseYear-1$" = some { text := "Year 2019" } := by
  native_decide

/- Its one static gate is that the model declares a Base Year, and the offset syntax is exactly a
sign and digits: any other tail is the single parse class rather than a zero offset. -/
example :
    pathTemplateError? ["Order"] (pathAt (.relative 0) [] "Amount")
        "Year $BaseYear$" = some .noBaseYear ∧
      pathTemplateError? ["Order"] (pathAt (.relative 0) [] "Amount")
        "Year $BaseYear*2$" = some (.invalidParameter "BaseYear*2") ∧
      pathTemplateError? ["Order"] (pathAt (.relative 0) [] "Amount")
        "Year $BaseYear+$" = some (.invalidParameter "BaseYear+") := by
  native_decide

/- Each field is already referenced by the condition, so these rows reach the category checks: missing name, Enumeration kind, then declared-category lookup. -/
example :
    pathTemplateOk? ["Order"] (pathAt (.relative 0) [] "Status")
        "See $Status->Group$" = some true ∧
      pathTemplateError? ["Order"] (pathAt (.relative 0) [] "Status")
        "See $Status->$" = some (.missingCategoryName "Status->") ∧
      pathTemplateError? ["Order"] (pathAt (.relative 0) [] "Status")
        "See $Status->Nope$" =
          some (.category "Status->Nope" (.unknownCategory "Nope")) ∧
      pathTemplateError? ["Order"] (pathAt (.relative 0) [] "Amount")
        "See $Amount->Group$" =
          some (.categoryFieldNotEnumeration "Amount->Group" amount.id) := by
  native_decide

/- The suffixes are alternatives: combining them is a parse failure, which the Kernel confirms. A
**doubled** arrow has no single class: a declared first category reaches the trailing-syntax refusal,
an undeclared first category stops at the category gate, and a non-Enumeration field stops at the kind
gate. The three rows differ only in that first lookup, so they separate gate order from syntax. -/
example :
    pathTemplateError? ["Order"] (pathAt (.relative 0) [] "Status")
        "See $Status.value->Group$" =
      some (.invalidParameter "Status.value->Group") ∧
    pathTemplateError? ["Order"] (pathAt (.relative 0) [] "Status")
        "See $Status->Group->Group$" =
      some (.invalidParameter "Status->Group->Group") ∧
    pathTemplateError? ["Order"] (pathAt (.relative 0) [] "Status")
        "See $Status->Nope->Nope$" =
      some (.category "Status->Nope->Nope" (.unknownCategory "Nope")) ∧
    pathTemplateError? ["Order"] (pathAt (.relative 0) [] "Amount")
        "See $Amount->Group->Group$" =
      some (.categoryFieldNotEnumeration "Amount->Group->Group" amount.id) := by
  native_decide

/- An unbalanced quote is a parse failure rather than a name, so a half-written escape never resolves
as a literal name containing a quote. -/
example :
    pathTemplateError? ["Order"] (pathAt (.relative 0) [] "For")
        "See $'For$" = some (.invalidParameter "'For") := by
  native_decide

private def inputs : ValidationMessageInputs where
  fieldName field :=
    if field == amount.id then
      { providerResult := some "Amount label"
        modelLabel := some "Ignored model label"
        debugDisplay := "/Order/Amount" }
    else
      { providerResult := none, modelLabel := none, debugDisplay := "Other" }
  fieldValue field :=
    if field == amount.id then
      { displayValue := some "$Other$", defaultDisplay := "0" }
    else
      { displayValue := none, defaultDisplay := "" }
  fieldStoredToken field := if field == status.id then some "open" else none
  -- Distinct per terminal so a render case can tell which word was written, which is the only thing
  -- a caller can be asked for while what the Kernel renders here is unmeasured.
  formPointer _ pointer :=
    match pointer with
    | .line => "L"
    | .name => "N"

def render? (template : String) : Option ResolvedMessageText := do
  let condition ← condition?
  let checked ←
    (elaborateValidationMessageTemplate model keywordProfile condition template).toOption
  pure (checked.toRenderPlan inputs).render

/-- Render a template under a condition chosen by its operand, so a case may pick the field it needs. -/
private def renderOn? (group : GroupPath) (reference : SurfaceFieldPath)
    (template : String) : Option ResolvedMessageText := do
  let condition ← conditionOn? group reference
  let checked ←
    (elaborateValidationMessageTemplate model keywordProfile condition
      template).toOption
  pure (checked.toRenderPlan inputs).render

/- The checked part retains **which** of the two form-pointer words was authored, so a caller can
   answer for each one separately. That is the whole reason the two are one form with a terminal field
   rather than one undifferentiated part: what either renders is unmeasured, and a part that had
   collapsed them could not even pose the question to its caller. -/
example :
    render? "at $Other.Vordruckzeile$/$Other.Vordruckname$" =
      some { text := "at L/N" } := by
  native_decide

/- A category access renders the category token the field's **current stored value** maps to, through
the declaration's own mapping rather than through anything the caller decides. `open` is the first
declared value, whose `Group` token is `A` — the exact Kernel-measured pairing. -/
example :
    renderOn? ["Order"] (pathAt (.relative 0) [] "Status")
        "Is $Status->Group$ now" = some { text := "Is A now" } := by
  native_decide

/- An absent stored value renders as the empty string, which is Kernel-measured: an empty Enumeration
renders nothing under **both** suffixes while its label still renders. A value the category does not
map cannot arise, because categories align one-to-one with the declared values. -/
example :
    (do
      let condition ← conditionOn? ["Order"] (pathAt (.relative 0) [] "Status")
      let checked ← (elaborateValidationMessageTemplate model keywordProfile
        condition "Is $Status->Group$ now").toOption
      pure (checked.toRenderPlan { inputs with
        fieldStoredToken := fun _ => none }).render) =
    some { text := "Is  now" } := by
  native_decide

private def templateOk? (template : String) : Option Bool := do
  let condition ← condition?
  pure (elaborateValidationMessageTemplate model keywordProfile condition
    template).toOption.isSome

private def templateError? (template : String) :
    Option ValidationMessageTemplateError := do
  let condition ← condition?
  match elaborateValidationMessageTemplate model keywordProfile condition template with
  | .ok _ => none
  | .error error => some error

example :
    render? "Cost $$ $Amount$ [$Amount.value$]" =
        some { text := "Cost $ Amount label [$Other$]" } ∧
      render? "$$$$" = some { text := "$$" } := by
  native_decide

example :
    templateError? "" =
        some .emptyTemplate ∧
      templateError? "$Missing" =
        some .oddDollarCount ∧
      templateError? "line\n$" =
        some .lineSeparator ∧
      templateError? "\t$" =
        some (.controlCharacter '\t') ∧
      templateError? "$Other$" =
        some (.fieldNotReferenced "Other" other.id) ∧
      templateError? "$Missing$" =
        some (.reference "Missing" (.invalidEntity (bare "Missing"))) ∧
      templateError? "$Amount.nope$" =
        some (.invalidParameter "Amount.nope") ∧
      templateError? "$For$" =
        some (.unquotedTerminalName "For") := by
  native_decide

/-- The Kernel code a template's refusal projects to, for a rule in `group` reading `reference` on
`onModel`. -/
private def namedClassOn? (onModel : FlatModel) (group : GroupPath) (reference : SurfaceFieldPath)
    (template : String) : Option (Option String) := do
  let condition ← (elaborate onModel group (.fieldFilled reference)).toOption
  match elaborateValidationMessageTemplate onModel keywordProfile condition template with
  | .ok _ => none
  | .error error => some (error.namedRuleDiagnostic?.map KernelStaticDiagnostic.kernelCode)

/- The name position's path refusals carry their own classes: an unknown root, an entity that does not
resolve below it, and a walk past the root. A name that resolves to a group is no read field, whatever the condition reads inside it
([checkpoint](../../docs/sources/message-and-pointer-probes.md#src-message-name-position-refusals)). -/
example :
    let root := namedClassOn? model ["Order"] (pathAt (.relative 0) ["Head", "Deeper"] "Deep")
    root "See $/Nope/Amount$" = some (some "INVALID_ROOT_GROUP") ∧
      root "See $/Order/Nope/Amount$" = some (some "INVALID_ENTITY") ∧
      root "See $Nope$" = some (some "INVALID_ENTITY") ∧
      root "See $Nope/Amount$" = some (some "INVALID_ENTITY") ∧
      root "See $Head$" = some (some "INVALID_FIELD") ∧
      root "See $Head/Deeper$" = some (some "INVALID_FIELD") ∧
      namedClassOn? model ["Order", "Head"] (bare "Amount") "See $../../Amount$" =
        some (some "ERROR_TEXT_PARAMETER_TOO_MANY_PARENT_GROUPS") ∧
      namedClassOn? model ["Order", "Head"] (bare "Amount") "See $..Wrong/Amount$" =
        some (some "INVALID_ENTITY") := by
  native_decide

/- The forms that carry a name keep its resolution but not always its group class
([checkpoint](../../docs/sources/message-and-pointer-probes.md#src-message-name-position-carriers)). A
form pointer naming a group draws its own class, while the suffixed forms and a group's lone absolute
segment keep the membership one. A keyed form resolves a group as an entity and leaves it to the index
gate, which this fragment does not decide, so only a key that names nothing is classed. The message's
short-name tier answers with the model's flag off, which is this fixture's default, admitting a read
or form-pointed field by its short name, and an ambiguous first segment answers even when more path
follows it. -/
example :
    let root := namedClassOn? model ["Order"] (pathAt (.relative 0) ["Head", "Deeper"] "Deep")
    let side := namedClassOn? model ["Order", "Side"] (bare "Aside")
    root "See $Head.Vordruckzeile$" = some (some "INVALID_FIELD_IN_PARAMETER") ∧
      root "See $/Order/Head.Vordruckname$" = some (some "INVALID_FIELD_IN_PARAMETER") ∧
      namedClassOn? model ["Order", "Head"] (bare "Amount") "See $Head.Vordruckzeile$" =
        some (some "INVALID_ENTITY") ∧
      namedClassOn? model ["Order", "Head"] (bare "Amount") "See $Deeper.Vordruckzeile$" =
        some (some "INVALID_FIELD_IN_PARAMETER") ∧
      root "See $Head.value$" = some (some "INVALID_FIELD") ∧
      root "See $Head->Cat$" = some (some "INVALID_FIELD") ∧
      root "See $Head For \"k\"$" = some none ∧
      root "See $Amount For Head$" = some none ∧
      root "See $Head For Nope$" = some (some "INVALID_ENTITY") ∧
      root "See $/Order$" = some (some "INVALID_FIELD") ∧
      root "See $/Nope$" = some (some "INVALID_ROOT_GROUP") ∧
      side "See $Amount$" = some (some "ERROR_TEXT_FIELDNAME_NOT_UNIQUE") ∧
      side "See $Amount/Foo$" = some (some "ERROR_TEXT_FIELDNAME_NOT_UNIQUE") ∧
      side "See $Deep/Foo$" = some (some "INVALID_ENTITY") ∧
      side "See $Deep$" = some (some "INVALID_FIELD") ∧
      root "See $Deep$" = none ∧
      side "See $Deep.Vordruckzeile$" = none ∧
      side "See $Amount.Vordruckzeile$" = some (some "ERROR_TEXT_FIELDNAME_NOT_UNIQUE") := by
  native_decide

/- A key is a literal or an entity with a key of its own, and the checks run in the parser's event
order: every name resolves as it is read, outer before inner, then a key that is itself keyed is
refused, then the index gate answers
([checkpoint](../../docs/sources/message-and-pointer-probes.md#src-message-name-position-carriers)).
So a name that resolves nowhere answers first in any position, a keyed field or group key draws the
nesting class, and a literal followed by a key reaches the index gate, which this fragment leaves
unprojected. The category suffix's two declaration gates carry their own classes
([checkpoint](../../docs/sources/message-and-pointer-probes.md#src-rule-message-parameter-grammar)). -/
example :
    let root := namedClassOn? model ["Order"] (pathAt (.relative 0) ["Head", "Deeper"] "Deep")
    root "See $Deep For Head/Deeper/Deep For \"k\"$" = some (some "ILLEGAL_SEMANTIC_INDEX") ∧
      root "See $Deep For Head For \"k\"$" = some (some "ILLEGAL_SEMANTIC_INDEX") ∧
      root "See $Deep For Head/Deeper/Deep For Deep$" = some (some "ILLEGAL_SEMANTIC_INDEX") ∧
      root "See $Deep For \"k1\" For \"k2\"$" = some none ∧
      root "See $Deep For Nope For \"k\"$" = some (some "INVALID_ENTITY") ∧
      root "See $Nope For Head/Deeper/Deep For \"k\"$" = some (some "INVALID_ENTITY") ∧
      root "See $Deep For Head/Deeper/Deep For Nope$" = some (some "INVALID_ENTITY") ∧
      namedClassOn? model ["Order"] (bare "Status") "See $Status->Nope$" =
        some (some "INVALID_CATEGORY") ∧
      namedClassOn? model ["Order"] (bare "Amount") "See $Amount->Group$" =
        some (some "FIELD_NO_ENUM") := by
  native_decide

/-- One code point as a one-character string, so a case can name a scalar Lean's char escapes do not spell. -/
private def cp (value : Nat) : String := String.singleton (Char.ofNat value)

private def templateNamedDiagnostic? (template : String) : Option (Option String) :=
  (templateError? template).map fun error =>
    error.namedRuleDiagnostic?.map KernelStaticDiagnostic.kernelCode

example :
    templateError? "$Other->$" = some (.fieldNotReferenced "Other->" other.id) ∧
    templateError? "$Other->->Group$" =
      some (.fieldNotReferenced "Other->->Group" other.id) ∧
    templateError? "$Missing->$" =
      some (.reference "Missing->" (.invalidEntity (bare "Missing"))) ∧
    templateError? "$Missing->->Group$" =
      some (.reference "Missing->->Group" (.invalidEntity (bare "Missing"))) ∧
    templateError? "$Amount->$" = some (.missingCategoryName "Amount->") ∧
    templateNamedDiagnostic? "$Amount->$" = some (some "NO_CATEGORY") ∧
    templateError? "$Amount->->Group$" = some (.missingCategoryName "Amount->->Group") := by
  native_decide

example :
    templateError? "$Other-> For \"k1\"$" =
      some (.semanticIndexUnsupported "Other-> For \"k1\"") ∧
    templateError? "$Missing-> For \"k1\"$" =
      some (.reference "Missing-> For \"k1\"" (.invalidEntity (bare "Missing"))) := by
  native_decide

example :
    ["", "$Amount", "line\ntwo", "row\there", "$BaseYear$", "$Other$"].map
        templateNamedDiagnostic? =
      [some (some "RULE_HAS_NO_ERRORTEXT"), some (some "WRONG_NUMBER_OF_DOLLARS"),
       some (some "INVALID_LINEBREAK"), some (some "INVALID_CHARACTERS"),
       some (some "NO_BASE_YEAR"), some (some "INVALID_FIELD")] ∧
    templateNamedDiagnostic? "$BaseYear+1$" = some (some "NO_BASE_YEAR") ∧
    templateNamedDiagnostic? "$Other.value$" = some (some "INVALID_FIELD") ∧
    templateNamedDiagnostic? "$Né$" = some (some "MVK_LEXER_STANDARD_ERROR") ∧
    templateNamedDiagnostic? "row $#/Order/$" = some (some "MVK_INCOMPLETE_INPUT") ∧
    templateNamedDiagnostic? "row $#/Order//Head$" = some (some "MVK_UNEXPECTED_TOKEN") ∧
    templateNamedDiagnostic? "row $#/'Order$" = some (some "MVK_LEXER_STANDARD_ERROR") ∧
    templateNamedDiagnostic? "row $#Zeile-$" = some (some "MVK_EXPECTED_TOKEN_NOT_FOUND") ∧
    templateNamedDiagnostic? "row $#/Order-x$" = some (some "MVK_UNEXPECTED_TOKEN") := by
  native_decide

example :
    templateNamedDiagnostic? (cp 0x1F600 ++ " $Amount") =
      some (some "WRONG_NUMBER_OF_DOLLARS") ∧
    templateNamedDiagnostic? (cp 0x1F600 ++ "\ttwo") =
      some (some "INVALID_CHARACTERS") ∧
    templateNamedDiagnostic? ("row $An" ++ cp 0x1F600 ++ "chor$") =
      some (some "MVK_LEXER_STANDARD_ERROR") ∧
    templateNamedDiagnostic? (cp 0x1F600 ++ " $Amount$") = some none ∧
    templateNamedDiagnostic? "$BaseYear+$" = some none ∧
    templateNamedDiagnostic? (cp 0x1F600 ++ " $Amount For \"k1\"$") = some none ∧
    templateNamedDiagnostic? "Cost $$ $Amount$" = none ∧
    templateNamedDiagnostic? "$$$$" = none := by
  native_decide

example :
    templateError? ("t" ++ cp 0x1F600 ++ "x $Amount") =
      some (.unsupportedCharacterWithError (Char.ofNat 0x1F600) .oddDollarCount) ∧
    templateError? ("t" ++ cp 0x1F600 ++ "x $Missing$") =
      some (.unsupportedCharacterWithError (Char.ofNat 0x1F600)
        (.reference "Missing" (.invalidEntity (bare "Missing")))) ∧
    templateError? ("t" ++ cp 0x1F600 ++ "x\ntwo") =
      some (.unsupportedCharacterWithError (Char.ofNat 0x1F600) .lineSeparator) ∧
    templateError? ("t" ++ cp 0x1F600 ++ "x\ttwo") =
      some (.unsupportedCharacterWithError (Char.ofNat 0x1F600)
        (.controlCharacter '\t')) ∧
    templateError? ("row $An" ++ cp 0x1F600 ++ "chor$") =
      some (.unsupportedCharacterWithError (Char.ofNat 0x1F600)
        (.parameterCharacter ("An" ++ cp 0x1F600 ++ "chor") (Char.ofNat 0x1F600))) ∧
    templateError? ("t" ++ cp 0x1F600 ++ "x $Amount$") =
      some (.unsupportedCharacter (Char.ofNat 0x1F600)) ∧
    templateError? ("x" ++ cp 0x1F600 ++ cp 0x1D400 ++ "y") =
      some (.unsupportedCharacter (Char.ofNat 0x1F600)) ∧
    templateError? ("x" ++ cp 0x1F600 ++ " $Amount For \"k1\"$") =
      some (.unsupportedCharacterWithError (Char.ofNat 0x1F600)
        (.semanticIndexUnsupported "Amount For \"k1\"")) := by
  native_decide

/- **The template's character repertoire is the BMP, and it is the value charset's rule reaching a second
   carrier** — not the printable-ASCII bound this gate used to apply, which refused message text the Kernel
   admits. Measured over fourteen admitted BMP code points spanning Latin-1, Latin Extended-A, currency,
   Greek, Cyrillic, CJK, punctuation and `U+FFFD`, and two refused supplementary-plane ones
   ([checkpoint](../../docs/SOURCES.md#src-message-template-character-repertoire)). The refusal is the same
   BMP predicate `LegalCharset` already carries for a stored value. -/
example :
    templateError? "Prüfe $Amount$" = none ∧
    templateError? "Größe – €5 … 一 α Ж ÿ" = none ∧
    templateError? ("smile " ++ cp 0x1F600) = some (.unsupportedCharacter (Char.ofNat 0x1F600)) ∧
    templateError? ("bold " ++ cp 0x1D400) = some (.unsupportedCharacter (Char.ofNat 0x1D400)) := by
  native_decide

/- **The invisible-format characters are the control class, not the repertoire one.** `DELETE`, the C1
   `NEL`, a soft hyphen and a zero-width space each draw the Kernel's `INVALID_CHARACTERS` where a line
   separator draws its own class, so this gate cannot be stated as "C0 plus DEL". `U+2028` stays the line
   class, which is what keeps the two apart. -/
example :
    templateError? ("del " ++ cp 0x007F) = some (.controlCharacter (Char.ofNat 0x007F)) ∧
    templateError? ("nel " ++ cp 0x0085) = some (.controlCharacter (Char.ofNat 0x0085)) ∧
    templateError? ("soft " ++ cp 0x00AD) = some (.controlCharacter (Char.ofNat 0x00AD)) ∧
    templateError? ("zwsp " ++ cp 0x200B) = some (.controlCharacter (Char.ofNat 0x200B)) ∧
    templateError? ("sep " ++ cp 0x2028) = some .lineSeparator := by
  native_decide

/- **Both Unicode separators are the line class, and the line gate is asked first over the whole text**
   ([inbound](../../docs/SOURCES.md#inbound-2026-09-26m-message-characters)). `U+2029` is not a control
   character, so a reading keyed on control characters misses it; beside a tab written earlier the
   separator still answers. Either character gate withholds the parameter classes: the unknown name draws
   its entity class only in the control row, and the unclosed parameter its dollar class not at all. A
   no-break space is admitted, which separates the `\p{C}` reading from one refusing every non-printing
   or space character. -/
example :
    templateError? ("par " ++ cp 0x2029) = some .lineSeparator ∧
    templateError? ("nbsp " ++ cp 0x00A0 ++ " x") = none ∧
    templateError? ("a\tb" ++ cp 0x2028 ++ "c") = some .lineSeparator ∧
    templateError? "see $Missing$" =
      some (.reference "Missing" (.invalidEntity (bare "Missing"))) ∧
    templateError? ("see $Missing$ a" ++ cp 0x200B ++ "b") =
      some (.controlCharacter (Char.ofNat 0x200B)) ∧
    templateError? ("see $Missing$ a" ++ cp 0x2028 ++ "b") = some .lineSeparator ∧
    templateError? ("see $Amount a" ++ cp 0x200B ++ "b") =
      some (.controlCharacter (Char.ofNat 0x200B)) := by
  native_decide

/- **The control class is Java's `\p{C}` asked per code point**
   ([inbound](../../docs/SOURCES.md#inbound-2026-09-26m-message-characters)), so the format, private-use
   and unassigned characters draw it too, and a supplementary character inside the set draws it beside
   the repertoire refusal where one outside it draws the refusal alone. -/
example :
    [0xFEFF, 0x200E, 0xE000, 0x378].all (fun point =>
      templateError? ("a" ++ cp point ++ "b") == some (.controlCharacter (Char.ofNat point))) ∧
    [0xF0000, 0xE0001].all (fun point =>
      templateError? ("a" ++ cp point ++ "b") ==
        some (.unsupportedCharacterWithError (Char.ofNat point) (.controlCharacter (Char.ofNat point)))) ∧
    templateNamedDiagnostic? ("a" ++ cp 0xE0001 ++ "b") = some (some "INVALID_CHARACTERS") ∧
    templateError? ("a" ++ cp 0x1F600 ++ "b") = some (.unsupportedCharacter (Char.ofNat 0x1F600)) := by
  native_decide

/- **A parameter's own body keeps the ASCII bound, and that is a different refusal from the repertoire
   one.** The Kernel reports a non-ASCII letter inside a parameter through its lexer, naming the character
   and its position, where the same letter in surrounding text is admitted — so the bound belongs to the
   name grammar rather than to the template. The position payload is not tracked here. -/
example :
    templateError? "row $Anchéor$" = some (.parameterCharacter "Anchéor" 'é') ∧
    templateError? ("row $No" ++ cp 0x20AC ++ "pe$") =
      some (.parameterCharacter ("No" ++ cp 0x20AC ++ "pe") (Char.ofNat 0x20AC)) ∧
    templateError? ("row $No" ++ cp 0x4E00 ++ "pe$") =
      some (.parameterCharacter ("No" ++ cp 0x4E00 ++ "pe") (Char.ofNat 0x4E00)) ∧
    templateError? "row $Amount$ é" = none := by
  native_decide

/- **The seven German letters the token grammar names sit on the near side of that bound**, which is
   what stops the ASCII test being read as the whole rule: an unknown name spelled with `ö` or `ß`
   reaches entity lookup and reports its own reference failure, where `é` never leaves the lexer. The
   pair is therefore a *reference* failure and not a lexical one — the discriminator the two classes
   have to keep apart, since only the lexical code says the text was never a name. -/
example :
    templateError? "row $Nöpe$" =
        some (.reference "Nöpe" (.invalidEntity (bare "Nöpe"))) ∧
      templateError? "row $Nopß$" =
        some (.reference "Nopß" (.invalidEntity (bare "Nopß"))) ∧
      templateError? "row $ÄÜÖäüöß$" =
        some (.reference "ÄÜÖäüöß" (.invalidEntity (bare "ÄÜÖäüöß"))) := by
  native_decide

/- **The two form-pointer terminals are the one field form that skips the condition-membership gate.**
   The Kernel admits `$Entity.Vordruckzeile$` and `$Entity.Vordruckname$` on a field the condition
   never references — measured on a Number field, a repeatable-group field, and the bare, relative and
   absolute spellings alike — where every other name-position form on an unreferenced field is refused.
   `Other` is unreferenced here, `Amount` is the condition's own operand, and the third row is the
   contrast that makes the exemption a fact about the suffix rather than about the model. -/
example :
    templateOk? "row $Other.Vordruckzeile$" = some true ∧
      templateOk? "row $Other.Vordruckname$" = some true ∧
      templateOk? "row $Amount.Vordruckzeile$" = some true ∧
      templateError? "row $Other$" = some (.fieldNotReferenced "Other" other.id) := by
  native_decide

/- Their only measured gate resolves the entity to a **field**: an undeclared name draws its own
   reference failure, and the bare terminal without an entity is an ordinary entity lookup rather than
   a terminal at all. Neither composes with a further suffix. -/
example :
    templateError? "row $Nope.Vordruckzeile$" =
        some (.reference "Nope.Vordruckzeile" (.invalidEntity (bare "Nope"))) ∧
      templateError? "row $Vordruckzeile$" =
        some (.reference "Vordruckzeile" (.invalidEntity (bare "Vordruckzeile"))) ∧
      templateError? "row $Amount.Vordruckzeile.value$" =
        some (.invalidParameter "Amount.Vordruckzeile.value") := by
  native_decide

/- The **semantic-index suffix** on a parameter. A keyed parameter names a semantic index over a
repeatable group, and this fragment's model is nonrepeatable, so every well-formed keyed parameter is
refused as outside the fragment rather than admitted or mapped to the Kernel's pairing class. What the
cases separate is the grammar *in front of* that boundary: which spellings are well formed and reach
it, and which are refused earlier and where. -/
example :
    templateError? "Bad $Amount For \"k1\"$" =
        some (.semanticIndexUnsupported "Amount For \"k1\"") := by
  native_decide

/- Keying **replaces the field-membership gate rather than removing a gate**. The unkeyed spelling of
a field the condition never mentions is refused `INVALID_FIELD`; the keyed spelling escapes that gate
and meets the index gate instead, whose admitted set is the condition's own keyed field together with
the group's declared index field and nothing further. So membership is a property of the unkeyed form
while the keyed form answers to a different, and also finite, set — an earlier reading of this
paragraph said keying admits any field, which a group declaring only those two fields cannot refute
([checkpoint](../../docs/SOURCES.md#src-keyed-parameter-admits-the-index-field-only)). The pair below
holds regardless: the same field reaches two different refusals depending only on whether it carries
a key, which is the distinction a fragment without repeatable groups can still hold. -/
example :
    templateError? "$Other For \"k1\"$" =
        some (.semanticIndexUnsupported "Other For \"k1\"") ∧
      templateError? "$Other$" =
        some (.fieldNotReferenced "Other" other.id) := by
  native_decide

/- The suffix sits **before** the key, which is the one ordering the grammar admits: measured, the
Kernel accepts `$X.value For "k"$` and refuses `$X For "k".value$` as a parse failure. Here the first
is well formed and reaches the fragment boundary while the second never becomes a parameter at all. -/
example :
    templateError? "$Amount.value For \"k1\"$" =
        some (.semanticIndexUnsupported "Amount.value For \"k1\"") ∧
      templateError? "$Amount For \"k1\".value$" =
        some (.invalidParameter "Amount For \"k1\".value") := by
  native_decide

/- A key is a quoted token or a path to the keying field, and nothing else: an **unquoted** bare word
is not a token that fails to parse but a field reference that fails to resolve, which is the
`INVALID_ENTITY` the Kernel reports for that same spelling. So a key's name is resolved even though
the keyed form requires no membership. A literal takes no key of its own, so one written after it
leaves the literal for the index gate rather than nesting. -/
example :
    templateError? "$Amount For \"k1\" For \"k2\"$" =
        some (.semanticIndexUnsupported "Amount For \"k1\" For \"k2\"") ∧
      templateError? "$Amount For k1$" =
        some (.reference "Amount For k1"
          (.invalidEntity (pathAt (.relative 0) [] "k1"))) := by
  native_decide

/- The keyed category form reaches the fragment's unsupported index gate before the category can be checked; the measured ordering is recorded in the category-gate checkpoint. -/
example :
    templateError? "$Status->Group For \"k1\"$" =
        some (.semanticIndexUnsupported "Status->Group For \"k1\"") ∧
      templateError? "$Status-> For \"k1\"$" =
        some (.semanticIndexUnsupported "Status-> For \"k1\"") := by
  native_decide

/- **The value suffix is the profile's word, not a literal in the parser.** Every sibling terminal was
already supplied by the caller and this one was matched as `.value`, so a German-language profile
would have been read with the English word — the Kernel's own terminal tables give `value` under an
English condition language and `Wert` under German, and each is a lexer refusal in the other's model
([checkpoint](../../docs/SOURCES.md#src-index-terminal-admitting-spelling)).

Each language sits on **both** sides here, which is what distinguishes a parametric parser from one
that happens to accept both words: under the English profile `.value` selects the value part while
`.Wert` is not recognized as the suffix at all, leaving a residue that is no legal entity spec and
drawing `invalidParameter` — and under a German profile the two swap. So the other language's word
fails as a *parse*, not at the unquoted-terminal gate. This locks *this fragment's* parametricity;
the spellings themselves are the caller's data, and no row here claims which word a given Kernel
model takes. -/
example :
    let germanProfile := { keywordProfile with valueSuffixTerminal := "Wert" }
    let parsedAs (profile : ValidationMessageKeywordProfile)
        (template : String) : Option Bool := do
      let condition ← conditionOn? ["Order"] (bare "Amount")
      pure (elaborateValidationMessageTemplate model profile condition
        template).toOption.isSome
    parsedAs keywordProfile "$Amount.value$" = some true ∧
      parsedAs keywordProfile "$Amount.Wert$" = some false ∧
      parsedAs germanProfile "$Amount.Wert$" = some true ∧
      parsedAs germanProfile "$Amount.value$" = some false := by
  native_decide

end A12Kernel.Conformance.ValidationMessageAuthoring
