import A12Kernel.Elaboration.ValidationMessageDiagnostic

/-! # Checked validation-message authoring conformance locks -/

namespace A12Kernel.Conformance.ValidationMessageAuthoring

open A12Kernel

private def amount : FlatFieldDecl :=
  { id := 0, groupPath := ["Order"], name := "Amount",
    policy := { kind := .number { scale := 0, signed := true } } }

private def other : FlatFieldDecl :=
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

/-- A field under a **second root group**. The Kernel admits a model with more than one root, which is
what makes the root shorthand's meaning measurable rather than a distinction without a difference. -/
private def branchLabel : FlatFieldDecl :=
  { id := 8, groupPath := ["Vendor", "Branch"], name := "Label",
    policy := { kind := .string } }

private def model : FlatModel :=
  { fields := [amount, other, headAmount, forField, indexField, status,
      deepField, asideField, branchLabel] }

private def bare (field : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field }

/-- The exact en_US parameter terminal set, read off the Kernel's own English terminal bundle, together
with the seven this producer historically accepts unquoted inside an entity name. Only `For`,
`RuleGroup`, and `BaseYear` therefore need the quote escape here. -/
private def keywordProfile : ValidationMessageKeywordProfile := {
  path := {
    reserved := [
      "For", "index", "RootGroup", "RuleGroup", "Usb", "Vordruckname",
      "Vordruckzeile", "BaseYear", "value", "Zeile"
    ]
  }
  unquotedTerminals := [
    "value", "RootGroup", "Zeile", "Usb", "index", "Vordruckzeile",
    "Vordruckname"
  ]
  baseYearTerminal := "BaseYear"
  forTerminal := "For"
  valueSuffixTerminal := "value"
  rootGroupTerminal := "RootGroup"
  ruleGroupTerminal := "RuleGroup"
  formLineTerminal := "Vordruckzeile"
  formNameTerminal := "Vordruckname"
  retiredGroupTerminals := ["Zeile", "Usb"]
}

private def condition? : Option (CheckedFlatCondition model) :=
  (elaborate model ["Order"] (.fieldFilled (bare "Amount"))).toOption

private def pathAt (base : PathBase) (groups : List String) (field : String) :
    SurfaceFieldPath :=
  { base, groups, field }

/-- A condition in `group` whose one operand is `reference`, so the membership gate is satisfied for
exactly that field however the message spells it. -/
private def conditionOn? (group : GroupPath) (reference : SurfaceFieldPath) :
    Option (CheckedFlatCondition model) :=
  (elaborate model group (.fieldFilled reference)).toOption

private def pathTemplateOk? (group : GroupPath) (reference : SurfaceFieldPath)
    (template : String) : Option Bool := do
  let condition ← conditionOn? group reference
  pure (elaborateValidationMessageTemplate model keywordProfile condition
    template).toOption.isSome

private def pathTemplateError? (group : GroupPath) (reference : SurfaceFieldPath)
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

/- Malformed specs are the Kernel's single parse class, not a family of shape classes: an absolute
path with no group, an empty segment, and a bare parent walk with no field. -/
example :
    pathTemplateError? ["Order"] (pathAt (.relative 0) ["Head"] "Amount")
        "See $/Amount$" = some (.invalidParameter "/Amount") ∧
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

private def render? (template : String) : Option ResolvedMessageText := do
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
    templateNamedDiagnostic? "row $#/'Order$" = some (some "MVK_LEXER_STANDARD_ERROR") := by
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
the keyed form requires no membership. A key that is itself keyed is refused as nesting. -/
example :
    templateError? "$Amount For \"k1\" For \"k2\"$" =
        some (.nestedSemanticIndex "Amount For \"k1\" For \"k2\"") ∧
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

/-- A rule in `/Order/Head`, whose group has one ancestor above it, one **declared** group below it,
and one declared sibling. Every group-position case below runs against this one rule. -/
private def headGroupOk? (template : String) : Option Bool :=
  pathTemplateOk? ["Order", "Head"] (bare "Amount") template

private def headGroupError? (template : String) :
    Option ValidationMessageTemplateError :=
  pathTemplateError? ["Order", "Head"] (bare "Amount") template

/- The **group position** `$#...$`. Measured at kernel 30.8.1, the rule's own group and its ancestors
are always available, which is the arm these rows exercise; a group the condition reads into is the
other arm, locked below. The two keyword shorthands name the endpoints of the ancestor chain and are
admitted here for that reason, not as separate admissions — but **`RuleGroup`
additionally carries a placement condition**, so that shared reason is not the whole rule: a rule
sitting directly in the root group may not write `$#RuleGroup$` at all, while `$#RootGroup$` and the
absolute spelling of that very group are both admitted from the same locus. The rows here are one
level down, where all four spellings are admitted; the root-locus rows below are where the shorthand
parts from the other two. Measured on the computation carrier first
([checkpoint](../../docs/SOURCES.md#src-rulegroup-shorthand-root-gate)) and then on this one
([checkpoint](../../docs/sources/message-and-pointer-probes.md#src-rulegroup-root-gate-on-the-rule-carrier)),
which is the crossing that closed it. -/
example :
    headGroupOk? "In $#/Order/Head$" = some true ∧
      headGroupOk? "In $#/Order$" = some true ∧
      headGroupOk? "In $#RuleGroup$" = some true ∧
      headGroupOk? "In $#RootGroup$" = some true := by
  native_decide

/- The refused half, and the separator that makes availability the operative gate rather than mere
existence: `/Order/Head/Deeper` and `/Order/Side` are groups this model really **declares**, and both
are refused exactly like the unknown `/Order/Nope`, because this condition reads nothing inside either.
The same two groups are admitted once the condition reads into them, below. -/
example :
    headGroupError? "In $#/Order/Head/Deeper$" =
        some (.invalidGroupParameter "#/Order/Head/Deeper") ∧
      headGroupError? "In $#/Order/Side$" =
        some (.invalidGroupParameter "#/Order/Side") ∧
      headGroupError? "In $#/Order/Nope$" =
        some (.invalidGroupParameter "#/Order/Nope") := by
  native_decide

/- A path without the leading separator is **relative to the rule's group**, so a bare word names a
group *below* it. `Head` is the rule's own group and `Order` its ancestor, both admitted when spelled
absolutely above, but spelled bare they name `/Order/Head/Head` and `/Order/Head/Order`, which do not
exist; a bare word is not looked up as the short name of a group elsewhere. A field name in this
position is refused like any other word
([checkpoint](../../docs/sources/message-and-pointer-probes.md#src-message-group-availability)). -/
example :
    headGroupError? "In $#Head$" = some (.invalidGroupParameter "#Head") ∧
      headGroupError? "In $#Order$" = some (.invalidGroupParameter "#Order") ∧
      headGroupError? "In $#Amount$" = some (.invalidGroupParameter "#Amount") := by
  native_decide

/- A group the condition **reads into** is available whatever its position relative to the rule: the
root-group rule reading `Head/Deeper/Deep` admits the descendant `Deeper`, and the intermediate `Head`
that holds no read field directly, in the relative and the absolute spelling alike. The same rule still
refuses the unread sibling, an unknown relative group, and a relative path naming the read field
itself; and a bare `Deeper`, which is available by path, is refused because nothing named so sits
directly below the rule's group
([checkpoint](../../docs/sources/message-and-pointer-probes.md#src-message-group-availability)). -/
example :
    let deep := pathAt (.relative 0) ["Head", "Deeper"] "Deep"
    pathTemplateOk? ["Order"] deep "In $#Head$" = some true ∧
      pathTemplateOk? ["Order"] deep "In $#Head/Deeper$" = some true ∧
      pathTemplateOk? ["Order"] deep "In $#/Order/Head/Deeper$" = some true ∧
      pathTemplateOk? ["Order"] deep "In $#'Head'$" = some true ∧
      pathTemplateError? ["Order"] deep "In $#Deeper$" =
        some (.invalidGroupParameter "#Deeper") ∧
      pathTemplateError? ["Order"] deep "In $#Side$" =
        some (.invalidGroupParameter "#Side") ∧
      pathTemplateError? ["Order"] deep "In $#Head/Nope$" =
        some (.invalidGroupParameter "#Head/Nope") ∧
      pathTemplateError? ["Order"] deep "In $#Head/Deeper/Deep$" =
        some (.invalidGroupParameter "#Head/Deeper/Deep") := by
  native_decide

/- A **read sibling** is available too, so availability is not containment in either direction. From
`/Order/Head` reading `/Order/Side/Aside`, the sibling is admitted by a parent walk, by an absolute
path, and by a walk whose turning point names the group it reaches; a turning point naming another
group is refused on the Kernel's entity class, not the group one. -/
example :
    let aside := pathAt .absolute ["Order", "Side"] "Aside"
    pathTemplateOk? ["Order", "Head"] aside "In $#../Side$" = some true ∧
      pathTemplateOk? ["Order", "Head"] aside "In $#/Order/Side$" = some true ∧
      pathTemplateOk? ["Order", "Head"] aside "In $#..Order/Side$" = some true ∧
      pathTemplateError? ["Order", "Head"] aside "In $#..Wrong/Side$" =
        some (.groupTurningPointMismatch "#..Wrong/Side") := by
  native_decide

/- A parent walk reaches the ancestor arm, and one that climbs past the root group is refused on the
message route's own above-root class. A bare `..` names the parent itself. -/
example :
    headGroupOk? "In $#..$" = some true ∧
      headGroupOk? "In $#../Head$" = some true ∧
      headGroupError? "In $#../Side$" = some (.invalidGroupParameter "#../Side") ∧
      headGroupError? "In $#Deeper$" = some (.invalidGroupParameter "#Deeper") ∧
      headGroupError? "In $#../../Order$" =
        some (.groupParameterAboveRoot "#../../Order") ∧
      pathTemplateError? ["Order"] (bare "Other") "In $#../Head$" =
        some (.groupParameterAboveRoot "#../Head") := by
  native_decide

/- A relative spelling meets the same lexical classes as an absolute one. -/
example :
    headGroupError? "In $#Deeper/$" =
        some (.groupParameterLexical "#Deeper/" .truncated) ∧
      headGroupError? "In $#Deeper//Deep$" =
        some (.groupParameterLexical "#Deeper//Deep" .separator) ∧
      headGroupError? "In $#'Deeper$" =
        some (.groupParameterLexical "#'Deeper" .lexer) := by
  native_decide

/- The argument is refused in **layers**, and a later layer never answers ahead of an earlier one
([checkpoint](../../docs/sources/message-and-pointer-probes.md#src-message-group-argument-layers)).
A character the parameter lexer forms no token for, or a malformed quoted name, is the lexer class
even before an unknown name; a separator with no name after it is a syntax class even before an
unknown name; then the path is looked up; and only a path that resolves meets the syntax class for a
token left after it. -/
example :
    let deep := pathTemplateError? ["Order"] (pathAt (.relative 0) ["Head", "Deeper"] "Deep")
    deep "In $#Head[1]$" = some (.groupParameterLexical "#Head[1]" .lexer) ∧
      deep "In $#Head*$" = some (.groupParameterLexical "#Head*" .lexer) ∧
      deep "In $#Head%$" = some (.groupParameterLexical "#Head%" .lexer) ∧
      deep "In $#'1Head'$" = some (.groupParameterLexical "#'1Head'" .lexer) ∧
      deep "In $#Nope[1]$" = some (.groupParameterLexical "#Nope[1]" .lexer) ∧
      deep "In $#/Order/Head[1]$" = some (.groupParameterLexical "#/Order/Head[1]" .lexer) ∧
      deep "In $#$" = some (.groupParameterLexical "#" .truncated) ∧
      deep "In $#Nope/$" = some (.groupParameterLexical "#Nope/" .truncated) ∧
      deep "In $#/Nope/$" = some (.groupParameterLexical "#/Nope/" .truncated) ∧
      deep "In $#Side/$" = some (.groupParameterLexical "#Side/" .truncated) ∧
      deep "In $#Nope//Deeper$" = some (.groupParameterLexical "#Nope//Deeper" .separator) ∧
      deep "In $#He-ad$" = some (.invalidGroupParameter "#He-ad") ∧
      deep "In $#/Order/He-ad$" = some (.invalidGroupParameter "#/Order/He-ad") ∧
      deep "In $#Head-x$" = some (.groupParameterLexical "#Head-x" .unexpected) ∧
      deep "In $#Head)$" = some (.groupParameterLexical "#Head)" .unexpected) ∧
      deep "In $#Head x$" = some (.groupParameterLexical "#Head x" .unexpected) ∧
      deep "In $#/Order/Head-x$" =
        some (.groupParameterLexical "#/Order/Head-x" .unexpected) ∧
      headGroupError? "In $#Head/..$" = some (.groupParameterLexical "#Head/.." .unexpected) ∧
      headGroupError? "In $#...$" = some (.groupParameterLexical "#..." .unexpected) := by
  native_decide

/- A bare word that names nothing directly below the rule's group is looked up as the **short name of
a field**, never of a group. `Amount` is declared twice, so from `/Order/Side` it is ambiguous and
refused on its own class; the unique field `Aside`, reached that way from the root group, is refused
as a field. A group whose name is unique is not found this way at all, which is what refuses a bare
`Deeper` from the root group above. -/
example :
    pathTemplateError? ["Order", "Side"] (bare "Aside") "In $#Amount$" =
        some (.groupShortNameNotUnique "#Amount" "Amount") ∧
      pathTemplateError? ["Order"] (bare "Other") "In $#Aside$" =
        some (.invalidGroupParameter "#Aside") := by
  native_decide

/- The descendant arm from a rule below the root, and a parent walk that reaches the root group
exactly, beside one step more. -/
example :
    pathTemplateOk? ["Order", "Head"] (pathAt (.relative 0) ["Deeper"] "Deep") "In $#Deeper$" =
        some true ∧
      pathTemplateOk? ["Order", "Head", "Deeper"] (bare "Deep") "In $#../..$" = some true ∧
      pathTemplateError? ["Order", "Head", "Deeper"] (bare "Deep") "In $#../../..$" =
        some (.groupParameterAboveRoot "#../../..") := by
  native_decide

/- Two historic terminals are **recognized** in this position and refused on their own class, which the
Kernel reports with a code distinct from an unknown group. Other words that look like terminals of
the same vintage are not terminals here at all: they draw the ordinary unknown-group refusal, and so
does an arbitrary name, so the retired class is exactly two members wide rather than a catch-all for
old syntax. The Kernel's `$#index(Rows)$` row, measured on a model with no field of that name, is not
locked here, because this fixture declares a field `index` that the bare word's short-name lookup
would find. -/
example :
    headGroupError? "In $#Zeile$" = some (.retiredGroupTerminal "#Zeile" "Zeile") ∧
      headGroupError? "In $#Usb$" = some (.retiredGroupTerminal "#Usb" "Usb") ∧
      headGroupError? "In $#Vordruckzeile$" =
        some (.invalidGroupParameter "#Vordruckzeile") ∧
      headGroupError? "In $#Vordruckname$" =
        some (.invalidGroupParameter "#Vordruckname") ∧
      headGroupError? "In $#NotATerminal$" =
        some (.invalidGroupParameter "#NotATerminal") := by
  native_decide

/- The position marker selects a **different grammar**, not a different form inside the name grammar:
the same word is an entity lookup without it and a group terminal with it. That is the pair the Kernel
separates by reporting an entity refusal for one spelling and admitting the other. -/
example :
    headGroupOk? "In $#RootGroup$" = some true ∧
      headGroupError? "In $RootGroup$" =
        some (.reference "RootGroup"
          (.invalidEntity (pathAt (.relative 0) [] "RootGroup"))) := by
  native_decide

/- At the root the chain has one member, so the three spellings would all denote that one group — and
the Kernel refuses exactly one of them. A rule sitting directly in the root group may not write the
`RuleGroup` shorthand, while `RootGroup` and the absolute spelling of that very group are admitted
from the identical locus
([checkpoint](../../docs/sources/message-and-pointer-probes.md#src-rulegroup-root-gate-on-the-rule-carrier)).
So the gate is on the word, not on the position: the group is nameable there twice over. The group
below — admitted as the *rule's own* group one row above — is still refused here, because this
condition reads nothing inside it. -/
example :
    pathTemplateError? ["Order"] (bare "Other") "In $#RuleGroup$" =
        some (.ruleGroupImmediatelyBelowRoot "#RuleGroup") ∧
      pathTemplateOk? ["Order"] (bare "Other") "In $#RootGroup$" = some true ∧
      pathTemplateOk? ["Order"] (bare "Other") "In $#/Order$" = some true ∧
      pathTemplateError? ["Order"] (bare "Other") "In $#/Order/Head$" =
        some (.invalidGroupParameter "#/Order/Head") := by
  native_decide

/- One level down the same shorthand is admitted, which is what makes the row above a placement gate
   rather than the shorthand being unsupported. -/
example :
    pathTemplateOk? ["Order", "Head"] (bare "Amount") "In $#RuleGroup$" =
      some true := by
  native_decide

/- The group argument takes the name grammar's **single-quote escape** at any segment, and the quotes
are erased before the group is looked up, so a quoted spelling reaches the same group as its bare one. -/
example :
    headGroupOk? "In $#/'Order'/'Head'$" = some true ∧
      headGroupOk? "In $#/'Order'/Head$" = some true ∧
      headGroupOk? "In $#/Order/'Head'$" = some true ∧
      headGroupOk? "In $#/'Order'$" = some true := by
  native_decide

/- Quoting is not merely erased, though: it **suppresses** the keyword reading. Each of these three
words is a terminal in this position unquoted — two admitted, one on the retired class — and quoting
all three turns them into ordinary group names, which are then refused because no group of that name
sits below the rule's group. That is the separator between "quotes are stripped first" and "quotes decide whether the
word is a terminal at all". -/
example :
    headGroupError? "In $#'RootGroup'$" =
        some (.invalidGroupParameter "#'RootGroup'") ∧
      headGroupError? "In $#'RuleGroup'$" =
        some (.invalidGroupParameter "#'RuleGroup'") ∧
      headGroupError? "In $#'Zeile'$" = some (.invalidGroupParameter "#'Zeile'") := by
  native_decide

/- An absolute path resolves in **two stages**, and the Kernel reports them apart. The first segment
must name a declared root group; when it does not, the refusal is the root one whatever follows it. A
declared root followed by an unknown or unavailable group is the ordinary group refusal instead, so
root existence and availability are separate gates rather than one. -/
example :
    headGroupError? "In $#/Nope$" = some (.unknownRootGroup "#/Nope" "Nope") ∧
      headGroupError? "In $#/Nope/Head$" =
        some (.unknownRootGroup "#/Nope/Head" "Nope") ∧
      headGroupError? "In $#/Order/Nope$" =
        some (.invalidGroupParameter "#/Order/Nope") := by
  native_decide

/- A malformed **spelling** is a parse failure rather than a group refusal, and the Kernel separates
three lexical classes among these shapes rather than reporting one. The class follows the malformed
shape, so it is decidable here; only the character position the lexer code additionally carries is not.
A trailing separator and a doubled one are the pair that shows the position of the empty segment
decides, since neither is distinguishable from the other by its characters alone. -/
example :
    headGroupError? "In $#/Order/$" =
        some (.groupParameterLexical "#/Order/" .truncated) ∧
      headGroupError? "In $#//Order$" =
        some (.groupParameterLexical "#//Order" .separator) ∧
      headGroupError? "In $#/'Order/Head$" =
        some (.groupParameterLexical "#/'Order/Head" .lexer) ∧
      headGroupError? "In $#/''$" =
        some (.groupParameterLexical "#/''" .lexer) := by
  native_decide

/- The root shorthand names the root of the **rule's own** ancestor chain, not a model-wide root. A
second root group separates the two readings: a rule under it admits the shorthand while the other
root, which neither contains the rule nor holds a read field, is refused. -/
example :
    pathTemplateOk? ["Vendor", "Branch"] (bare "Label") "In $#RootGroup$" =
        some true ∧
      pathTemplateOk? ["Vendor", "Branch"] (bare "Label") "In $#/Vendor$" =
        some true ∧
      pathTemplateError? ["Vendor", "Branch"] (bare "Label") "In $#/Order$" =
        some (.invalidGroupParameter "#/Order") := by
  native_decide

/- What an admitted **group** parameter renders, measured on the Kernel: the 1-based repetition index
   of the named group in the firing row, and `1` for a nonrepeatable group. A three-row document
   whose rule fires on rows 2 and 3 renders `2` and `3`, which separates the row's own index from a
   firing ordinal
   ([checkpoint](../../docs/sources/message-and-pointer-probes.md#src-message-group-parameter-rendered-index)).
   Only the nonrepeatable arm is reachable here, and deliberately so: an available group is an
   ancestor of the rule's row group or holds a field the condition reads, and this route's condition
   spine refuses a repeatable reference, so neither arm reaches a repeatable group. What these cases lock is that
   the bytes are the **Kernel's constant** rather than the caller's, which is what they used to be. -/

example : render? "[root=$#/Order$]" = some { text := "[root=1]" } := by
  native_decide

example : render? "[rtg=$#RootGroup$]" = some { text := "[rtg=1]" } := by
  native_decide

/-- The rule's own group is this model's root, so the shorthand never reaches rendering at all: the
    placement gate refuses it during authoring, and this row records that the render route is
    unreachable from this host rather than that it renders something. A rendered `RuleGroup` needs a
    rule one level down, which this fixture's nonrepeatable spine does not carry. -/
example : render? "[rg=$#RuleGroup$]" = none := by
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
