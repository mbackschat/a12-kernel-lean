import A12Kernel.Elaboration.ValidationMessageAuthoring

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

private def model : FlatModel :=
  { fields := [amount, other, headAmount, forField, indexField, status] }

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

/- The category suffix's three gates, in the Kernel's own order: a missing name is a parse failure, a
non-Enumeration field is refused before any category is looked up, and an undeclared name arrives
through the one existing Enumeration projection gate carrying its own class. -/
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
**doubled** arrow is where this fragment is narrower than the Kernel: it lands in the same parse class
here, while the Kernel reaches its category gate first and reports the first name as unknown. Both
refuse, and this local class projects to no Kernel diagnostic, so the narrowing publishes no claim. -/
example :
    pathTemplateError? ["Order"] (pathAt (.relative 0) [] "Status")
        "See $Status.value->Group$" =
      some (.invalidParameter "Status.value->Group") ∧
    pathTemplateError? ["Order"] (pathAt (.relative 0) [] "Status")
        "See $Status->A->B$" = some (.invalidParameter "Status->A->B") := by
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

private def templateError? (template : String) :
    Option ValidationMessageTemplateError := do
  let condition ← condition?
  match elaborateValidationMessageTemplate model keywordProfile condition template with
  | .ok _ => none
  | .error error => some error

private def stringPatternInputs : StringPatternMessageInputs where
  fieldName := "Code"
  fieldValue := "$field$"

private def stringPatternRender? (template : String) : Option ResolvedMessageText := do
  let checked ←
    (elaborateEnUsStringPatternMessageTemplate template).toOption
  pure (checked.renderError stringPatternInputs).text

private def stringPatternTemplateError? (template : String) :
    Option ValidationMessageTemplateError :=
  match elaborateEnUsStringPatternMessageTemplate template with
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
      templateError? "Prüfe $" =
        some (.unsupportedCharacter 'ü') ∧
      templateError? "$Other$" =
        some (.fieldNotReferenced "Other" other.id) ∧
      templateError? "$Missing$" =
        some (.reference "Missing" (.invalidEntity (bare "Missing"))) ∧
      templateError? "$Amount.nope$" =
        some (.invalidParameter "Amount.nope") ∧
      templateError? "$For$" =
        some (.unquotedTerminalName "For") := by
  native_decide

example :
    stringPatternRender? "$field$" =
        some { text := "Code" } ∧
      stringPatternRender? "Value [$field.value$]" =
        some { text := "Value [$field$]" } := by
  native_decide

example :
    stringPatternTemplateError? "$Field$" =
        some (.invalidParameter "Field") ∧
      stringPatternTemplateError? "$Code$" =
        some (.invalidParameter "Code") ∧
      stringPatternTemplateError? "Cost $$ $field$" =
        some (.invalidParameter "") ∧
      stringPatternTemplateError? "$field" =
        some .oddDollarCount := by
  native_decide

end A12Kernel.Conformance.ValidationMessageAuthoring
