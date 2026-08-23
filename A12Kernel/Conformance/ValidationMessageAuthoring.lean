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

private def model : FlatModel :=
  { fields := [amount, other, headAmount] }

private def bare (field : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field }

private def keywordProfile : PathKeywordProfile :=
  { reserved := ["For", "value"] }

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

/- A reserved word is refused at **any** path level, not only as the final name, and the refusal names
the colliding segment rather than the whole spec. -/
example :
    pathTemplateError? ["Order"] (pathAt (.relative 0) ["Head"] "Amount")
        "See $For/Amount$" = some (.unsupportedQuotedName "For") := by
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

private def render? (template : String) : Option ResolvedMessageText := do
  let condition ← condition?
  let checked ←
    (elaborateValidationMessageTemplate model keywordProfile condition template).toOption
  pure (checked.toRenderPlan inputs).render

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
        some (.unsupportedQuotedName "For") := by
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
