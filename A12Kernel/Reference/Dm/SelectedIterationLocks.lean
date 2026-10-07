import A12Kernel.Reference.Dm.LowerValidation
import A12Kernel.Reference.Dm.Parser

namespace A12Kernel.Dm.SelectedIterationLocks

private def model : FlatModel := {
  timeZoneId := "UTC"
  fields := [
    { id := 1, name := "Key", groupPath := ["Form", "Parents"], repeatableScope := [1], policy := { kind := .string } },
    { id := 2, name := "Anchor", groupPath := ["Form", "Parents"], repeatableScope := [1], policy := { kind := .number { scale := 0, signed := true } } },
    { id := 3, name := "Id", groupPath := ["Form", "Parents", "Rows"], repeatableScope := [1, 10], policy := { kind := .string } },
    { id := 4, name := "N", groupPath := ["Form", "Parents", "Rows"], repeatableScope := [1, 10], policy := { kind := .number { scale := 0, signed := true } } },
    { id := 5, name := "Text", groupPath := ["Form", "Parents", "Rows"], repeatableScope := [1, 10], policy := { kind := .string } },
    { id := 6, name := "Flag", groupPath := ["Form", "Parents", "Rows"], repeatableScope := [1, 10], policy := { kind := .boolean } },
    { id := 8, name := "A", groupPath := ["Form", "Parents", "Rows", "Body"], repeatableScope := [1, 10], policy := { kind := .number { scale := 0, signed := true } } },
    { id := 9, name := "B", groupPath := ["Form", "Parents", "Rows", "Body"], repeatableScope := [1, 10], policy := { kind := .number { scale := 0, signed := true } } },
    { id := 10, name := "N", groupPath := ["Form", "Parents", "Rows", "Items"], repeatableScope := [1, 10, 20], policy := { kind := .number { scale := 0, signed := true } } },
    { id := 11, name := "M", groupPath := ["Form", "Parents", "Rows", "Items"], repeatableScope := [1, 10, 20], policy := { kind := .number { scale := 0, signed := true } } },
    { id := 15, name := "LookupKey", groupPath := ["Form", "Parents", "Lookup"], repeatableScope := [1, 30], policy := { kind := .string } },
    { id := 16, name := "RootNumber", groupPath := ["Form"], policy := { kind := .number { scale := 0, signed := true } } },
    { id := 18, name := "ParentFlag", groupPath := ["Form", "Parents"], repeatableScope := [1], policy := { kind := .boolean } },
    { id := 19, name := "Stamp", groupPath := ["Form", "Parents", "Rows"], repeatableScope := [1, 10], policy := { kind := .temporal .date .fullDate }, temporalTargetPolicy := some { format := "yyyy-MM-dd" } },
    { id := 20, name := "ParentStamp", groupPath := ["Form", "Parents"], repeatableScope := [1], policy := { kind := .temporal .date .fullDate }, temporalTargetPolicy := some { format := "yyyy-MM-dd" } },
    { id := 21, name := "Consent", groupPath := ["Form", "Parents", "Rows"], repeatableScope := [1, 10], policy := { kind := .confirm } },
    { id := 22, name := "ParentConsent", groupPath := ["Form", "Parents"], repeatableScope := [1], policy := { kind := .confirm } },
    { id := 17, name := "Case", groupPath := ["Form", "Parents", "Lookup"], repeatableScope := [1, 30], policy := { kind := .number { scale := 0, signed := true } } }]
  repeatableGroups := [
    { level := 1, path := ["Form", "Parents"], repeatability := some 2 },
    { level := 10, path := ["Form", "Parents", "Rows"], repeatability := some 3, indexField := some 3 },
    { level := 20, path := ["Form", "Parents", "Rows", "Items"], repeatability := some 2 },
    { level := 30, path := ["Form", "Parents", "Lookup"], repeatability := some 2 }] }


private def condition (text : String) (group : GroupPath := ["Form", "Parents"]) :
    Option (CheckedValidationCondition model) := do
  let parsed ← (parseText .english text).toOption
  (lowerCondition model group false parsed.body).toOption

private def classifies (text : String) (expected : IterationGuardStatus)
    (allowed : Bool) (group : GroupPath := ["Form", "Parents"])
    (errorField : FieldId := 2) (level : RepeatableLevel := 1) : Bool :=
  match condition text group with
  | none => false
  | some checked => checked.core.iterationGuardStatusAt level == expected &&
      match assembleResolvedValidationRule model checked errorField "SELECTED_GUARD" .error { parts := [] } with
      | .ok _ => allowed
      | .error (.negativeConditionInIteration refused) => !allowed && refused == level
      | .error _ => false

private def guarded : List String := [
  "Sum(Rows/Body For Key) > 0",
  "Sum(Rows/Items*/N For Key) > 0",
  "MinValue(Rows/Body For Key) > 0",
  "MaxValue(Rows/Body For Key) > 0",
  "FirstFilledValue(Rows/Body For Key) > 0",
  "NumberOfValueInFields(1 In Rows/Body For Key) > 0",
  "NumberOfDifferentValues(Rows/Body For Key) > 0",
  "NumberOfValueInFields(\"x\" In Rows/Text For Key,Key) > 0",
  "NumberOfValueInFields(True In Rows/Flag For Key,Rows/Flag For \"b\") > 0",
  "SumOfProducts(Rows/Items*/N For Key,Rows/Items*/M For \"b\") > 0",
  "Sum(Rows/Body For \"a\") > 0",
  "Sum(Anchor,Rows/N For Key) > 0"]

private def unguarded : List String := [
  "Sum(Rows/Body For Key) == 0",
  "NumberOfValueInFields(1 In Rows/Body For Key) < 1",
  "Sum(/Form/RootNumber,Rows/N For Key) > 0"]

example : (guarded ++ unguarded).all (fun text => (condition text).isSome) = true := by native_decide

example : guarded.all (fun text =>
    classifies ("FieldFilled(Anchor) Or " ++ text) .guarded true &&
    classifies (text ++ " Or FieldFilled(Anchor)") .guarded true) = true := by native_decide

example : unguarded.all (fun text =>
    classifies ("FieldFilled(Anchor) Or " ++ text) .unguarded false &&
    classifies ("FieldFilled(Anchor) And " ++ text) .guarded true) = true := by native_decide

private def nested (text : String) (expected : IterationGuardStatus) (allowed : Bool) : Bool :=
  classifies ("FieldFilled(Case) Or " ++ text) expected allowed ["Form", "Parents", "Lookup"] 17 30

example : nested "Sum(/Form/Parents/Rows/Body For LookupKey) > 0" .guarded true ∧
    nested "Sum(/Form/Parents/Rows/N For LookupKey,/Form/Parents/Rows/N For \"b\") > 0" .unguarded false ∧
    nested "SumOfProducts(/Form/Parents/Rows/Items*/N For LookupKey,/Form/Parents/Rows/Items*/M For \"b\") > 0" .guarded true ∧
    classifies "FieldFilled(/Form/Parents/Anchor) And (FieldFilled(Case) Or SumOfProducts(/Form/Parents/Rows/Items*/N For LookupKey,/Form/Parents/Rows/Items*/M For \"b\") == 0)"
      .guarded true ["Form", "Parents", "Lookup"] 17 30 ∧
    classifies "FieldFilled(Case) Or SumOfProducts(/Form/Parents/Rows/Items*/N For LookupKey,/Form/Parents/Rows/Items*/M For \"b\") == 0"
      .unguarded false ["Form", "Parents", "Lookup"] 17 1 := by native_decide

/-- Isolate guard classification through the checked-source assembly boundary from reader operand admission; the companion reader matrix below checks that boundary separately. -/
private def booleanCompanion (expected : Bool) : Option Bool := do
  let group := ["Form", "Parents"]
  let parsed ← (parseText .english ("NumberOfValueInFields(" ++ (if expected then "True" else "False") ++ " In ParentFlag,Rows/Flag For Key)")).toOption
  let .call _ _ (some listed) none := parsed.body | none
  let surface ← (lowerEntitySource model group listed).toOption
  let source ← (elaborateBooleanValueCountSource model group expected surface (some group)).toOption
  let zero ← decodeNumber? "0"
  let guard ← condition "FieldFilled(Anchor)"
  let core : ValidationCondition model := .or guard.core (.leaf (.orderedNumeric .sameGroupAddressed {
    op := .ordinary .greater, left := .atom (.booleanValueCount source), right := .literal zero }))
  let checked ← (CheckedValidationCondition.checkCore model group core source.modelWellFormed).toOption
  pure (checked.core.iterationGuardStatusAt 1 == .guarded &&
    (assembleResolvedValidationRule model checked 2 "BOOLEAN_GUARD" .error { parts := [] }).isOk)

example : booleanCompanion true = some true ∧ booleanCompanion false = some true := by native_decide

private def parentBindingCases : List (String × String × String) := [
  ("FieldValuesNotUnique(", "Anchor", "Rows/N"),
  ("FieldValuesNotUnique(", "Key", "Rows/Text"),
  ("FieldValuesNotUnique(", "ParentStamp", "Rows/Stamp"),
  ("NumberOfValueInFields(True In ", "ParentFlag", "Rows/Flag"),
  ("NumberOfValueInFields(False In ", "ParentFlag", "Rows/Flag"),
  ("NumberOfValueInFields(True In ", "ParentConsent", "Rows/Consent")]

private def parentBindingText (opening parent child : String) (key : String)
    (reverse : Bool) : String :=
  let selected := child ++ " For " ++ key
  opening ++ (if reverse then selected ++ "," ++ parent else parent ++ "," ++ selected) ++
    (if opening.startsWith "Number" then ") > 0" else ")")

example : parentBindingCases.all (fun (opening, parent, child) =>
    ["Key", "\"a\""].all (fun key => [false, true].all (fun reverse =>
      classifies ("FieldFilled(Anchor) And " ++ parentBindingText opening parent child key reverse)
        .guarded true))) = true := by native_decide

private def staticDiagnostic (text : String) :
    Option KernelStaticDiagnostic := do
  let group := ["Form", "Parents"]
  let parsed ← (parseText .english text).toOption
  let .call _ arguments listed none := parsed.body | none
  let source ← (lowerEntitySource model group (listed.getD arguments)).toOption
  match elaborateNumberValuesNotUniqueSource model group source (bindingGroup? := some group) with
  | .error error => error.diagnostic?
  | .ok _ => none

private def booleanError (text : String) (expected : Bool) : Option BooleanValueCountElabError := do
  let group := ["Form", "Parents"]
  let parsed ← (parseText .english text).toOption
  let .call _ _ (some listed) none := parsed.body | none
  let source ← (lowerEntitySource model group listed).toOption
  match elaborateBooleanValueCountSource model group expected source (bindingGroup? := some group) with
  | .error error => some error
  | .ok _ => none

example : staticDiagnostic "FieldValuesNotUnique(Anchor)" = some .paramSizeInvalidN ∧
    staticDiagnostic "FieldValuesNotUnique(ParentFlag,Rows/Flag For Key)" = some .onlyStringEnumNumberDateAllowed ∧
    booleanError "NumberOfValueInFields(False In ParentConsent,Rows/Consent For Key)" false =
      some (.fieldKindMismatch ["Form", "Parents", "ParentConsent"] false .confirm) := by native_decide

example : parentBindingCases.all (fun (opening, parent, child) =>
    !(condition ("FieldFilled(Anchor) And " ++ opening ++ parent ++ "," ++ child ++
      (if opening.startsWith "Number" then ") > 0" else ")"))).isSome) = true ∧
    classifies "FieldFilled(Anchor) And FieldValuesNotUnique(Anchor,/Form/RootNumber)" .guarded true ∧
    !(condition "FieldFilled(Anchor) And FieldValuesNotUnique(Anchor,Lookup/Case)").isSome ∧
    !(condition "FieldFilled(Anchor) And FieldValuesNotUnique(Anchor,Rows/Items/N)").isSome := by native_decide

private def unboundAt (field : String) (level : RepeatableLevel) : Bool :=
  let group := ["Form", "Parents"]
  match parseText .english ("FieldValuesNotUnique(Anchor," ++ field ++ ")") with
  | .ok parsed => match parsed.body with
    | .call _ arguments none none => match lowerEntitySource model group arguments with
      | .ok surface => match elaborateNumberValuesNotUniqueSource model group surface
          (bindingGroup? := some group) with
        | .error (.shape (.resolve (.unboundOperandLevel _ found))) => found.level == level
        | _ => false
      | _ => false
    | _ => false
  | _ => false

example : unboundAt "Rows/N" 10 = true ∧ unboundAt "Lookup/Case" 30 = true ∧
    unboundAt "Rows/Items/N" 10 = true := by native_decide

end A12Kernel.Dm.SelectedIterationLocks
