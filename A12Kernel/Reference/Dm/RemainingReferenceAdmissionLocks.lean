import A12Kernel.Reference.Dm.Validate

namespace A12Kernel.Dm.RemainingReferenceAdmissionLocks

private def model : FlatModel := {
  timeZoneId := "UTC"
  fields := [
    { id := 1, name := "Key", groupPath := ["Form"], policy := { kind := .string } },
    { id := 2, name := "Anchor", groupPath := ["Form"], policy := { kind := .number { scale := 0, signed := true } } },
    { id := 12, name := "Amount", groupPath := ["Form"], policy := { kind := .number { scale := 0, signed := true } } },
    { id := 3, name := "Code", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .string } },
    { id := 4, name := "N", groupPath := ["Form", "Rows", "Items"], repeatableScope := [10, 20], policy := { kind := .number { scale := 0, signed := true } } },
    { id := 5, name := "M", groupPath := ["Form", "Rows", "Items"], repeatableScope := [10, 20], policy := { kind := .number { scale := 0, signed := true } } },
    { id := 6, name := "Other", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .number { scale := 0, signed := true } } },
    { id := 7, name := "Text", groupPath := ["Form"], policy := { kind := .string } },
    { id := 8, name := "Value", groupPath := ["Form", "Rows", "Box"], repeatableScope := [10], policy := { kind := .number { scale := 0, signed := true } } },
    { id := 9, name := "Value", groupPath := ["Form", "Head"], policy := { kind := .number { scale := 0, signed := true } } },
    { id := 11, name := "Value", groupPath := ["Form", "Tail"], policy := { kind := .number { scale := 0, signed := true } } },
    { id := 10, name := "Due", groupPath := ["Form"], policy := { kind := .temporal .date .fullDate }, temporalTargetPolicy := some { format := "yyyy-MM-dd" } }]
  repeatableGroups := [
    { level := 10, path := ["Form", "Rows"], repeatability := some 3, indexField := some 3 },
    { level := 20, path := ["Form", "Rows", "Items"], repeatability := some 2 }] }

private def checked (condition errorPath : String) (group : GroupPath := ["Form"]) : Lowering (CheckedResolvedValidationRule model) :=
  let dm : DmModel := { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  checkRule dm .english {
    group, name := "References", errorCode := "REFERENCES", errorEntityRelPath := "../" ++ errorPath,
    condition, severity := "ERROR" }

private def references (condition errorPath : String) (field : FieldId) (level : RepeatableLevel)
    (group : GroupPath := ["Form"]) := do
  let rule ← (checked condition errorPath group).toOption
  pure (rule.condition.core.authoredErrorReference? field,
    rule.condition.core.formOnlyErrorReference? field, rule.condition.core.errorReferenceAt? field level)

private def selectedProduct := "SumOfProducts(Rows/Items*/N For Key,Rows/Items*/M For \"b\") > 0"
private def cases : List (String × String × FieldId × RepeatableLevel × Bool) := [
  ("FieldFilled(Text)", "Text", 7, 10, false),
  ("[Text] PatternMatched \"[0-9]+\"", "Text", 7, 10, false),
  ("Valid(Text,\"Code\")", "Text", 7, 10, false),
  ("Length(Text) > 0", "Text", 7, 10, false),
  ("DifferenceInDays(Due,Due) == 0", "Due", 10, 10, false),
  ("NumberOfFilledGroups(Head,Tail) > 0", "Head/Value", 9, 10, false),
  ("NumberOfFilledGroups(Rows/Items*) > 0", "Rows/Items/N", 4, 10, true),
  (selectedProduct, "Rows/Items/N", 4, 10, false)]

private def rowProduct := "SumOfProducts(/Form/Rows/Items*/N,/Form/Rows/Items*/M) > 0"

private def refusedAs (condition errorPath : String) (error : FlatRuleAssemblyError) : Bool :=
  match checked condition errorPath with
  | .ok _ => false
  | .error refusal => refusal.construct == "RuleAssembly" && refusal.detail == (repr error).pretty

private def scalarReferences (condition : String) (field : FieldId) (level : RepeatableLevel) := do
  let parsed ← (parseText .english condition).toOption
  let .compare operator left right := parsed.body | none
  let surface ← (lowerNumericComparison model ["Form"] operator left right false).toOption
  let comparison ← (elaborateNumericComparison model ["Form"] surface).toOption
  let checked ← (CheckedValidationCondition.fromNumeric comparison).toOption
  pure (checked.core.authoredErrorReference? field,
    checked.core.formOnlyErrorReference? field, checked.core.errorReferenceAt? field level)

private def arithmeticCases : List (String × String × FieldId) := [
  ("[Anchor] + 1 > 0", "Anchor", 2),
  ("Sum(Anchor,Amount) + [Anchor] > 0", "Anchor", 2),
  ("NumberOfFilledGroups(Head,Tail) + [Anchor] > 0", "Head/Value", 9)]

example : model.validate.isOk = true := by native_decide

example : cases.all (fun (condition, errorPath, field, level, binding) =>
    references condition errorPath field level == some (some true, some false, some binding)) = true := by native_decide
example : references rowProduct "Items/N" 4 10 ["Form", "Rows"] =
    some (some true, some false, some true) := by native_decide
example : references rowProduct "Items/N" 4 20 ["Form", "Rows"] =
    some (some true, some false, some false) ∧
    references "NumberOfFilledGroups(Rows/Items*) > 0" "Rows/Items/N" 4 20 =
      some (some true, some false, some false) := by native_decide

example : arithmeticCases.all (fun (condition, errorPath, field) =>
    references condition errorPath field 10 == some (some true, some false, some false) &&
    scalarReferences condition field 10 == some (some true, some false, some false)) := by native_decide

example : ["Length(Text) > 0", "DifferenceInDays(Due,Due) == 0"].all (fun condition =>
    let field := if condition.startsWith "Length" then 7 else 10
    scalarReferences condition field 10 == some (some true, some false, some false) &&
    scalarReferences condition 2 10 == some (some false, some false, some false)) := by native_decide

example : references "[Rows/Other] + 1 > 0" "Rows/Other" 6 10 =
    some (some true, some false, some true) ∧
    references "FieldFilled(Rows/Other)" "Rows/Other" 6 10 =
      some (some true, some false, some true) := by native_decide

example : cases.all (fun (condition, errorPath, _, level, _) =>
    references condition errorPath 2 level == some (some false, some false, some false)) := by native_decide

example : (cases.take 6).all (fun (condition, _, _, _, _) =>
    refusedAs condition "Anchor" (.errorFieldNotReferenced 2)) := by native_decide

example : references selectedProduct "Rows/Items/N" 1 10 =
    some (some true, some false, some false) ∧
    references selectedProduct "Rows/Items/N" 3 10 =
      some (some false, some false, some false) ∧
    refusedAs selectedProduct "Rows/Code" (.errorFieldNotReferenced 3) := by native_decide

example : (let condition := selectedProduct.replace "For Key" "For \"a\""
    references condition "Rows/Items/N" 4 10 == some (some true, some false, some false) &&
    references condition "Rows/Items/N" 1 10 == some (some false, some false, some false) &&
    refusedAs condition "Rows/Code" (.errorFieldNotReferenced 3)) := by native_decide

example : references rowProduct "Items/M" 5 10 ["Form", "Rows"] =
    some (some true, some false, some true) ∧
    references rowProduct "Items/M" 5 20 ["Form", "Rows"] =
      some (some true, some false, some false) := by native_decide

example : references selectedProduct "Rows/Items/M" 5 10 =
    some (some true, some false, some false) ∧
    (let rightKey := "SumOfProducts(Rows/Items*/N For \"a\",Rows/Items*/M For Key) > 0";
      references rightKey "Rows/Items/M" 5 10 == some (some true, some false, some false) &&
      references rightKey "Key" 1 10 == some (some true, some false, some false)) := by native_decide

example : (let mixedGroups := "NumberOfFilledGroups(Head,Rows*) > 0"
    references mixedGroups "Head/Value" 9 10 == some (some true, some false, some false) &&
    references mixedGroups "Rows/Code" 3 10 == some (some true, some false, some false)) := by native_decide

example : references "RepetitionNotUnique(Rows/Code)" "Rows/Code" 3 10 =
    some (some true, some false, some true) := by native_decide

private def rnuFrom := "RepetitionNotUnique(Rows/Code @From Rows)"
private def rnuNested := "RepetitionNotUnique(Rows/Items/N @From Rows)"

example : references "RepetitionNotUnique(Rows/Code)" "Rows/Code" 6 10 =
    some (some false, some false, some false) := by native_decide

example : refusedAs "RepetitionNotUnique(Rows/Code)" "Rows/Other" (.errorFieldNotReferenced 6) ∧
    references rnuFrom "Rows/Other" 6 10 = some (some true, some false, some true) ∧
    references rnuFrom "Rows/Other" 4 10 = some (some true, some false, some true) ∧
    references rnuFrom "Rows/Other" 4 20 = some (some true, some false, some false) ∧
    references rnuFrom "Rows/Other" 2 10 = some (some false, some false, some false) := by native_decide

example : references rnuNested "Rows/Items/N" 4 20 = some (some true, some false, some true) ∧
    refusedAs rnuNested "Rows/Items/M" (.errorFieldIterationInvalid 5 20) ∧
    refusedAs "RepetitionNotUnique(Rows/Items/N,Rows/Code @From Rows)" "Rows/Items/M"
      (.errorFieldIterationInvalid 5 20) ∧
    references "RepetitionNotUnique(Rows/Items/N,Rows/Items/M @From Rows)" "Rows/Items/M" 5 20 =
      some (some true, some false, some true) := by native_decide

example : [rnuNested ++ " And FieldFilled(Rows/Items/M)",
    "FieldFilled(Rows/Items/M) Or " ++ rnuNested].all (fun condition =>
      references condition "Rows/Items/M" 5 20 == some (some true, some false, some true)) := by native_decide

end A12Kernel.Dm.RemainingReferenceAdmissionLocks
