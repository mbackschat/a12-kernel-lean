import A12Kernel.Reference.Dm.HavingFixture

namespace A12Kernel.Dm.EntityCategoryLocks
open A12Kernel

private def domain : EnumerationDeclaration := {
  storedTokens := ["keep", "drop"], categories := [{ name := "Label", tokens := ["K", "D"] }] }

private def model (tokenTarget : Bool := false) : FlatModel := { HavingFixture.model with
  fields := (HavingFixture.model.fields.map fun field =>
    if field.id == 2 || field.id == 3 then
      { field with policy := { kind := .enumeration }, enumeration := some domain }
    else if field.id == 5 && tokenTarget then
      { field with policy := { kind := .enumeration }, enumeration := some { storedTokens := ["K", "D"] } }
    else field) ++ [{ id := 6, name := "Other", groupPath := ["Form"], policy := { kind := .enumeration }, enumeration := some domain }] }

private def run (operation expected : String) (tokenTarget : Bool := false) :=
  HavingFixture.runModel (model tokenTarget) "" false "keep" "keep" "drop"
    (extra := [("Other", .str "drop")]) (operationOverride := some operation)
    (ruleExpected := if tokenTarget then "\"" ++ expected ++ "\"" else expected)

private def agrees (operation expected : String) (tokenTarget : Bool := false) : Bool :=
  (run operation expected tokenTarget).any fun (verdict, outputs) =>
    (match verdict with | .fired _ => true | _ => false) && outputs == ["value " ++ expected]

example : (model false).validate.isOk && (model true).validate.isOk = true := by native_decide

example : agrees "NumberOfFilledFields(Rows*)" "6" &&
    agrees "NumberOfFilledFields(Expected, Other)" "2" &&
    agrees "NumberOfFilledFields(Rows*/N)" "3" &&
    agrees "NumberOfValueInFields(\"keep\" In Rows*/Tag)" "2" = true := by native_decide

example : ["NumberOfFilledFields(Rows* -> Label)",
    "NumberOfFilledFields(Rows -> Label)",
    "NumberOfValueInFields(\"K\" In Rows* -> Label)"].all (fun operation =>
      let result := HavingFixture.readerResults operation (model false) false
      result.1 != "admitted" && result.2 != "admitted") = true := by native_decide

private def refusedAs (operation code rawClass : String) : Bool :=
  let result := HavingFixture.readerResults operation (model false) false
  [result.1, result.2].all fun detail =>
    detail == code || decide ((detail.splitOn rawClass).length > 1)

example : ["NumberOfFilledFields(Expected->Label, Other->Label)",
    "NumberOfFilledFields(Rows*/Tag->Label)",
    "NumberOfFilledFields(Rows*/Tag->Label Having [Rows/N] < 5)"].all (fun operation =>
      refusedAs operation "MVK_CATEGORY_NOT_ALLOWED" "FieldEntityShapeElabError.categoryNotAllowed") = true := by native_decide

example : ["NumberOfFilledFields(Rows*/Tag->Missing)",
    "NumberOfFilledFields(Rows*/Tag->Missing Having [Rows/N] < 5)"].all (fun operation =>
      refusedAs operation "MVK_CATEGORY_UNKOWN" "FieldEntityShapeElabError.unknownCategory") &&
    ["NumberOfFilledFields(Rows*/N->Label)",
    "NumberOfFilledFields(Rows*/N->Label Having [Rows/N] < 5)"].all (fun operation =>
      refusedAs operation "MVK_NO_ENUMERATION" "ResolveError.categoryReadOfNonEnumeration") = true := by native_decide

example : agrees "NumberOfValueInFields(\"K\" In Expected->Label, Other->Label)" "1" &&
    agrees "NumberOfValueInFields(\"K\" In Rows*/Tag->Label)" "2" &&
    agrees "NumberOfValueInFields(\"K\" In Rows*/Tag->Label Having [Rows/N] < 5)" "1" = true := by native_decide

example : agrees "FirstFilledValue(Expected->Label, Other->Label)" "K" true &&
    agrees "FirstFilledValue(Rows*/Tag->Label)" "K" true &&
    agrees "FirstFilledValue(Rows*/Tag->Label Having [Rows/N] == 5)" "D" true = true := by native_decide

private def ordinaryModel : FlatModel := { (model false) with
  fields := (model false).fields ++ [
    { id := 7, name := "Choice", groupPath := ["Form", "Pool"], policy := { kind := .enumeration }, enumeration := some domain },
    { id := 8, name := "Digits", groupPath := ["Form"], policy := { kind := .enumeration },
      enumeration := some { storedTokens := ["1", "2"] } }] }

private def ordinaryDiagnostic (condition : String) : Option String :=
  match checkRule { flat := ordinaryModel, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
      .english {
        group := ["Form"], name := "Entity", errorCode := "ENTITY", errorEntityRelPath := "../Error",
        condition := "FieldFilled(Error) And " ++ condition, severity := "ERROR" } with
  | .ok _ => none
  | .error error => some error.detail

example : ordinaryModel.validate.isOk = true := by native_decide

example : ["Length(Error) > 0", "FieldValueAsNumber(Digits) > 0",
    "FirstFilledValue(Pool, Pool/Choice->Label) == \"keep\""].all (fun condition =>
      ordinaryDiagnostic condition == none) = true := by native_decide

-- The parameter-read grid and entity-list root/category oracle separate the authored slot
-- from expanded declaration overlap (spec/07 §5; src-field-value-read-predictions).
private def refusalRows := [
    ("Length(/Form) > 0", KernelStaticDiagnostic.noGroupsAllowed),
    ("FieldValueAsNumber(Pool) > 0", .noGroupsAllowed),
    ("FirstFilledValue(Pool, Pool/Choice) == \"keep\"", .duplicateParam2),
    ("FirstFilledValue(Pool, Pool) == \"keep\"", .duplicateParam1),
    ("FirstFilledValue(/Form, Pool/Choice->Label) == \"keep\"", .rootGroupReferenced),
    ("FirstFilledValue(Pool, Pool/Choice->Missing) == \"keep\"", .categoryUnknown)
  ]

example : refusalRows.all (fun (condition, expected) => ordinaryDiagnostic condition == some expected.kernelCode) = true := by native_decide

end A12Kernel.Dm.EntityCategoryLocks
